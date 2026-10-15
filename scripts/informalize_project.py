#!/usr/bin/env python3
"""Run the template and recursive-summary pipeline on existing project exports."""
import argparse
import asyncio
import copy
from dataclasses import asdict, replace
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import traceback

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Informalization/Informalization_py"))


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


async def main(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    random.seed(0)
    import Infrastructure.OpenAIAPICommunicator as api_module
    original = api_module.OpenAIAPICommunicator
    semaphore = asyncio.Semaphore(3)
    calls = []
    attempts = 0
    configuration = original().request_identity
    metadata_path = output / "backend.json"
    if metadata_path.exists():
        if json.loads(metadata_path.read_text()) != configuration:
            raise RuntimeError("Output directory belongs to another model or backend; use a new directory")
    elif any(output.iterdir()):
        raise RuntimeError("Existing output has no backend identity; use a new output directory")
    save(metadata_path, configuration)

    class RecordedCommunicator(original):
        async def get_response(self, messages, temperature=1.0):
            nonlocal attempts
            messages = list(messages)
            request = {**self.request_identity, "requested_temperature": temperature, "messages": messages}
            key = hashlib.sha256(json.dumps(request, ensure_ascii=False, sort_keys=True).encode()).hexdigest()
            path = output / "requests" / (key + ".json")
            if path.exists():
                from openai.types.chat import ChatCompletionMessage
                return ChatCompletionMessage.model_validate(json.loads(path.read_text())["message"])
            async with semaphore:
                if attempts >= 300:
                    raise RuntimeError("Run stopped at the 300-request limit")
                attempts += 1
                message = await super().get_response(messages, temperature)
                record = {"request": request, "message": message.model_dump(),
                          "response_model": self.model, **self.last_response_metadata}
                save(path, record)
                calls.append({"cache": path.name, "model": self.model, "usage": record["usage"],
                              "backend": self.backend, "authentication": "chatgpt"})
                save(output / "calls.json", calls)
                print(f"MODEL_CALL {len(calls)}", flush=True)
                return message

    api_module.OpenAIAPICommunicator = RecordedCommunicator
    from Infrastructure.InfoLoader import TacticInfoLoader, PremiseInfoLoader
    from Infrastructure.AbstractSyntaxTreeLoader import AbstractSyntaxTreeLoader
    from Infrastructure.PremiseLibrary import PremiseLibrary
    from Infrastructure.PremiseExtractor import PremiseExtractor
    from ApplicationService.PremiseDiscriptor import PremiseDescriptor
    from ApplicationService.InformalizationService import InformalizationService
    from DomainService.DomainExtractor import DomainExtractor
    from DomainService.PromptFactories import TacticInformalizationPromptFactory

    library = PremiseLibrary()
    library.__library_data_path__ = str(output / "Library")
    (output / "Library").mkdir(exist_ok=True)
    service = InformalizationService()
    groups = []
    all_premises = []
    for relative in args.files:
        source = (args.project / relative).resolve()
        folder = (args.exports / relative).resolve()
        tactics = TacticInfoLoader().load(folder / "tacticInfo.json")
        premises = PremiseInfoLoader().load(folder / "premiseInfo.json")
        ast = AbstractSyntaxTreeLoader().load(folder / "abstractSyntaxTreeInfo.json")
        service.__preprocess_tactic_info__(tactics, ast)
        all_premises.extend(premises)
        for group in service.__tactic_info_separator__.separate_tactic_infos(ast, tactics):
            name = service.__ast_seacher__.get_theorem_name(group[0], ast)
            if args.theorem and name not in args.theorem:
                continue
            groups.append((name, source, group, premises, ast))
    if not groups:
        raise RuntimeError("No requested theorem found in the exports")

    # Build the domain-specific premise library from the actual source definitions.
    # Upstream ships a Mathlib library; an external project needs its own entries.
    unique = {}
    for premise in all_premises:
        source_path = Path(premise.definitionPath).resolve()
        project = args.project.resolve()
        local = source_path.is_relative_to(project) and ".lake" not in source_path.relative_to(project).parts
        selected_namespace = any(premise.fullName.startswith(ns + ".") for ns in args.context_namespace)
        if (local or selected_namespace) and premise.kind in ("definition", "theorem"):
            unique.setdefault(premise.fullName, premise)
    descriptor = PremiseDescriptor(PremiseExtractor())
    seeds = []
    for premise in sorted(unique.values(), key=lambda p: p.kind != "definition"):
        enriched = copy.deepcopy(premise)
        if premise.kind == "definition" and premise.definitionStartPos:
            lines = Path(premise.definitionPath).read_text().splitlines()
            block = []
            for line in lines[premise.definitionStartPos.line - 1:]:
                if not line.strip() and block:
                    break
                block.append(line)
            enriched = replace(enriched, declaration=(premise.declaration or "") + "\n\nFull definition from source:\n" + "\n".join(block))
        description = await descriptor.proc_description(enriched, all_premises, Path(premise.definitionPath))
        seeds.append({"name": premise.fullName, "input": enriched.declaration, "description": description})
    save(output / "premise-descriptions.json", seeds)
    print(f"PREMISES_COMPLETE {len(seeds)}", flush=True)

    async def run_group(item):
        name, source, group, premises, ast = item
        destination = output / "theorems" / name
        if (destination / "summary.txt").exists():
            return name, (destination / "summary.txt").read_text()
        worker = InformalizationService()
        indents = worker.__ast_seacher__.search_tactic_indents(group, ast)
        tree = worker.__dependency_tree_handler__.construct_tactic_info_tree(group, indents)
        data = await worker.__tactic_informalizer__.informalize(
            DomainExtractor().extract_domain_roots(source), group, premises, tree, source)
        applied, answers, evals, given, details = data
        worker.__dependency_tree_handler__.remove_specific_tactic_node_children(tree.nodes, "rw")
        worker.__dependency_tree_handler__.parse_informalized(tree.nodes, answers.copy())
        statement = await worker.__get_statement__(source, name, premises)
        summary, progress = await worker.__informalization_summerizer__.summerize_answers(statement, premises, tree)
        save(destination / "details.json", {"statement": statement, "applied_tactics": applied,
             "step_explanations": answers, "rewrite_scores": evals, "premises": given,
             "evaluation_data": details, "recursive_summaries": [asdict(p) for p in progress]})
        (destination / "summary.txt").write_text(summary)
        print(f"THEOREM_COMPLETE {name}", flush=True)
        return name, summary

    results = await asyncio.gather(*(run_group(item) for item in groups))
    library.write_to_file()
    (output / "all-proofs.txt").write_text("\n\n".join(name + "\n\n" + text for name, text in results))
    if args.combine:
        target = next(item for item in groups if item[0] == args.combine)
        statement = await service.__get_statement__(target[1], target[0], target[3])
        # One additional application of the upstream summary prompt combines helper proofs.
        context = ["Definitions: " + "\n".join(p["description"] for p in seeds if p["description"])]
        context.extend(text for _, text in results)
        combined = await RecordedCommunicator().get_response(
            TacticInformalizationPromptFactory().make_summerize_prompts(statement, context), 1.0)
        (output / "combined-proof.txt").write_text(combined.content)
    save(output / "result.json", {"status": "complete", "theorems": [name for name, _ in results],
         "fork_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
         "new_model_calls": len(calls), **configuration, "combined": args.combine})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--exports", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--theorem", action="append")
    parser.add_argument("--context-namespace", action="append", default=[], help="Additional imported namespace to describe")
    parser.add_argument("--combine", help="Target theorem for one summary across generated helper proofs")
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    try:
        asyncio.run(main(args))
    except Exception as error:
        save(args.output / "result.json", {"status": "failed", "type": type(error).__name__, "error": str(error)})
        traceback.print_exc()
        raise SystemExit(1)
