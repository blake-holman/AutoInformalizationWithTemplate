"""Offline integration checks; no model or API credentials are used."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "ExportInfos"
sys.path.insert(0, str(ROOT / "Informalization/Informalization_py"))
from Infrastructure.InfoLoader import TacticInfoLoader, PremiseInfoLoader
from Infrastructure.AbstractSyntaxTreeLoader import AbstractSyntaxTreeLoader
from ApplicationService.TacticInfoSeparator import TacticInfoSeparator
from DomainService.AbstractSyntaxTreeSearcher import AbstractSyntaxTreeSearcher
from ApplicationService.TreeStructureReconstructor import TacticDependencyTreeHandler


class ExtractionTests(unittest.TestCase):
    def extract(self, file, output):
        return subprocess.run(
            [sys.executable, str(ROOT / "scripts/extract_project.py"),
             "--project", str(PROJECT), "--output", str(output), str(file)],
            capture_output=True, text=True,
        )

    def test_round_trip(self):
        with tempfile.TemporaryDirectory() as tmp:
            result = self.extract(Path("Tests/ExtractionSmoke.lean"), tmp)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            folder = Path(tmp) / "Tests/ExtractionSmoke.lean"
            tactics = TacticInfoLoader().load(folder / "tacticInfo.json")
            premises = PremiseInfoLoader().load(folder / "premiseInfo.json")
            ast = AbstractSyntaxTreeLoader().load(folder / "abstractSyntaxTreeInfo.json")
            self.assertTrue(tactics)
            self.assertTrue(premises)
            self.assertTrue(all(Path(p.definitionPath).is_file() for p in premises))
            searcher = AbstractSyntaxTreeSearcher()
            tactics = [t for t in tactics if searcher.is_proof_tactic_info(t, ast)]
            groups = TacticInfoSeparator().separate_tactic_infos(ast, tactics)
            self.assertEqual([searcher.get_theorem_name(g[0], ast) for g in groups],
                             ["double_add", "two_cases"])
            for group in groups:
                indents = searcher.search_tactic_indents(group, ast)
                tree = TacticDependencyTreeHandler().construct_tactic_info_tree(group, indents)
                self.assertTrue(tree.nodes)
            self.assertTrue(any(t.goalsAfter == "no goals" for t in tactics))
            self.assertTrue(any(t.tacticCommand == "rw_element" for t in tactics))

    def test_invalid_proof_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="Invalid",
                                             dir=PROJECT / "Tests", delete=False) as file:
                file.write("import Mathlib.Tactic\nexample : False := by exact True.intro\n")
                source = Path(file.name)
            try:
                result = self.extract(source.relative_to(PROJECT), tmp)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(list(Path(tmp).rglob("tacticInfo.json")))
            finally:
                source.unlink()


if __name__ == "__main__":
    unittest.main()
