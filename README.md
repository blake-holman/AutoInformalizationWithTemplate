# Natural Language Translation of Formal Proofs through Informalization of Proof Steps and Recursive Summarization along Proof Structure

## Lean 4.34 fork

This fork ports the extractor to `leanprover/lean4:v4.34.0-rc2` and pins Mathlib to
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The existing tactic templates and summary
prompts are unchanged. Seven additional templates cover `omega`, `rintro`,
`unfold`, `dsimp`, `subst`, `ext`, and `constructor`.

Install the Python dependencies and build the extractor:

```bash
source make_env.sh
cd ExportInfos
lake exe cache get
lake build
cd ..
```

The build produces Lean modules; extraction runs through `lean --run` and does not
require native compilation of all of Mathlib.

Extract a file from another already-built project using the same toolchain:

```bash
python scripts/extract_project.py \
  --project /path/to/project \
  --output /path/to/proof-data \
  MyProject/MyProof.lean
```

This command uses that project's compiled dependencies and source search paths.
It writes syntax trees, tactic goals, premise references, and import paths under
the output directory without changing the proof files. It makes no API calls.
The existing Python loaders and proof-tree reconstruction accept these exports.
To run the model pipeline on those exports, with `OPENAI_API_KEY` already set:

```bash
python scripts/informalize_project.py \
  --project /path/to/project \
  --exports /path/to/proof-data \
  --output /path/to/generated-proofs \
  MyProject/MyProof.lean
```

Use repeated `--theorem NAME` options to select results and repeated
`--context-namespace NAMESPACE` options to include descriptions of imported
namespaces beyond the project's own declarations. An optional `--combine NAME`
applies the upstream summary prompt once more to the generated helper proofs,
with `NAME` as the target statement. That final combination across theorems is an
extension to the original per-theorem pipeline.

The runner uses the original `gpt-4.1-mini` model, tactic templates, and recursive
summarizer. It creates project-specific premise descriptions from source, saves
raw requests and responses, and caches completed requests. Seven newly supported
tactics use added templates without additional few-shot examples. Unsupported
tactics raise an error instead of silently shifting the step explanations.
The output directory may contain private proof material and should stay outside
published repository content.

Run the offline extraction checks after building:

```bash
python -m unittest discover -s tests -v
```

The checks load the exports through the Python pipeline, reconstruct two theorem
proof trees, resolve premise source paths, and ensure an invalid Lean proof fails
without exporting proof data.

The upstream examples, saved output, and instructions below are historical and
were produced with Lean 4.10. Updating all example proofs is outside this port.

-----

## Objective

We aim to create a framework that outputs human-readable natural language mathematical proofs from formal proofs. By doing so, we intend to solve one of the major challenges in autoformalization technology: the scarcity of data.

-----
![](<methodology.png>)
-----

## How to Use

1.  Install **Visual Studio Code**.
2.  Set up **Lean 4** by following the instructions at `https://lean-lang.org/install/#setting-up-lean`.
3.  Open the file `ExportInfo/DataExtraction.lean` and select **Restart File** from the "∀" button in the top-right corner.
4.  Wait for the build to complete. (This may take anywhere from 30 minutes to 2 hours).
5.  Run `source make_env.sh` to install the necessary modules.
6.  Make `.env` file in the root folder and set OpenAI API Key in the following format.
```
OPENAI_API_KEY = <YOUR_API_KEY>
```
7.  Run `source Informalize.sh <PATH>` to output the informalized results to the `Informalization/ExportData/` directory. For `<PATH>`, provide the path to a `.lean` file or a directory containing `.lean` files located under `ExportInfos/LeanExportInfos`.




