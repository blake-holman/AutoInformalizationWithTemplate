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
To run the model pipeline, install Codex CLI and sign in through ChatGPT first.
`codex login status` must report `Logged in using ChatGPT`. This fork uses
`codex exec` and has no paid API fallback; it does not require an API key.

Run it on those exports:

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

The runner uses the Codex model and reasoning effort from `~/.codex/config.toml`
(or `$CODEX_HOME/config.toml`), with the existing tactic templates and recursive
summarizer. Override these using `INFORMALIZATION_MODEL` and
`INFORMALIZATION_REASONING_EFFORT`; `INFORMALIZATION_CODEX` selects the executable.
Each request runs in an empty temporary directory, requires ChatGPT authentication,
and ignores API-key environment variables and user provider configuration.
It creates project-specific premise descriptions from source, saves
raw requests and responses, and caches completed requests. Seven newly supported
tactics use added templates without additional few-shot examples. Unsupported
tactics raise an error instead of silently shifting the step explanations.
The output directory may contain private proof material and should stay outside
published repository content.

This is a different model experiment from the original GPT-4.1-mini run. The CLI
receives the existing conversation messages serialized as JSON and does not apply
the upstream temperature setting. Both differences are recorded in request
metadata. Use a fresh output directory for a new model or backend so older answers
cannot be reused silently. `INFORMALIZATION_TIMEOUT_SECONDS` sets the per-request
timeout (default 900 seconds).

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
6.  For this fork, install Codex CLI and sign in through ChatGPT. The original API-key backend has been replaced by the headless adapter described above.
7.  Run `source Informalize.sh <PATH>` to output the informalized results to the `Informalization/ExportData/` directory. For `<PATH>`, provide the path to a `.lean` file or a directory containing `.lean` files located under `ExportInfos/LeanExportInfos`.




