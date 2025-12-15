# Natural Language Translation of Formal Proofs through Informalization of Proof Steps and Recursive Summarization along Proof Structure

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




