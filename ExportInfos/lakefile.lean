import Lake
open Lake DSL

package «Lean_ExportInfos»

@[default_target]
lean_lib «LeanExportInfos» where
  roots := #[`DataExtraction, `LeanExportInfos.SpecificPremiseExtraction]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "85e3a25e006c35636f0e53b0e9296caca2685bc0"
