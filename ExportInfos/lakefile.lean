import Lake
open Lake DSL

package «Lean_ExportInfos» where
  -- add package configuration options here

lean_lib «LeanExportInfos» where
  -- add library configuration options here

@[default_target]
lean_exe «lean_exportinfos» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
