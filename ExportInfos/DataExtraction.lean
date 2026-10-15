import Lean
import Lake
import «LeanExportInfos».PathExploreModules
import «LeanExportInfos».TraceInfoStructures
import «LeanExportInfos».TreeTraverseModules

open Lean Elab System InfoStructure

set_option maxHeartbeats 2000000  -- 10x the default maxHeartbeats.

set_option linter.unusedVariables false

namespace ImportInfo
/--
ファイルの入力情報を文字列として取得する。
-/
def getImportInfos(header : Lean.Elab.HeaderSyntax) : IO String := do
  let mut paths : Array String := #[]
  for info in header.imports do
    if info.module != `Init then
      let path := (← PathModule.findLeanFile info.module).toString
      if !paths.contains path then
        paths := paths.push path
  return "\n".intercalate paths.toList
end ImportInfo
namespace Export

/--
メッセージログからエラーを出力する。
エラーがない場合は何もしない。
-/
def printErrorMessage(msg : MessageLog) : IO Unit := do
  if msg.hasErrors then
    for message in msg.toList do
      if message.severity == .error then
        IO.println s!"エラー発生 : {← message.toString}"
    throw $ IO.userError "Errors has occurred during import process!"
/--
ファイルの出力を行う。
-/

def exportInfos (filePath : FilePath) (header : Lean.Elab.HeaderSyntax) (ast : Array Syntax) (tacticInfo : Array TacticTraceInfo) (premiseInfo : Array PremiseTraceInfo): IO Unit := do
  let currentDir ← IO.currentDir
  assert! currentDir.fileName != "lean4"
  let absPath := (← PathModule.getAbsolutePath filePath)
  let relativePath? := PathModule.getRelativePart absPath currentDir
  match relativePath? with
    | none => throw $ IO.userError "relative path does not exists."
    | some path =>
      let parentDirectoryName := (← IO.getEnv "INFORMALIZATION_EXPORT_DIR").getD "Export"
      let astJsonPath := mkFilePath [parentDirectoryName, path.toString, "abstractSyntaxTreeInfo.json"]
      let tacticInfoJsonPath := mkFilePath [parentDirectoryName, path.toString, "tacticInfo.json"]
      let premiseInfoJsonPath := mkFilePath [parentDirectoryName, path.toString, "premiseInfo.json"]
      PathModule.makeParentDirectories astJsonPath
      PathModule.makeParentDirectories tacticInfoJsonPath
      PathModule.makeParentDirectories premiseInfoJsonPath
      IO.FS.writeFile astJsonPath (toJson ast).pretty
      IO.FS.writeFile tacticInfoJsonPath (toJson tacticInfo).pretty
      IO.FS.writeFile premiseInfoJsonPath (toJson premiseInfo).pretty
      let depPath := mkFilePath [parentDirectoryName, path.toString, "dep_paths.txt"]
      PathModule.makeParentDirectories depPath
      IO.FS.writeFile depPath (← ImportInfo.getImportInfos header)
end Export
/--
パスからデータを抽出する。
-/
unsafe def extractDataFromFile(path : System.FilePath) : IO Unit := do
  let absPath ← PathModule.getAbsolutePath path
  -- ファイル読み込み
  let file ← IO.FS.readFile absPath
  -- おまじないのようなもの
  Lean.enableInitializersExecution

  -- 読み込んだファイルとパスから InputContext を作成
  -- ファイルをパースしてlean内部の情報を取得できるようにする
  let inputContext := Lean.Parser.mkInputContext file absPath.toString
  -- ヘッダー (import 部分) の情報を抽出する。
  let (header, parserState, msg) ← Lean.Parser.parseHeader inputContext
  -- ヘッダーから環境を抽出
  let (environment, msg) ← processHeader header {} msg inputContext
  Export.printErrorMessage msg
  -- 環境のメインモジュール設定
  let environment := environment.setMainModule (← moduleNameOfFileName path none)
  -- commandState 作成
  let commandState := { Command.mkState environment msg {} with infoState.enabled := true }
  -- コマンドを実行
  let state ← IO.processCommands inputContext parserState commandState
  Export.printErrorMessage state.commandState.messages
  let environment' := state.commandState.env
  let commands := state.commands.pop
  -- ファイル内の全ての木構造を抽出
  let allTree := state.commandState.infoState.trees.toArray

  -- コマンドから抽出された infoState を渡して各木構造をすべてトレース
  let traceM := (SearchTrees.searchAllTrees allTree environment').run'  ⟨#[header] ++ commands, #[], #[]⟩
  let (trace, _) ← traceM.run'.toIO {fileName := s!"{path}", fileMap := FileMap.ofString file} {env := environment}
  Export.exportInfos path header trace.abstractSyntaxTree trace.tacticInfos trace.premiseInfos
  pure ()

/-
  データ抽出が可能なファイルかどうかをチェックする
-/
def enableExtraction(path : FilePath) : IO Bool := do
  if (← path.isDir) ∨ path.extension != "lean" then
    return false
  let currentDir ← IO.currentDir
  let some relativePath := PathModule.getRelativePart path currentDir | throw $ IO.userError s!"Invalid path was given : {path}"
  let libRelative := PathModule.getRelativePart relativePath PathModule.packageDirectoryPath
  if libRelative != none then
    return false
  let some oleanPath := PathModule.fetchBuildFile "lib" relativePath "olean" | throw $ IO.userError s!"Invalid path was given : {path}"
  return ← oleanPath.pathExists

/--
  フォルダ内のすべてのleanファイルの情報を抽出する
-/
def extractDataInFolder (folderPath : FilePath) : IO Unit := do
  let mut taskList := #[]
  for path in ← System.FilePath.walkDir folderPath do
    if ← enableExtraction path then
      let t ← IO.asTask $ IO.Process.run {cmd := "lake", args := #["env", "lean", "--run", "DataExtraction.lean", path.toString]}
      taskList := taskList.push (t, path)
  for (t, path) in taskList do
    match ← IO.wait t with
      | Except.error _ =>
        println! s!"Failed to process {path}"
        pure ()
      | Except.ok _ => pure ()



unsafe def main (args : List String): IO Unit := do
  match args with
  | [path] =>
    let path ← PathModule.getAbsolutePath ⟨path⟩
    if ← path.isDir then
      extractDataInFolder path
    else
      extractDataFromFile path
  | _ => throw $ IO.userError "There are no path"

/-
lake env lean --run DataExtraction.lean LeanExportInfos/TargetFile/Basic.lean で実行する
-/
