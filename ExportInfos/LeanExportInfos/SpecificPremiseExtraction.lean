import Lean
import Lake
import «LeanExportInfos».PathExploreModules
import Mathlib
import Batteries
import Init.Data.List.Basic
import «LeanExportInfos».PrettyPrint
import Lean.Server.InfoUtils

set_option maxHeartbeats 2000000  -- 10x the default maxHeartbeats.

set_option linter.unusedVariables false

open Lean Elab System
namespace Info

instance : ToJson Substring.Raw where
  toJson s := toJson s.toString

instance : ToJson String.Pos.Raw where
  toJson n := toJson n.1

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax
deriving instance ToJson for Position

/--
tactic の情報を抽出する。
-/

structure PremiseTraceInfo where
  fullName : String
  definitionStartPos : Option Position
  definitionEndPos : Option Position
  moduleName : String
  definitionPath : String
  startPos : Option String.Pos.Raw
  endPos : Option String.Pos.Raw
  kind : Option String
  detail : Option String
deriving ToJson

structure TraceInfo where
  premiseInfos : Array PremiseTraceInfo
deriving ToJson

-- State にすることで TraceInfo を書き換え可能にする。
abbrev TraceM := StateT TraceInfo MetaM

end Info

set_option linter.unusedVariables false

namespace Search
open Info

/--
term の情報を抽出する。

-/
private def extractTermInfo (context : ContextInfo) (termInfo : TermInfo) (environment : Environment) : TraceM Unit := do
  if termInfo.stx.getKind == ``Lean.Parser.Term.byTactic then
    pure ()
  let info := Info.ofTermInfo termInfo
  let text ← info.fmtHover? context
  let fmtText : String:= match text with
    | some t => toString t.fmt
    | none => ""
  let some fullName := termInfo.expr.constName? | return ()
  let kind : Option String :=
    match environment.find? fullName with
      | some info =>
        match info with
          | ConstantInfo.defnInfo _ => "definition"
          | ConstantInfo.axiomInfo _ => "axiom"
          | ConstantInfo.thmInfo _ => "theorem"
          | ConstantInfo.opaqueInfo _ => ""
          | ConstantInfo.quotInfo _ => ""
          | ConstantInfo.inductInfo _ => ""
          | ConstantInfo.ctorInfo _ => "constructor"
          | ConstantInfo.recInfo _ => ""
      | none => none
  if kind != "" && kind != none then
    let fileMap ← getFileMap
    let positionBefore : Option String.Pos.Raw := termInfo.toElabInfo.stx.getPos?
    let positionAfter : Option String.Pos.Raw := termInfo.toElabInfo.stx.getTailPos?
    let declarationRanges ← withEnv environment $ findDeclarationRanges? fullName
    let definitionStartPos : Option Position :=
      match declarationRanges with
        | some declRanges => declRanges.selectionRange.pos
        | none => none
    let definitionEndPos : Option Position :=
      match declarationRanges with
        | some declRanges => declRanges.selectionRange.endPos
        | none => none
    let moduleName :=
      if let some moduleIndex := environment.const2ModIdx[fullName]? then
        environment.header.moduleNames[moduleIndex.toNat]!
      else
        environment.header.mainModule
    let mut definitionPath := toString $ ← PathModule.findLeanFile moduleName
    if definitionPath.startsWith "./" then
      -- ./ を除く
      definitionPath := (definitionPath.drop 2).toString
    if definitionPath.startsWith "/lake/" then
      definitionPath := (mkFilePath [".lake", (definitionPath.drop 6).toString]).toString
    definitionPath := toString $ ← PathModule.getAbsolutePath (mkFilePath [definitionPath])
    let pb : Option Position := match positionBefore with
      | some info => fileMap.toPosition info
      | none => none
    let pa : Option Position := match positionAfter with
      | some info => fileMap.toPosition info
      | none => none
    if definitionStartPos != pb && definitionEndPos != pa then
      -- 情報をStateモナドのtraceに格納する
      modify fun trace => {
        trace with premiseInfos := trace.premiseInfos.push {
          fullName := toString fullName,
          definitionStartPos := definitionStartPos,
          definitionEndPos := definitionEndPos,
          definitionPath := definitionPath,
          moduleName := toString moduleName,
          startPos := positionBefore,
          endPos := positionAfter,
          kind := kind
          detail := fmtText
        }
      }
  pure ()

/--
情報の種類ごとに担当のメソッドに引き渡す。
-/
def extractInfo (context : ContextInfo) (info : Info) (parentTree : InfoTree) (environment : Environment) (depth : Nat): TraceM Unit := do
  match info with
    | .ofTermInfo termInfo =>
      extractTermInfo context termInfo environment
    | _ => pure ()

/--
再帰的に木構造を探索する。
-/
partial def searchTree (contextInfo : ContextInfo) (infoTree : InfoTree) (parentTree : InfoTree) (environment : Environment) (depth : Nat): TraceM Unit := do
  let mut currentDepth := depth
  match infoTree with
    | .context context' remainTree =>
      match context'.mergeIntoOuter? contextInfo with
        | some context => searchTree context remainTree infoTree environment currentDepth
        | none => panic! "Cannot synthesize contexts"
    | .node info children =>
      extractInfo contextInfo info parentTree environment currentDepth
      for child in children do
        searchTree contextInfo child infoTree environment currentDepth
    | _ => pure ()

/--
親となる木構造に対して探索を行う。
-/
def searchTopTree (tree : InfoTree) (env : Environment) : TraceM Unit := do
  match tree with
    | .context context ramainTree =>
      match context.mergeIntoOuter? none with
        | some context => searchTree context ramainTree tree env 0
        | none => panic! "Cannot access to Top InfoTree"
    | _ => pure ()

/--
引数に渡された木構造を順番に探索する。
-/
def searchAllTrees(trees : Array InfoTree) (environment : Environment) : TraceM TraceInfo := do
  for tree in trees do
    searchTopTree tree environment
  get

end Search


namespace Import
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
end Import
namespace Export

open Info
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

def exportInfos (filePath : FilePath) (header : Lean.Elab.HeaderSyntax) (premiseInfo : Array PremiseTraceInfo): IO Unit := do
  let currentDir ← IO.currentDir
  assert! currentDir.fileName != "lean4"
  let absPath := (← PathModule.getAbsolutePath filePath)
  let relativePath? := PathModule.getRelativePart absPath currentDir
  match relativePath? with
    | none => throw $ IO.userError "relative path does not exists."
    | some path =>
      let parentDirectoryName := (← IO.getEnv "INFORMALIZATION_EXPORT_DIR").getD "Export"
      let premiseInfoJsonPath := mkFilePath [parentDirectoryName, "premises", path.toString, "premiseInfo.json"]
      IO.println premiseInfoJsonPath
      PathModule.makeParentDirectories premiseInfoJsonPath
      IO.FS.writeFile premiseInfoJsonPath (toJson premiseInfo).pretty
      let depPath := mkFilePath [parentDirectoryName, "premises", path.toString, "dep_paths.txt"]
      PathModule.makeParentDirectories depPath
      let importInfo ← Import.getImportInfos header
      IO.println s!"importInfo : {importInfo}"
      IO.FS.writeFile depPath importInfo
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
  let traceM := (Search.searchAllTrees allTree environment').run'  ⟨#[]⟩
  let (trace, _) ← traceM.run'.toIO {fileName := s!"{path}", fileMap := FileMap.ofString file} {env := environment}
  Export.exportInfos path header trace.premiseInfos
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
      let t ← IO.asTask $ IO.Process.run {cmd := "lake", args := #["env", "lean", "--run", "SpecificPremiseExtraction.lean", path.toString]}
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
lake env lean --run SpecificPremiseExtraction.lean LeanExportInfos/TargetFile/Basic.lean で実行する
-/
