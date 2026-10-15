import Lean
import Mathlib
import Lake
import Batteries
import Init.Data.List.Basic
import «LeanExportInfos».PathExploreModules
import «LeanExportInfos».TraceInfoStructures
import «LeanExportInfos».PrettyPrint
import Lean.Server.InfoUtils

open Lean Elab System

set_option linter.unusedVariables false

namespace SearchTrees
open InfoStructure

/--
ゴール情報を分割する際に使用する構造体
-/
structure GoalsInfo where
  hypBefore : String
  goalBefore : String
  hypAfter : String
  goalAfter : String

structure AppliedModuleInfo where
  type? : Option Format
  exprExplicit? : Option Format
  docs? : Option String

/--
tacticInfo の syntax が byTactic だったとき、その構成要素が妥当なものになっているのかを確認する。
異常な構造になっていた場合は false が返るため、assert! でチェックすること。
-/
private def validateByTactic (tacticInfo : TacticInfo) : Bool :=
  match tacticInfo.stx with
  -- by + タクティクの列にちゃんとなっていれば OK
  | .node _ _ #[.atom _ "by", .node _ ``Lean.Parser.Tactic.tacticSeq _] => true
  | _ => false

/--
tacticInfo の syntax が tacticの列(tacticSeq) だったとき、その構成要素が妥当なものになっているのかを確認する。
異常な構造になっていた場合は false が返るため、assert! でチェックすること。
-/

private def validateTacticSeq (tacticInfo : TacticInfo) : Bool :=
  match tacticInfo.stx with
    -- tac ; tac みたいな場合か . tac みたいなやつであればOK
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeq1Indented _] => true
    | .node _ _ #[.node _ ``Lean.Parser.Tactic.tacticSeqBracketed _] => true
    -- おかしな奴だけはじく。
    | _ => false

/--
tacticInfo の syntax 構造をバリデーションする。
-/
private def validateTacticInfoSyntax (tacticInfo : TacticInfo) : TraceM Unit := do
  match tacticInfo.stx.getKind with
  | ``Lean.Parser.Term.byTactic =>
    assert! validateByTactic tacticInfo
  | ``Lean.Parser.Tactic.tacticSeq =>
    assert! validateTacticSeq tacticInfo
  | _ => pure ()
/--
適用したterm や tactic などの情報を抽出する。
-/
private def extractAppliedModuleInfo (context : ContextInfo) (info : Info) : IO AppliedModuleInfo := do
  context.runMetaM info.lctx do
    let type? ← match (← info.type?) with
      | some type => some <$> (Meta.ppExpr =<< instantiateMVars type)
      | none => pure none
    let exprExplicit? ← match info with
      | Elab.Info.ofTermInfo ti =>
        pure <| some <| ← (Meta.ppExpr ti.expr)
      | Elab.Info.ofFieldInfo fi => pure <| some <| fi.fieldName.toString
      | _ => pure none
    return (AppliedModuleInfo.mk type? exprExplicit? (← info.docString?))

/--
tactic の情報を抽出する。
-/
private def extractTacticInfo (contextInfo : ContextInfo) (tacticInfo : TacticInfo) (parentTree : InfoTree) (depth : Nat): TraceM Unit := do
  validateTacticInfoSyntax tacticInfo
  -- 親の InfoTree に対してマッチング
  match parentTree with
  -- tactic の情報を持つ子があったとき
  | .node (Info.ofTacticInfo i) _ =>
    -- kind を取ってくる
    match i.stx.getKind with
    -- tac ; tac, . tac, rw [~~~] のとき
    | ``Lean.Parser.Tactic.tacticSeq1Indented | ``Lean.Parser.Tactic.tacticSeqBracketed | ``Lean.Parser.Tactic.rewriteSeq | ``Batteries.Tactic.seq_focus =>
      let appliedModuleInfo ← extractAppliedModuleInfo contextInfo (Info.ofTacticInfo tacticInfo)
      -- tactic 適用前のContextInfo
      let contextBefore := { contextInfo with mctx := tacticInfo.mctxBefore }
      -- tactic 適用後のContextInfo
      let mut appliedTactic := tacticInfo.stx.prettyPrint.pretty
      let contextAfter := { contextInfo with mctx := tacticInfo.mctxAfter }
      let goalsBefore ← PrettyPrint.prettyPrintGoals contextBefore tacticInfo.goalsBefore
      let goalsAfter ← PrettyPrint.prettyPrintGoals contextAfter tacticInfo.goalsAfter

      if goalsBefore == "no goals" || goalsBefore == goalsAfter then
        pure ()
      else
        let some startPosition := tacticInfo.stx.getPos? true | pure ()
        let some endPosition := tacticInfo.stx.getTailPos? true | pure ()
        let fileMap ← getFileMap
        match tacticInfo.stx with
          | .node _ _ stxs =>
            if tacticInfo.stx.getKind == ``Lean.Parser.Tactic.paren then
              pure ()
            else
              let mut command := stxs[0]!.prettyPrint.pretty
              if i.stx.getKind == ``Lean.Parser.Tactic.rewriteSeq then
                command := "rw_element"
              if tacticInfo.stx.getKind == ``Batteries.Tactic.seq_focus ∨ tacticInfo.stx.getKind == ``Lean.Parser.Tactic.«tactic_<;>_» then
                command := "<;>"
              -- node ならここまでの情報をstate Monad である traceInfo に追加
              modify fun trace => {
                trace with tacticInfos := trace.tacticInfos.push {
                  goalsBefore := goalsBefore,
                  goalsAfter := goalsAfter,
                  tacticCommand := command,
                  appliedTactic := appliedTactic,
                  tacticDocument := appliedModuleInfo.docs?,
                  startPos := startPosition,
                  endPos := endPosition
                }
              }
          | _ => pure ()
    | _ => pure ()
  | _ => pure ()

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
          | ConstantInfo.opaqueInfo _ => "opaque"
          | ConstantInfo.quotInfo _ => "quot"
          | ConstantInfo.inductInfo _ => "inductive"
          | ConstantInfo.ctorInfo _ => "constructor"
          | ConstantInfo.recInfo _ => "recursor"
      | none => none
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
    | .ofTacticInfo tacticInfo =>
      extractTacticInfo context tacticInfo parentTree depth
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

end SearchTrees
