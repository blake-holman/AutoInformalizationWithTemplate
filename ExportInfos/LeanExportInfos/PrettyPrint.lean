import Lean
import Lake

open Lean Elab System

namespace PrettyPrint

/--
pretty - print のネストに使用するスペースの数
-/
def indentSize : Int := 2
/--
引数に渡された文字列の末尾に改行記号を追加する。
-/
private def insertLineBreak(str : String) : String :=
  if str.isEmpty then
    str
  else
    str ++ "\n"

/--
引数に渡された情報を整形して文字列として返す。
-/
private def formatInformation(identityNames : List Name) (type? : Option Expr) (varInfoText : String) : MetaM String := do
  if identityNames.isEmpty then
    return varInfoText
  else
    let infoTxt := insertLineBreak varInfoText
    match type? with
      | some type =>
        -- 型情報があるときは x y z : ℕ みたいな感じで出力
        let formattedType := ← Meta.ppExpr type
        let names := Format.joinSep identityNames.reverse (format " ")
        let typeWithNest := Format.nest indentSize (Format.line ++ formattedType)
        return (infoTxt ++ (names ++ " : " ++ typeWithNest).group).pretty
      | none =>
        return infoTxt

/--
変数情報を見やすい形に整形して文字列として出力する。
-/
private def prettyPrintVariables(variableNames  : List Name) (previousType? : Option Expr) (varInfoTxt : String) (localDeclaration : LocalDecl) : MetaM (List Name × Option Expr × String) := do
  match localDeclaration with
  -- ローカル変数
  | .cdecl _ _ localVarName type _ _ =>
    let localVarName := localVarName.simpMacroScopes
    let instType ← instantiateMVars type
    if previousType? == none || previousType? == some instType then
      return (localVarName::variableNames, some instType, varInfoTxt)
    else do
      let formattedNames ← formatInformation variableNames previousType? varInfoTxt
      return ([localVarName], some instType, formattedNames)
    | .ldecl _ _ bindedFreeVarName type value _ _ => do
      let bindedFreeVarName := bindedFreeVarName.simpMacroScopes
      let varInfoTxt ← formatInformation variableNames previousType? varInfoTxt
      let varInfoTxt := insertLineBreak varInfoTxt
      let type ← instantiateMVars type
      let formattedType ← Meta.ppExpr type
      let value ← instantiateMVars value
      let formattedValue ← Meta.ppExpr value
      let varInfoTxt := varInfoTxt ++  (format bindedFreeVarName ++ " : " ++ formattedType  ++ " := " ++ Format.nest indentSize (Format.line ++ formattedValue)).group.pretty
      return ([], none, varInfoTxt)

/--
ゴールの情報を成形して文字列として出力する。
-/
private def prettyPrintGoal(mvarId : MVarId) : MetaM String := do
  let decl := (← getMCtx).findDecl? mvarId
  match decl with
    | some mvarDeclaration =>
      let localContext := (mvarDeclaration.lctx).sanitizeNames.run' {options := (← getOptions)}
      Meta.withLCtx localContext mvarDeclaration.localInstances do
        let (variableNames, type?, varInfoTxt) ← localContext.foldlM (init := ([], none, "")) fun (variableNames, previousType?, varInfoTxt) (localDeclaration : LocalDecl) =>
          if localDeclaration.isAuxDecl || localDeclaration.isImplementationDetail then
            return (variableNames, previousType?, varInfoTxt)
          else
            prettyPrintVariables variableNames previousType? varInfoTxt localDeclaration
        let formattedInfo ← formatInformation variableNames type? varInfoTxt
        let formattedGoalType ← Meta.ppExpr (← instantiateMVars mvarDeclaration.type)
        let formattedGoal := Meta.getGoalPrefix mvarDeclaration ++ Format.nest indentSize formattedGoalType
        let formattedInfo := (insertLineBreak formattedInfo) ++ formattedGoal.pretty
        match mvarDeclaration.userName with
          | Name.anonymous => return formattedInfo
          | name => return (insertLineBreak ("case " ++ name.eraseMacroScopes.toString)) ++ formattedInfo
    | none => return "there are no goals"

/--
引数に渡された ContextInfo 上で各ゴールを pretty-printし、 文字列として結合して返す。
-/
def prettyPrintGoals(contextInfo : ContextInfo) (goals : List MVarId) : IO String :=
  if goals.isEmpty then
    return "no goals"
  else
    let formattedGoals := contextInfo.runMetaM {} (return Std.Format.prefixJoin "\n\n" (← goals.mapM (prettyPrintGoal ·)))
    return (← formattedGoals).pretty.trimAscii.toString
end PrettyPrint
