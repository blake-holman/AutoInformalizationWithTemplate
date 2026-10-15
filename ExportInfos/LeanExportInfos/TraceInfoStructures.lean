import Lean
import Lake

open Lean Elab System
namespace InfoStructure

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

structure TacticTraceInfo where
  goalsBefore : String
  goalsAfter : String
  tacticCommand : String
  appliedTactic : String
  tacticDocument : Option String
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
deriving ToJson

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
  abstractSyntaxTree : Array Syntax
  tacticInfos : Array TacticTraceInfo
  premiseInfos : Array PremiseTraceInfo
deriving ToJson

-- State にすることで TraceInfo を書き換え可能にする。
abbrev TraceM := StateT TraceInfo MetaM

end InfoStructure
