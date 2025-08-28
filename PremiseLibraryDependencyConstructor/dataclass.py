from dataclasses import dataclass
from typing import Optional, List, Tuple
import re
from pathlib import Path
import json
from enum import Enum

@dataclass(frozen=True)
class Position:
   line : int
   column : int

@dataclass
class PremiseInfo:
  fullName : str
  definitionStartPos : Optional[Position]
  definitionEndPos : Optional[Position]
  moduleName : str
  definitionPath : str
  startPos : int
  endPos : int
  kind : str
  detail : str
  declaration : str
  description : Optional[str]
  fullDefinition : Optional[str]

class PremiseType(Enum):
    Definition = "definition"
    Theorem = "theorem"

@dataclass
class Explanatory:
    name : str
    description : str
@dataclass
class PremiseLibraryData:
    type : PremiseType
    code : str
    comment : Optional[str]
    explanatories : List[Explanatory]
    fullDefinition : Optional[str]
    description : str


def load_premise(path : Path) -> List[PremiseInfo] :
    """
    パスからPremiseInfoをロードする
    """
    path = path.resolve()
    if (not path.exists()) :
        raise RuntimeError(f"Given path doesn't exist. path : {path}")
    premiseInfos = []
    with open(path.as_posix(), 'r', encoding="UTF-8") as f:
        loaded_json = json.load(f)
        for premiseInfo in loaded_json:
            (decl, desc) = split_detail(premiseInfo["detail"])
            premiseInfos.append(
                PremiseInfo(
                    moduleName=premiseInfo['moduleName'],
                    kind=premiseInfo['kind'],
                    fullName=premiseInfo['fullName'],
                    definitionPath=premiseInfo['definitionPath'],
                    startPos= premiseInfo['startPos'],
                    endPos=premiseInfo['endPos'],
                    definitionStartPos=Position(
                        line=int(premiseInfo['definitionStartPos']['line']),
                        column=int(premiseInfo['definitionStartPos']['column'])
                    ) if premiseInfo['definitionStartPos'] != None else None,
                    definitionEndPos=Position(
                        line=int(premiseInfo['definitionEndPos']['line']),
                        column=int(premiseInfo['definitionEndPos']['column'])
                    ) if premiseInfo['definitionEndPos'] != None else None,
                    detail=premiseInfo["detail"],
                    declaration = decl,
                    description = desc,
                    fullDefinition=None
                )
            )
    return premiseInfos

def split_detail(detail : str)->Tuple[str, Optional[str]]:
    """
    Leanから抽出されたPremiseの詳細情報 (Hoverで表示される情報 / MarkDownで書かれている)を情報の内容ごとに分割する 
    返り値は (宣言情報, optional(説明文))
    """
    # 詳細情報はmarkdownの罫線 (***) で区切られている
    # 情報の並びは (宣言情報 | 説明文 | 宣言されているモジュール)
    # このうち後ろ二つはない場合がある。
    # 宣言情報と、もしあれば説明文を取得する。
    rawComponents = detail.split("\n***\n")
    declarationMatch = re.search("```lean\\n(.*?)\\n```", rawComponents[0], re.DOTALL)
    declaration = None
    if declarationMatch != None:
        declaration = declarationMatch.group(1)
    if len(rawComponents) >= 2:
        if "import" in rawComponents[1]:
            return (declaration, None)
        return (declaration, rawComponents[1])
    else:
        return (declaration, None)
    
# '```lean\nFaithfulSMul.eq_of_smul_eq_smul.{u_11, u_12} {M : Type u_11} {α : Type u_12} [SMul M α] [self : FaithfulSMul M α]\n  {m₁ m₂ : M} : (∀ (a : α), m₁ • a = m₂ • a) → m₁ = m₂\n```\n***\nTwo elements `m₁` and `m₂` are equal whenever they act in the same way on all points. '
    