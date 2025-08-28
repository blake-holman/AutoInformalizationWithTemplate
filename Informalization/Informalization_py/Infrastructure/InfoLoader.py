from DomainService.IInfoLoader import ITacticInfoLoader, IPremiseInfoLoader
import DomainModel.ParseDataStructure as DataStructure
from typing import List, Tuple, Optional
from pathlib import Path
import json
import re

class TacticInfoLoader(ITacticInfoLoader) : 
    def load(self, path : Path) -> List[DataStructure.TacticInfo] :
        """
        load TacticInfo from path.
        """
        path = path.resolve()
        if (not path.exists()) :
            raise RuntimeError(f"given path doesn't exist : {path}")
        tacticInfos = []
        with open(path.resolve().as_posix(), 'r',encoding="UTF-8") as f:
            loaded_json = json.load(f)
            for tacticInfo in loaded_json:
                tacticInfos.append(
                    DataStructure.TacticInfo(
                        startPos=int(tacticInfo['startPos']), 
                        endPos=int(tacticInfo['endPos']),
                        goalsBefore=tacticInfo['goalsBefore'],
                        goalsAfter=tacticInfo['goalsAfter'],
                        tacticCommand=tacticInfo['tacticCommand'],
                        appliedTactic=tacticInfo['appliedTactic'], 
                        tacticDocument=tacticInfo['tacticDocument'] if ('tacticDocument' in tacticInfo) else None
                        ))
        return tacticInfos

class PremiseInfoLoader(IPremiseInfoLoader):
    def load(self, path : Path) -> List[DataStructure.PremiseInfo] :
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
                (decl, desc) = self.__split_detail__(premiseInfo["detail"])
                premiseInfos.append(
                    DataStructure.PremiseInfo(
                        moduleName=premiseInfo['moduleName'],
                        kind=premiseInfo['kind'],
                        fullName=premiseInfo['fullName'],
                        definitionPath=premiseInfo['definitionPath'],
                        startPos= premiseInfo['startPos'],
                        endPos=premiseInfo['endPos'],
                        definitionStartPos=DataStructure.Position(
                            line=int(premiseInfo['definitionStartPos']['line']),
                            column=int(premiseInfo['definitionStartPos']['column'])
                        ) if premiseInfo['definitionStartPos'] != None else None,
                        definitionEndPos=DataStructure.Position(
                            line=int(premiseInfo['definitionEndPos']['line']),
                            column=int(premiseInfo['definitionEndPos']['column'])
                        ) if premiseInfo['definitionEndPos'] != None else None,
                        declaration = decl,
                        description = desc
                    )
                )
        return premiseInfos

    def __split_detail__(self, detail : str)->Tuple[str, Optional[str]]:
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
        

        