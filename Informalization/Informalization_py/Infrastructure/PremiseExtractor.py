from pathlib import Path
from typing import List
from DomainModel.ParseDataStructure import PremiseInfo
from DomainService.IPremiseExtractor import IPremiseExtractor, PremiseSource
import re
import json
import os
from Infrastructure.PremiseLibrary import PremiseLibrary
from injector import inject

class PremiseExtractor(IPremiseExtractor):
    @inject
    def __init__(self) -> None:
        self.__theorem_capture_eq__ = re.compile(r"(theorem|lemma)([\s\S]*?)\s*?:=", re.DOTALL)
        self.__theorem_capture_case__ = re.compile(r"(theorem|lemma)([\s\S]*?)\s*?\|", re.DOTALL)
        self.__definition_capture__ = re.compile(r"def([\s\S]*?):=([\s\S]*?)")
        self.__kind_proc_dict__ = {
            'theorem' : self.__proc_theorem__,
            'definition' : self.__proc_definition__,
            'constructor' : self.__proc_constructor__,
        }
        self.__library__ = PremiseLibrary()
    def __get_module_name__(self, moduleName : str)->str:
        return moduleName.replace("«.lake».packages.mathlib.", "")
    def extract_description(self, premiseInfo: PremiseInfo, definitionPath : Path) -> PremiseSource | None:
        moduleName = self.__get_module_name__(premiseInfo.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        keys.append(premiseInfo.fullName)
        # keys の最初の要素がライブラリの親フォルダ名、二番目の要素がドメインもしくはファイル名
        if len(keys) < 2:
            raise ValueError
        filePath = Path(__file__).parent.joinpath("Library", keys[0], keys[1] + ".json")
        premisePath = Path(premiseInfo.definitionPath).absolute()
        # ファイルに保存されていないときはローカルライブラリの方を検索する
        if not os.path.exists(filePath) or premisePath.as_posix() in definitionPath.as_posix():
            data = self.__library__.get_data(premiseInfo)
            if not data == None:
                return PremiseSource(data.description)
            else:
                return None
        with open(Path(__file__).parent.joinpath("Library", keys[0], keys[1] + ".json"), "r", encoding="utf-8") as f:
            data = json.load(f)
        for key in keys[2:]:
            if not key in data.keys():
                return None
            data = data[key]
        return PremiseSource(data["description"])
    def extract_premise_data(self, premiseInfo: PremiseInfo) -> PremiseSource | None:
        return PremiseSource(premiseInfo.declaration)
        definitionPath = Path(__file__).resolve().parent.parent.parent.joinpath("ExportData", premiseInfo.definitionPath)
        with open(definitionPath, "r", encoding="UTF-8") as f:
            source = f.readlines()
        # line は 1 スタートなので -1 して配列の 0 スタートに合わせる
        if premiseInfo.kind in self.__kind_proc_dict__.keys():
            return self.__kind_proc_dict__[premiseInfo.kind](premiseInfo, source)
        else:
            return None
    def __proc_constructor__(self, premiseInfo : PremiseInfo, source : List[str]) -> PremiseSource | None:
        # 次の空行が来るまで読み取って渡す。
        premise_source = ''
        for s in source[premiseInfo.definitionStartPos.line - 1:]:
            if s == '\n':
                break
            premise_source += s
        return PremiseSource(premise_source)
    def __proc_theorem__(self, premiseInfo : PremiseInfo, source : List[str]) -> PremiseSource | None:
        # line は 1 スタートなので -1 して配列の 0 スタートに合わせる
        premise_source = ''
        for s in source[premiseInfo.definitionStartPos.line - 1:]:
            if s == '\n':
                break
            premise_source += s
        # theorem(lemma) foo: bar := ... の形で書かれている場合は、foo : bar の部分だけを抜き出す
        # theorem(lemma) foo: bar | 0 => _ | n => _   ... の形で書かれている場合も、foo : bar の部分だけを抜き出す
        eq_match = self.__theorem_capture_eq__.search(premise_source)
        case_match = self.__theorem_capture_case__.search(premise_source)
        # 両方マッチした場合はより短い方を採用する
        if eq_match != None and case_match != None:
            eq_result = eq_match.group(2).replace('\n', ' ').lstrip().rstrip()
            case_result = case_match.group(2).replace('\n', ' ').lstrip().rstrip()
            if len(eq_result) < len(case_result):
                return PremiseSource(eq_result)
            else:
                return PremiseSource(case_result)
        if eq_match != None:
            return PremiseSource(eq_match.group(2).replace('\n', ' ').lstrip().rstrip())
        if case_match != None:
            return PremiseSource(case_match.group(2).replace('\n', ' ').lstrip().rstrip())
        return None
    def __proc_definition__(self, premiseInfo : PremiseInfo, source : List[str])-> PremiseSource | None:
        premise_sources = source[premiseInfo.definitionStartPos.line - 1:]
        result = ""
        for s in premise_sources:
            if s == '\n' or s.lstrip().startswith('#') or s.lstrip().startswith('export'):
                if result != "":
                    return PremiseSource(result.replace('\n', ' ').lstrip().rstrip())
                return None
            result += s
        return PremiseSource(result.replace('\n', ' ').lstrip().rstrip())
        

        
