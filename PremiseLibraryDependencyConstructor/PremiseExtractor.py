from pathlib import Path
from typing import List
from dataclass import PremiseInfo
import re
from dataclasses import dataclass

@dataclass(frozen=True)
class PremiseSource:
    source : str


class PremiseExtractor():
    def __init__(self) -> None:
        self.__theorem_capture_eq__ = re.compile(r"(theorem|lemma)([\s\S]*?)\s*?:=", re.DOTALL)
        self.__theorem_capture_case__ = re.compile(r"(theorem|lemma)([\s\S]*?)\s*?\|", re.DOTALL)
        self.__definition_capture__ = re.compile(r"def([\s\S]*?):=([\s\S]*?)")
        self.__kind_proc_dict__ = {
            'theorem' : self.__proc_theorem__,
            'definition' : self.__proc_definition__,
            'constructor' : self.__proc_constructor__,
        }
        self.__align_tag__ = "#align"
    def extract_align(self, premiseInfo : PremiseInfo) -> List[str] | None:
        if premiseInfo.definitionStartPos == None:
            return None
        definitionPath = Path(__file__).resolve().parent.parent.parent.joinpath("ExportData", premiseInfo.definitionPath)
        with open(definitionPath, "r", encoding="UTF-8") as f:
            source = f.readlines()
        premise_source = ''
        # 次の空行まで取得する
        for s in source[premiseInfo.definitionStartPos.line - 1:]:
            if s == '\n':
                break
            premise_source += s
        isStructure = False
        if not("def" in premise_source or "theorem" in premise_source or "lemma" in premise_source):
            # 上の空行まで取得する
            upper_source = source[:premiseInfo.definitionStartPos.line - 1]
            upper_source.reverse()
            for s in upper_source:
                if s == "\n" or "--" in s or "-/" in s or "/--" in s:
                    break
                premise_source = s + premise_source
            if "class" in premise_source or "structure" in premise_source or "inductive" in premise_source:
                isStructure = True
        if self.__align_tag__ in premise_source:
            aligns = premise_source.split(self.__align_tag__)[1:]
            formatted = []
            for align in aligns:
                splitted = align.split(" ")
                for name in splitted:
                    if name == "":
                        continue
                    if isStructure:
                        component_name = premiseInfo.fullName.split(".")[-1]
                        name += "." + component_name
                    formatted.append(name.replace("\n", ""))
            return formatted
        else:
            return None
    def extract_premise_data(self, premiseInfo: PremiseInfo) -> PremiseSource | None:
        if premiseInfo.definitionStartPos == None:
            return None
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
        

        
