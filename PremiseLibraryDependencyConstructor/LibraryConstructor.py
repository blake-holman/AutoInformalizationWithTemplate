import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict
import json
from premise_descriptor_test import PremiseDiscriptor
from dataclass import PremiseInfo, PremiseLibraryData, Explanatory, PremiseType, load_premise
import re
from PremiseExtractor import PremiseExtractor
from dotenv import load_dotenv
import os
import random
from tqdm import tqdm


class PremiseLibrary:
    def __init__(self):
        self.__library_data_path__ = "premise_lib.json"
        self.__library__ : Dict = self.load_library()
        self.__common_few_shots__ = [
            PremiseLibraryData(
                type = PremiseType.Definition,
                code = "Even.{u_2} {α : Type u_2} [Add α] (a : α) : Prop",
                comment = "An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,\nfor some `r : α`.",
                explanatories=[],
                fullDefinition="def IsSquare (a : α) : Prop := ∃ r, a = r * r",
                description="A number which can be divided by 2."
            ),
            PremiseLibraryData(
                type = PremiseType.Definition,
                code = "Set.Nonempty.{u} {α : Type u} (s : Set α) : Prop",
                comment = "The property `s.Nonempty` expresses the fact that the set `s` is not empty. It should be used\nin theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks\nto the dot notation.",
                explanatories=[],
                fullDefinition="protected def Nonempty (s : Set α) : Prop :=\n  ∃ x, x ∈ s",
                description="A set which contains at least one element."
            ),
            PremiseLibraryData(
                type=PremiseType.Theorem,
                code = "mul_add.{x} {R : Type x} [Mul R] [Add R] [LeftDistribClass R] (a b c : R) : a * (b + c) = a * b + a * c",
                comment = "**Alias** of `left_distrib`.",
                explanatories=[],
                fullDefinition=None,
                description="Multiplying a number by a sum equals the sum of its products with each addend."
            )
        ]
    def __get_module_name__(self, moduleName : str)->str:
        return moduleName.replace("«.lake».packages.mathlib.", "")
    def check_existence(self, premise : PremiseInfo)->bool:
        moduleName = self.__get_module_name__(premise.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        keys.append(premise.fullName)
        library = self.__library__
        for key in keys:
            if not key in library.keys():
                return False
            library = library[key]
        return True

    def __convert_data_to_premise_library_data__(self, data: Dict)->PremiseLibraryData:
        explanatories = []
        for ex_key, ex_value in data["explanatories"].items():
            explanatories.append(Explanatory(ex_key, ex_value))
        return PremiseLibraryData(
            type=PremiseType.Definition if data["type"] == PremiseType.Definition.value else PremiseType.Theorem,
            code=data["code"],
            comment=data["comment"],
            explanatories=explanatories,
            fullDefinition=data["fullDefinition"],
            description=data["description"]
        )
    def get_data(self, premiseInfo : PremiseInfo)-> PremiseLibraryData:
        layer = self.__library__
        moduleName = self.__get_module_name__(premiseInfo.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        for key in keys:
            if key in layer.keys():
                layer = layer[key]
            else:
                raise RuntimeError(f"モジュール参照エラー : {premiseInfo.moduleName}")
        if not premiseInfo.fullName in layer.keys():
            raise RuntimeError(f"premise名参照エラー : {premiseInfo.fullName} / {layer.keys()}")
        data = layer[premiseInfo.fullName]
        return self.__convert_data_to_premise_library_data__(data)
    def save_data(self, premiseInfo : PremiseInfo, premiseSource : str, explanatories : List[Explanatory], description : str):
        moduleName = self.__get_module_name__(premiseInfo.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        layer = self.__library__
        for key in keys:
            if not key in layer.keys():
                layer[key] = {}
            layer = layer[key]
        if premiseInfo.fullName in layer.keys():
            return
        explanatories_data = {}
        for ex in explanatories:
            explanatories_data[ex.name] = ex.description
        layer[premiseInfo.fullName] = {
            "type" : PremiseType.Definition.value if premiseInfo.kind == PremiseType.Definition.value else PremiseType.Theorem.value,
            "code" : premiseInfo.declaration,
            "comment" : premiseInfo.description,
            "explanatories" : explanatories_data,
            "fullDefinition" : premiseSource if premiseInfo.kind == PremiseType.Definition.value else None,
            "description" : description
        }
    def get_fewshots(self, premiseInfo : PremiseInfo, count: int)->List[PremiseLibraryData]:
        # 同じファイルの他のPremise -> 同じディレクトリの他のPremise -> ... と調査していく
        few_shots = []
        # まず同じソースコードファイルの他の定義があるかどうかチェックする
        moduleName = self.__get_module_name__(premiseInfo.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        isSameFileDataExists = True
        existDataDomain = ""
        library = self.__library__
        for key in keys:
            if key in library.keys():
                library = library[key]
                existDataDomain = key
            else:
                isSameFileDataExists = False
                break
        if not isSameFileDataExists:
            if existDataDomain == "":
                # そもそも同ドメインのデータがなかった時
                # 固定のfew-shot例を与える
                return self.__common_few_shots__
            # 同ドメインの別ファイルデータからfew-shotを取得する
            return self.__rec_get_few_shots__(library, count)
        keys = list(library.keys())
        # 同じファイルのデータを取得する。指定個数に満たない場合は最大数分取得する
        for key in random.sample(keys, len(keys)):
            few_shots.append(self.__convert_data_to_premise_library_data__(library[key]))
            if len(few_shots) >= count:
                return few_shots
        return few_shots
    def __rec_get_few_shots__(self, library : Dict, count : int)->List[PremiseLibraryData]:
        few_shots = []
        keys = list(library.keys())
        for key in random.sample(keys, len(keys)):
            if "description" in library[key].keys():
                few_shots.append(self.__convert_data_to_premise_library_data__(library[key]))
                if len(few_shots) >= count:
                    return few_shots
            else:
                few_shots.extend(self.__rec_get_few_shots__(library[key], count)) 
                if len(few_shots) > count:
                    return few_shots[:count]
                return few_shots
        return few_shots
    def load_library(self):
        with open(self.__library_data_path__, "r") as f:
            return json.load(f)
    def write_to_file(self):
        with open(self.__library_data_path__, "w", encoding="utf-8") as f:
            json.dump(self.__library__, f, ensure_ascii=False, indent=2)

@dataclass
class PriorityInfo:
    path : str
    level : int
    
class TokenCounter:
    def __init__(self):
        self.__token_count_info_path__ = "TokenCountInfo.json"
        self.__input_token_count__ = 0
        self.__output_token_count__ = 0
        self.__input_token_cost_per_million__ = 0.15
        self.__output_token_cost_per_million__ = 0.60
        self.__init_token_count__()
    def __init_token_count__(self):
        with open(self.__token_count_info_path__) as f:
            data = json.load(f)
            self.__input_token_count__ = data["input_token_count"]
            self.__output_token_count__ = data["output_token_count"]
    def add_token_count(self, inputTokenCount : int, outputTokenCount : int)->None:
        if inputTokenCount < 0 or outputTokenCount < 0:
            raise ValueError("トークン数の加算において負の値は許容されていません")
        self.__input_token_count__ += inputTokenCount
        self.__output_token_count__ += outputTokenCount
        self.print_current_spend()
    def print_current_spend(self):
        cost = (self.__input_token_count__ * self.__input_token_cost_per_million__ + self.__output_token_count__ * self.__output_token_cost_per_million__)/ 10**6
        print(f"current spend : {cost}")
    def write_to_file(self):
        data = json.dumps({"input_token_count" : self.__input_token_count__, "output_token_count" : self.__output_token_count__})
        with open(self.__token_count_info_path__, "w", encoding="utf-8") as f:
            f.write(data)

premiseDiscriptor = PremiseDiscriptor()
premiseExtractor = PremiseExtractor()
library = PremiseLibrary()
counter = TokenCounter()

def extract_correspond_premise(targetSentence : str, targetPremise: PremiseInfo, premiseInfos : List[PremiseInfo]) -> List[PremiseInfo]:
    """
    指定文字列内に含まれているpremiseの情報を取得する。
    """
    result = {}
    check_align = False
    aligns = premiseExtractor.extract_align(targetPremise)
    if aligns != None:
        check_align = True 
    for premiseInfo in premiseInfos:
        if check_align and premiseInfo.fullName in aligns:
            continue
        target = re.escape(premiseInfo.fullName.split('.')[-1])
        if premiseInfo.kind == 'definition':
            # 定義名は前後に空白もしくは特定の記号があるときだけマッチングする
            regex = r"(?<![^\[\s,.])"+rf"{target}"+r"(?![^\]\s,])"
        else:
            # 定義以外はカスタム単語境界でキャプチャする
            regex = r"(?<![a-zA-Z0-9_'])"+ rf"{target}" +r"(?![a-zA-Z0-9_'])"
        try:
            captured = re.findall(regex, targetSentence)
        except re.PatternError as e:
            print(regex)
            raise e
        if len(captured) > 0 and not (premiseInfo.fullName in result.keys()) and premiseInfo.kind in ["definition", "constructor", "theorem"]:
            result[premiseInfo.fullName] = premiseInfo
    return list(result.values())
def make_path_to_premise_info(path : str):
    load_dotenv()
    premiseDirectoryPath = os.getenv('')
    return Path(premiseDirectoryPath + path + "/premiseInfo.json")

def proc_description(path : str):
    pathObj = make_path_to_premise_info(path)
    premises = load_premise(pathObj)
    print(f"Path : {path}")
    for premise in tqdm(premises):
        # 該当leanファイル内で定義されているものを生成対象とする
        if path in premise.definitionPath:
            # すでにあるものは処理しない
            if library.check_existence(premise):
                continue
            # 定義抽出
            premiseSource = premiseExtractor.extract_premise_data(premise)

            if premise.kind == PremiseType.Definition.value:
                # 依存定義を抽出
                if premiseSource == None:
                    dependencies = []
                else:
                    dependencies = extract_correspond_premise(premiseSource.source, premise, premises)
            else:
                dependencies = extract_correspond_premise(premise.declaration, premise, premises)
            # 循環参照の場合に対応するため、premise自身は依存Premiseから除く
            removed = []
            for d in dependencies:
                if d.fullName in premise.fullName:
                    removed.append(d)
            for r in removed:
                dependencies.remove(r)
            # 依存定義の説明文を取得
            explanatories = []
            for dependency in dependencies:
                try:
                    dependency_data = library.get_data(dependency)
                    explanatories.append(Explanatory(dependency.fullName, dependency_data.description))
                except RuntimeError as e:
                    # .elan下の組み込みライブラリのものを参照していた場合は生成を行う
                    if ".elan" in dependency.definitionPath:
                        fewShots = library.get_fewshots(dependency, 3)
                        (input_token_count, output_token_count, desciption) = premiseDiscriptor.make_description(
                            premiseInfo= dependency,
                            explanatories=[],
                            few_shots=fewShots
                        )
                        source = premiseExtractor.extract_premise_data(dependency)
                        if source == None:
                            library.save_data(dependency, "", [], desciption)
                        else:
                            library.save_data(dependency, source.source, [], desciption)
                        align = premiseExtractor.extract_align(dependency)
                        if align != None:
                            for name in align:
                                dependency.fullName = name
                                if source == None:
                                    library.save_data(dependency, "", [], desciption)
                                else:
                                    library.save_data(dependency, source.source, [], desciption)
                        counter.add_token_count(input_token_count, output_token_count)
                        explanatories.append(Explanatory(dependency.fullName, desciption))
                    # それ以外は無視する
                    else:
                        print(f"参照すべき定義がライブラリ上に保存されていません : {dependency.fullName} / {dependency.definitionPath}")
                        continue
            # 説明文を生成
            fewShots = library.get_fewshots(premise, 3)
            (input_token_count, output_token_count, desciption) = premiseDiscriptor.make_description(
                premiseInfo= premise,
                explanatories=explanatories,
                few_shots=fewShots
            )
            if premiseSource == None:
                library.save_data(premise, "", explanatories, desciption)
            else:
                library.save_data(premise, premiseSource.source, explanatories, desciption)
            align = premiseExtractor.extract_align(premise)
            if align != None:
                for name in align:
                    premise.fullName = name
                    if premiseSource == None:
                        library.save_data(premise, "", explanatories, desciption)
                    else:
                        library.save_data(premise, premiseSource.source, explanatories, desciption)
            counter.add_token_count(input_token_count, output_token_count)
            

def make_library(priorities : List[PriorityInfo]):
    current_level = 1
    current_level_data_count = 0
    while True:
        print(f"current_level : {current_level}")
        removed = []
        for priority in priorities:
            if priority.level <= current_level:
                removed.append(priority)
            if priority.level == current_level:
                proc_description(priority.path)
                current_level_data_count = current_level_data_count + 1
                library.write_to_file()
                counter.write_to_file()
        if current_level_data_count == 0:
            print(f"current_level : {current_level} / process stopped.")
            return
        for item in removed:
            priorities.remove(item)
        print(f"remain items : {len(priorities)}")
        current_level = current_level + 1
        current_level_data_count = 0

            
def load_priorities(path : Path)->List[PriorityInfo]:
    data = []
    with open(path, "r") as f:
        priorities = json.load(f)
        for info in priorities:
            data.append(PriorityInfo(info["path"], info["level"]))
    return data

if __name__ == "__main__":
    args = sys.argv
    if len(args) == 2:
        pathObj = Path(args[1])
        priorities = load_priorities(pathObj)
        try:
            make_library(priorities)
        except Exception as e:
            exception_type, exception_object, exception_traceback = sys.exc_info()
            filename = exception_traceback.tb_frame.f_code.co_filename
            line_no = exception_traceback.tb_lineno
            print(f"{filename}の{line_no}行目でエラーが発生しました。詳細：{e}")
            library.write_to_file()
            counter.write_to_file()