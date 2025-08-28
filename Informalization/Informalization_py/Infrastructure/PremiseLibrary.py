from pathlib import Path
from typing import Dict, Optional, List
import json
import re
import os
from DomainModel.ParseDataStructure import PremiseInfo
from injector import singleton
import random
from DomainModel.PremiseLibraryDataStructure import PremiseLibraryData, PremiseType, Explanatory
from threading import Lock

class SingletonMeta(type):
    _instances = {}
    _lock : Lock = Lock()

    def __call__(self, *args, **kwds):
        with self._lock:
            if self not in self._instances:
                instance = super().__call__(*args, **kwds)
                self._instances[self] = instance
        return self._instances[self]

class PremiseLibrary(metaclass = SingletonMeta):
    def __init__(self):
        self.__library_data_path__ = "Library"
        self.__library__ : Dict = {}
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
    def check_data_existence(self, premise : PremiseInfo)-> bool:
        moduleName = self.__get_module_name__(premise.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        keys.append(premise.fullName)
        # keys の最初の要素がライブラリの親フォルダ名、二番目の要素がドメインもしくはファイル名
        if len(keys) < 2:
            raise ValueError
        filePath = Path(__file__).parent.joinpath("Library", keys[0], keys[1] + ".json")
        # ファイルに保存されているかどうかを返す
        return os.path.exists(filePath)
    def load_data(self, module_name : str)->None:
        moduleName = self.__get_module_name__(module_name)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        # keys の最初の要素がライブラリの親フォルダ名、二番目の要素がドメインもしくはファイル名
        if len(keys) < 2:
            raise ValueError
        filePath = Path(__file__).parent.joinpath("Library", keys[0], keys[1] + ".json")
        # ファイルを読み込んでローカルのライブラリデータとする
        if os.path.exists(filePath):
            with open(filePath, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.__library__[keys[0]] = {}
            self.__library__[keys[0]][keys[1]] = data

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
    def get_data(self, premiseInfo : PremiseInfo)-> PremiseLibraryData | None:
        layer = self.__library__
        moduleName = self.__get_module_name__(premiseInfo.moduleName)
        keys = re.split(r'(?<!«)\.', moduleName)
        keys[-1] += ".lean"
        for key in keys:
            if key in layer.keys():
                layer = layer[key]
            else:
                return None
        if not premiseInfo.fullName in layer.keys():
            return None
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
        self.write_to_file()
    def write_to_file(self):
        library_files_dir = Path(__file__).parent.joinpath(self.__library_data_path__).absolute()
        for top_key in self.__library__.keys():
            dirpath = library_files_dir.joinpath(top_key)
            if not os.path.exists(dirpath):
                os.mkdir(dirpath)
            for domain_key in self.__library__[top_key].keys():
                domain_data = self.__library__[top_key][domain_key]
                with open(dirpath.joinpath(domain_key + ".json"), "w", encoding="utf-8") as f:
                    json.dump(domain_data, f, ensure_ascii=False, indent=2)
    def get_library(self)->Dict:
        return self.__library__
    def get_fewshots(self, premiseInfo : PremiseInfo, count: int)->Dict[str, str]:
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
