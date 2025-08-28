from pathlib import Path
from typing import Optional
from DomainModel.DomainInfo import DomainInfo
# ほんとうはroots用のリポジトリクラスを作った方がいいが過剰すぎるので今回はなし
from yaml import safe_load

class DomainExtractor():
    def __init__(self):
        with open(Path(__file__).resolve().parent.joinpath('domain_roots.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__domain_roots__= safe_load(f)
            self.unknownDomainKey = "Unknown"
    def extract_domain_roots(self, path : Path) -> DomainInfo:
        if path.suffix != ".lean":
            raise RuntimeError(f"ファイルパスがleanのものではありません!! : {path.as_posix()}")
        parts = list(path.parts)
        partsLength = len(parts)
        for key, paths in self.__domain_roots__.items():
            pathsLength = len(paths)
            if partsLength < pathsLength:
                continue
            subParts = []
            for i in range(partsLength - pathsLength + 1):
                subParts.append(parts[i : i + pathsLength])
            isTarget = False
            index = -1
            for i, subPart in enumerate(subParts):
                if paths == subPart:
                    isTarget = True
                    index = i + pathsLength -1
                    break
            if isTarget:
                # DomainInfo抽出
                return self.__extract_domain_info_from_path__(key, path, index)
            else:
                continue
        return DomainInfo(self.unknownDomainKey, "", parts[:-1])
    def __extract_domain_info_from_path__(self, domainType : str, path : Path, rootIndex : int) -> DomainInfo:
        if path.suffix in path.parts[rootIndex + 1]:
            return DomainInfo(domainType, "", [])
        return DomainInfo(domainType, path.parts[rootIndex + 1], path.parts[rootIndex + 2: -1])
