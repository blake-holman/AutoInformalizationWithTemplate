from yaml import safe_load
from pathlib import Path
from dataclasses import dataclass
from typing import List

@dataclass(frozen=True)
class TokenInfo:
    token : str
    description : str

class TokenInfoRepository():
    def __init__(self):
        with open(Path(__file__).resolve().parent.joinpath('tokenInfo.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__tokens__ = safe_load(f)
    def get(self, template : str)->List[TokenInfo]:
        tokenInfos = []
        for token in self.__tokens__.keys():
            if token in template:
                tokenInfos.append(
                    TokenInfo(
                        token= token,
                        description=self.__tokens__[token]
                    )
                )
        return tokenInfos

repository = TokenInfoRepository()

def getTokenInfo(template : str) -> List[TokenInfo]:
    return repository.get(template)