from dataclasses import dataclass
from enum import Enum
from typing import List
from DomainModel.InformalizationData import InformalizationData
from DomainModel.ParseDataStructure import TacticInfo
import abc

class TacticExampleState(Enum):
    Execute = 0
    Skip = 1
    NotExists = 9999

# class Tactic(list, Enum):

#     @classmethod
#     def value_of(cls, target_value : str):
#         """
#         該当するものがなかった時は None が返るので注意
#         """
#         for e in Tactic:
#             if target_value.lstrip().rstrip() in e.value :
#                 return e
#         return None

@dataclass(frozen=True)
class TacticExampleInfo:
    state : TacticExampleState
    examples : List[InformalizationData]

@dataclass(frozen=True)
class StatementFewShotExample:
    statement : str
    definitions : List[str]
    output : str

@dataclass(frozen=True)
class StatementInfo:
    statement : str
    definitions : List[str]

class ITacticFewShotExampleRepository(metaclass=abc.ABCMeta):
    @abc.abstractmethod
    def get(self, tacticInfo : TacticInfo) -> TacticExampleInfo:
        raise NotImplementedError()

class IStatementFewShotExampleRepository(metaclass=abc.ABCMeta):
    @abc.abstractmethod
    def get(self, statement : str) -> List[StatementFewShotExample]:
        raise NotImplementedError()