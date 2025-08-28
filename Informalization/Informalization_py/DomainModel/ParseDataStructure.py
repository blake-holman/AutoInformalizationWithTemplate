from dataclasses import dataclass
from typing import Optional, List

@dataclass
class TacticInfo:
    startPos : int
    endPos : int
    goalsBefore : str
    goalsAfter : str
    tacticCommand : str
    appliedTactic :str
    tacticDocument : Optional[str]
    
    def __eq__(self, value):
       return isinstance(value, self.__class__) and self.startPos == value.startPos and self.endPos == value.endPos and self.goalsBefore == value.goalsBefore and self.goalsAfter == value.goalsAfter and self.tacticCommand == value.tacticCommand and self.appliedTactic == value.appliedTactic
    def __ne__(self, value):
       return (not self.__eq__(value))

@dataclass(frozen=True)
class Position:
   line : int
   column : int
@dataclass(frozen=True)
class PremiseInfo:
  fullName : str
  definitionStartPos : Optional[Position]
  definitionEndPos : Optional[Position]
  moduleName : str
  definitionPath : str
  startPos : int
  endPos : int
  kind : str
  declaration : str
  description : Optional[str]
