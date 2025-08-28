from dataclasses import dataclass
from enum import Enum
from typing import Optional, List

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