from typing import NamedTuple, List

class InformalizationData(NamedTuple):
    appliedTactic : str
    goalsBefore : str
    goalsAfter : str
    defintionsAndTheorems : List[str]
    output : str