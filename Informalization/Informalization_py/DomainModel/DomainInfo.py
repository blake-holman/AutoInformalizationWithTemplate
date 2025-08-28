from dataclasses import dataclass
from typing import List
from enum import Enum

@dataclass(frozen=True)
class DomainInfo:
   domainType : str
   rootDomain : str
   subDomains : List[str]
