import abc
from DomainModel.AbstractSyntaxTree import NodeBase
from typing import List
from pathlib import Path



class IAbstractSyntaxTreeLoader(metaclass=abc.ABCMeta) :
    """
    An interface that defines the declaration of functions used to read tacticInfo.json files.
    """
    @abc.abstractmethod
    def load(self, path : Path) -> List[NodeBase] :
        """
        load TacticInfo from path.
        """
        raise NotImplementedError()