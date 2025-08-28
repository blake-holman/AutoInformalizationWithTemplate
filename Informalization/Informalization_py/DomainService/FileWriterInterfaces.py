import abc
from typing import List, Dict
from pathlib import Path
from DomainModel.ParseDataStructure import TacticInfo

class IFileWriter(metaclass=abc.ABCMeta) :
    """
    An interface that defines the declaration of functions used to save output data from framework.
    """
    @abc.abstractmethod
    def save_file(self, directory_path : Path, file_name : str, data : str):
        raise NotImplementedError()
    @abc.abstractmethod
    def save_dict(self, directory_path : Path, file_name : str, data : Dict):
        raise NotImplementedError()

class IInformalizationDataExporter:
    @abc.abstractmethod
    def save_data(self, filePath : Path, theorem_name : str, applied_tactics : List[str], answers : List[str], summary : str) -> None:
        raise NotImplementedError()