import abc
import DomainModel.ParseDataStructure as DataStructure
from typing import List
from pathlib import Path



class ITacticInfoLoader(metaclass=abc.ABCMeta) :
    """
    An interface that defines the declaration of functions used to read tacticInfo.json files.
    """
    @abc.abstractmethod
    def load(self, path : Path) -> List[DataStructure.TacticInfo] :
        """
        load TacticInfo from path.
        """
        raise NotImplementedError()

class IPremiseInfoLoader(metaclass=abc.ABCMeta) :
    """
    定義情報が格納されたクラス(premiseInfo.json)をデータ構造にパースするクラスが提供するメソッドを定義したインターフェース
    """
    @abc.abstractmethod
    def load(self, path : Path) -> List[DataStructure.PremiseInfo] :
        """
        パスからPremiseInfoをロードする
        """
        raise NotImplementedError()