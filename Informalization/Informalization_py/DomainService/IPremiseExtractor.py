import abc
from DomainModel.ParseDataStructure import PremiseInfo
from typing import Optional
from pathlib import Path

from dataclasses import dataclass

@dataclass(frozen=True)
class PremiseSource:
    source : str

class IPremiseExtractor(metaclass = abc.ABCMeta):
    """
    前提情報をファイルから抜き出すクラスが提供する機能を定義したインターフェース
    """
    @abc.abstractmethod
    # @deprecated("PremiseLibraryの構築に伴い非推奨")
    def extract_premise_data(self, premiseInfo : PremiseInfo) -> Optional[PremiseSource]:
        """
        premiseInfoの情報から具体的な情報を抜き出す
        """
        raise NotImplementedError
    @abc.abstractmethod
    def extract_description(self, premiseInfo : PremiseInfo, definitionPath : Path) -> Optional[PremiseSource]:
        """
        premiseの説明文をライブラリから得る
        """
        raise NotImplementedError