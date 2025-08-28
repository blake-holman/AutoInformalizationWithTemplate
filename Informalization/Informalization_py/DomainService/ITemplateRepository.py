import abc
from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo
from typing import Optional, Dict, Tuple, List
from enum import Flag, auto

from dataclasses import dataclass

class AdditionalPremiseRequirement(Flag):
    """
    追加で取得するpremiseをどこから取得するかを表す列挙型。
    そもそも追加で取得しない場合は noneが返される。
    """
    none = auto()
    goalBefore = auto()
    goalAfter = auto()

@dataclass(frozen=True)
class TemplateInfo:
    """
    タクティクの逆形式化プロンプトに用いるテンプレートの情報が格納されるデータクラス。
    """
    template : str
    tokenInfos : Dict[str, str]

class ITemplateRepository(metaclass = abc.ABCMeta):
    """
    タクティクの逆形式化に用いるテンプレートデータに対する操作を提供するリポジトリクラスのインターフェース。
    """
    @abc.abstractmethod
    def get(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        ) -> Optional[Tuple[TemplateInfo, AdditionalPremiseRequirement]]:
        """
        tacticInfoの情報から適切なテンプレート情報を取得する。
        """
        raise NotImplementedError