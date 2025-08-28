from typing import Tuple, List
import re
from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo

class CorrespondencePremiseExtractor():
    """
    TacticInfoから関連するPremiseを抽出するロジックを提供するクラス。
    """
    def __init__(self):
        self.__target_premise_kind__ = ["definition", "constructor", "theorem"]
    def __split_hypothesis_and_goals__(self, goals : str) -> Tuple[List[str], List[str]]:
        """
        goalsBefore及びgoalsAfterの文字列を仮定とゴールの文字列リストに分割する。

        返り値は [hypList, goalList]
        """
        hypAndGoals = re.split("⊢|\n\n", goals)
        # 配列の偶数インデックスは仮定部分 奇数インデックスはゴール部分
        hypList = [hypAndGoals[index] for index in range(len(hypAndGoals)) if index % 2 == 0]
        goalList = [hypAndGoals[index] for index in range(len(hypAndGoals)) if index % 2 != 0]
        return (hypList, goalList)

    def extract_correspond_premise_in_applied_tactic(self, tacticInfo : TacticInfo, premiseInfos : List[PremiseInfo])-> List[PremiseInfo]:
        """
        tacticで使用されているpremiseの情報を取得する
        """
        return self.__extract_correspond_premise__([tacticInfo.appliedTactic], tacticInfo, premiseInfos)
    
    def extract_correspond_premise_in_goals(self, tacticInfo : TacticInfo, premiseInfos : List[PremiseInfo])-> Tuple[List[PremiseInfo], List[PremiseInfo], List[PremiseInfo], List[PremiseInfo]]:
        """
        goalsBeforeおよびgoalsAfterに含まれるPremiseのリストを取得する。
        返り値は[goalsBeforeの仮定のPremiseリスト, goalsBeforeのゴールのPremiseリスト, goalsAfterの仮定のPremiseリスト, goalsAfterのゴールのPremiseリスト]
        """
        (goalsBeforeHypList, goalsBeforeGoalList) = self.__split_hypothesis_and_goals__(tacticInfo.goalsBefore)
        (goalsAfterHypList, goalsAfterGoalList) = self.__split_hypothesis_and_goals__(tacticInfo.goalsAfter)
        goalsBeforeHypPremise = self.__extract_correspond_premise__(goalsBeforeHypList, tacticInfo, premiseInfos)
        goalsBeforeGoalPremise = self.__extract_correspond_premise__(goalsBeforeGoalList, tacticInfo, premiseInfos)
        goalsAfterHypPremise = self.__extract_correspond_premise__(goalsAfterHypList, tacticInfo, premiseInfos)
        goalsAfterGoalPremise = self.__extract_correspond_premise__(goalsAfterGoalList, tacticInfo, premiseInfos)
        return (goalsBeforeHypPremise, goalsBeforeGoalPremise, goalsAfterHypPremise, goalsAfterGoalPremise)
    

    def __extract_correspond_premise__(self, targetSentences : List[str], tacticInfo  : TacticInfo, premiseInfos : List[PremiseInfo]) -> List[PremiseInfo]:
        """
        指定文字列内に含まれているpremiseの情報を取得する。
        """
        result = {}
        for targetSentence in targetSentences:
            for premiseInfo in premiseInfos:
                target = re.escape(premiseInfo.fullName.split('.')[-1])
                # Exist.intro が intro タクティクとマッチしてしまう問題への対処
                if target == tacticInfo.tacticCommand:
                    continue
                if premiseInfo.kind == 'definition':
                    # 定義名は前後に空白もしくは特定の記号があるときだけマッチングする
                    regex = r"(?<![^\[\s,.])"+rf"{target}"+r"(?![^\]\s,])"
                else:
                    # 定義以外はカスタム単語境界でキャプチャする
                    regex = r"(?<![a-zA-Z0-9_'])"+ rf"{target}" +r"(?![a-zA-Z0-9_'])"
                try:
                    captured = re.findall(regex, targetSentence)
                except re.PatternError as e:
                    print(regex)
                    raise e
                if len(captured) > 0 and not (premiseInfo.fullName in result.keys()) and premiseInfo.kind in ["definition", "constructor", "theorem"]:
                    result[premiseInfo.fullName] = premiseInfo
        return list(result.values())

