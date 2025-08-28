from DomainService.IFewShotExampleRepository import ITacticFewShotExampleRepository, IStatementFewShotExampleRepository, TacticExampleInfo, TacticExampleState, StatementFewShotExample
from DomainModel.InformalizationData import InformalizationData
from yaml import safe_load
from DomainModel.ParseDataStructure import TacticInfo
from typing import Optional, List
import re
from pathlib import Path

class TacticFewShotExampleRepository(ITacticFewShotExampleRepository):
    """
    Few-Shotの例として与えるデータの管理及び操作機能を提供するクラス
    """
    def __init__(self) -> None:
        # few-shot例を与える
        with open(Path(__file__).resolve().parent.joinpath('fewshots.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__few_shot_examples__ = safe_load(f)
        # データのキー名と対応するtacticとの対応辞書
        with open(Path(__file__).resolve().parent.joinpath('tacticCorrespondenceDict.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__tactic_correspondence_dict__ = safe_load(f)
        # tacticInfoの情報によって分岐が必要なtacticの名前と処理関数との対応辞書
        self.__tactic_need_branch__ = {
            "rewrite" : self.__proc_rewrite__,
            "have" : self.__proc_have__,
            "suffices" : self.__proc_suffices__,
            "simp" : self.__proc_simp__,
            "norm_num" : self.__proc_norm_num__
        }
        # 逆形式化をスキップするtactic
        self.__skip_target__ = [
            "norm_cast", "all_goals", "any_goals", "repeat", "<;>"
        ]
        # have の条件分岐に使用する正規表現
        self.__have_match__ = re.compile(r"have.*?:.*?:=[\\n|\s]*?by", re.DOTALL)
        # suffices の条件分岐に使用する正規表現
        self.__suffices_by_match__ = re.compile(r"(suffices.*?:?.*?)by", re.DOTALL)
        self.__suffices_from_match__ = re.compile(r"(suffices.*?:?.*?)from", re.DOTALL)

    def __get_correspond_key__(self, tacticCommand : str) -> Optional[str]:
        """
        tacticCommandから対応するキーを取得する
        """
        for key, values in self.__tactic_correspondence_dict__.items():
            if tacticCommand in values:
                return key
        return None

    def __proc_rewrite__(self, tacticInfo : TacticInfo):
        """
        rw コマンドの取得先データの条件分岐
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__few_shot_examples__["rw_with_no_goals"]
        return self.__few_shot_examples__["rw_with_remain_goals"]
    def __proc_have__(self, tacticInfo : TacticInfo):
        """
        have コマンドの取得先データの条件分岐
        """
        if self.__have_match__.search(tacticInfo.appliedTactic):
            return self.__few_shot_examples__["have_with_by"]
        return self.__few_shot_examples__["have_without_by"]
    def __proc_suffices__(self, tacticInfo : TacticInfo):
        """
        suffices コマンドの取得先データの条件分岐
        """
        byMatch = self.__suffices_by_match__.search(tacticInfo.appliedTactic)
        fromMatch = self.__suffices_from_match__.search(tacticInfo.appliedTactic)
        if byMatch == None and fromMatch == None:
            raise RuntimeError(f'Unknown suffices syntax : {tacticInfo.appliedTactic}')
        elif byMatch != None and fromMatch != None:
            byInfo = byMatch.group(1)
            fromInfo = fromInfo.group(1)
            if len(byInfo) < len(fromInfo):
                return self.__few_shot_examples__["suffices_by"]
            else:
                return self.__few_shot_examples__["suffices_from"]
        elif byMatch != None:
            return self.__few_shot_examples__["suffices_by"]
        return self.__few_shot_examples__["suffices_from"]
    def __proc_simp__(self, tacticInfo : TacticInfo):
        """
        simp コマンドの取得先データの条件分岐
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__few_shot_examples__["simp_finish"]
        return self.__few_shot_examples__["simp_rw"]
    def __proc_norm_num__(self, tacticInfo : TacticInfo):
        """
        norm_num コマンドの取得先データの条件分岐
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__few_shot_examples__["norm_num_finish"]
        return self.__few_shot_examples__["norm_num_rw"]    
    def get(self, tacticInfo : TacticInfo) -> TacticExampleInfo:
        """
        対応するfew-shot例を取得する
        """
        if tacticInfo.tacticCommand in self.__skip_target__:
            # スキップ対象のtacticはその旨通知
            return TacticExampleInfo(TacticExampleState.Skip, [])
        tactic = self.__get_correspond_key__(tacticInfo.tacticCommand.lstrip().rstrip())
        if tactic == None:
            # few-shotが未実装のtacticが来た時も通知
            return TacticExampleInfo(TacticExampleState.NotExists, [])
        if tactic in self.__tactic_need_branch__.keys():
            # 分岐が必要なtacticのときは処理関数にfew-shot例の取得を委譲
            raw_data = self.__tactic_need_branch__[tactic](tacticInfo)
        else:
            # 辞書からデータを取ってくる
            raw_data = self.__few_shot_examples__[tactic]
        examples = []
        for datum in raw_data:
            examples.append(
                InformalizationData(
                    appliedTactic=datum["appliedTactic"],
                    goalsBefore=datum["goalsBefore"],
                    goalsAfter=datum["goalsAfter"],
                    defintionsAndTheorems= datum["additionalInfo"],
                    output=datum["output"]
                )
            )
        return TacticExampleInfo(TacticExampleState.Execute, examples)

class StatementFewShotExampleRepository(IStatementFewShotExampleRepository):
    def __init__(self):
        # 返すデータ 現在は固定
        self.__few_shots__ = [
            StatementFewShotExample(
                statement="a b :  ℤ\nha :  Odd a\nhb :  Odd b\n⊢ 4 ∣ a + b ∨ 4 ∣ a - b",
                definitions=[
                    "def Odd (a : α) : Prop := ∃ k, a = 2 * k + 1"  
                ],
                output="If \\( a \\) and \\( b \\) are odd integers, then either \\( a + b \\) is divisible by 4, or \\( a - b \\) is divisible by 4."
            ),
            StatementFewShotExample(
                statement = "a b :  ℕ\n⊢ Even a ∧ Even b → Even (a + b)",
                definitions = [
                    "def IsSquare (a : α) : Prop := ∃ r, a = r * r"
                ],
                output="The sum of even numbers \\( a \\) and \\( b \\) is even."
            ),
            StatementFewShotExample(
                statement="α :  Type u_1\ninst✝² :  CancelCommMonoidWithZero α\ninst✝¹ :  NormalizationMonoid α\ninst✝ :  GCDMonoid α\nk m n :  α\n⊢ gcd k (m * n) ∣ gcd k m * gcd k n",
                definitions = [
                    "gcd : α → α → α", 
                ],
                output="the gcd of \\( k \\) and \\( m \\cdot n \\) divides the product of the gcd of \\( k \\) with \\( m \\) and the gcd of \\( k \\) with \\( n \\)."
            )
        ]
    def get(self, statement : str) -> List[StatementFewShotExample]:
        return self.__few_shots__