from DomainService.ITemplateRepository import ITemplateRepository, TemplateInfo, AdditionalPremiseRequirement
from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo
from typing import Optional, List, Tuple, Dict
import re
from pathlib import Path
from yaml import safe_load
from Infrastructure.tokeninfo_repository import getTokenInfo
from enum import Enum

class CaseAnalysisState(Enum):
    Goal = "Goal"
    Hypothesis = "Hypothesis"

class TemplateRepository(ITemplateRepository):
    def __init__(self):
        with open(Path(__file__).resolve().parent.joinpath('template.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__templates__ = safe_load(f)
        with open(Path(__file__).resolve().parent.joinpath('tacticCorrespondenceDict.yaml').absolute(), 'r', encoding='UTF-8') as f:
            self.__tactic_correspondence_dict__ = safe_load(f)
        # tacticInfoの情報によって分岐が必要なtacticの名前と処理関数との対応辞書
        self.__tactic_need_branch__ = {
            "apply" : self.__proc_apply__,
            "rewrite" : self.__proc_rewrite__,
            # "let" : self.__proc_let__,
            "have" : self.__proc_have__,
            "suffices" : self.__proc_suffices__,
            "exact" : self.__proc_exact__,
            "ring" : self.__proc_ring__,
            "obtain" : self.__proc_obtain__,
            "cases" : self.__proc_cases__,
            "rcases" : self.__proc_rcases__,
            "simp" : self.__proc_simp__,
            "push_neg" : self.__proc_push_neg__,
            "norm_num" : self.__proc_norm_num__,
            "dot" : self.__proc_dot__,
            "refine" : self.__proc_refine__,
        }
        # have の条件分岐に使用する正規表現
        self.__have_match__ = re.compile(r"have.*?:.*?:=[\\n|\s]*?by", re.DOTALL)
        # suffices の条件分岐に使用する正規表現
        self.__suffices_by_match__ = re.compile(r"(suffices.*?:?.*?)by", re.DOTALL)
        self.__suffices_from_match__ = re.compile(r"(suffices.*?:?.*?)from", re.DOTALL)
        self.__obtain_split_match__ = re.compile(r"obtain.*?⟨.*?⟩.*?:=.*?")
        self.__case_analysis_pattern__ = "case (.*?)\\n"
        self.__rcases_hyp_split_match__ = re.compile(r"rcases .*? with ⟨.*?⟩", re.DOTALL)
        self.__simp_with_theorem_and_assumption_match__ = re.compile(r"[simp|simpa]\s+(only\s+)?\[(.*?)\]", re.DOTALL)
        self.__let_match__ = re.compile(r"let (.*?)\s*?:=\s+(.+)")
        self.__case_replace__ = re.compile(r"case .*?\n")
        self.__hypothesis_pattern__ = "(.*?)\\s*?:\\s+(.*?)\\n"
        self.__kinds_classified_as_theorem__ = ["theorem", "constructor"]
        self.__logic_symbols__ = ["∃", "∀", "∧", "→", "∨", "¬"]
        self.__relationship_symbols__ = ["<->", "↔", "=", "≠", "<", ">", "≤", "≥", "∈", "∉", "⊆", "⊂", "⊇", "⊃", "⊕", "⊕'", "≈", "∪", "∩", "\\"]
        self.__case_analysis_state__ : CaseAnalysisState = CaseAnalysisState.Goal
    def __get_correspond_key__(self, tacticCommand : str) -> Optional[str]:
        """
        tacticCommandから対応するキーを取得する
        """
        for key, values in self.__tactic_correspondence_dict__.items():
            if tacticCommand in values:
                return key
        return None

    def __is_theorem_contained__(self, premises : List[PremiseInfo]) -> bool:
        """
        与えられたpremiseの中に定理として扱われるものが含まれているかどうかをチェックする。
        """
        # appliedTacticPremisesにconstructorかtheoremが一つでも使われていればtrueとする
        for premise in premises:
            if premise.kind in self.__kinds_classified_as_theorem__:
                return True
        return False

    def __is_definition_contained__(self, premises : List[PremiseInfo]) -> bool:
        """
        与えられたpremiseの中に定義として扱われるものが含まれているかどうかをチェックする。
        """
        for premise in premises:
            if premise.kind == "definition":
                return True
        return False

    def __is_theorem_used__(self, appliedTacticPremises : List[PremiseInfo])-> bool:
        """
        appliedTacticが外部の定理を使っているかどうかをチェックする。
        """
        # 一旦appliedTacticPremisesの中に定理扱いされるものが含まれているかどうかのみで判定する
        return self.__is_theorem_contained__(appliedTacticPremises)

    def __is_definition_used__(self, appliedTacticPremises : List[PremiseInfo])-> bool:
        """
        appliedTacticが外部の定義を使っているかどうかをチェックする。
        """
        # 一旦appliedTacticPremisesの中に定義扱いされるものが含まれているかどうかのみで判定する
        return self.__is_definition_contained__(appliedTacticPremises)
    def __extract_specific_kind_premise__(self, kind : str, premises : List[PremiseInfo])->List[PremiseInfo]:
        """
        特定の種類のpremiseを抽出する
        """
        result = []
        for premise in premises:
            if premise.kind == kind:
                result.append(premise)
        return result
    def __extract_definition_premise__(self, premises : List[PremiseInfo])->List[PremiseInfo]:
        """
        定義のpremiseを抽出する
        """
        return self.__extract_specific_kind_premise__("definition", premises)
    
    def __is_assumption_used__(
            self, 
            goalsBefore : str,
            component : str,
            hypothesisPremise : List[PremiseInfo]
        )-> bool:
        """
        appliedTacticが仮定の命題情報を使っているかどうかをチェックする。
        """
        # 1. hypothesisBeforeから仮定を全て抽出して辞書にまとめる
        hypotheses : Dict[str, str]= {}
        goalsBefore = re.split("⊢|\n\n", goalsBefore)
        hypContexts = [goalsBefore[index] for index in range(len(goalsBefore)) if index % 2 == 0]
        for hypContext in hypContexts:
            hyps = re.findall(self.__hypothesis_pattern__, hypContext)
            for hyp in hyps:
                # a b c : Nat のような場合もあるので、スペースで区切ってそれぞれ対応する
                type = hyp[1]
                hypComponents = [c.lstrip().rstrip() for c in hyp[0].split(" ")]
                for c in hypComponents:
                    if not (c in hypotheses.keys()):
                        hypotheses[c] = type
        # 2. 各仮定についてその名前を抽出する。
        hypothesis_names = hypotheses.keys()
        # 3. appliedTacitcを見、仮定の名前が前後に文字もしくは数字が来ていない形で含まれているかどうかを確認
        contained_names = []
        for name in hypothesis_names:
            capture_pattern = "(?<!\\w)" + name + "(?!\\w)"
            if re.findall(capture_pattern, component):
                contained_names.append(name)
        # 4. もし一つも含まれていなければその時点でFalseを返す。
        if len(contained_names) == 0:
            return False
        # 5. もし含まれていた場合は、その仮定の型を見る。
        types = [hypotheses[name] for name in contained_names]
        # 6. 型が関係演算子、論理演算子を含む、もしくは外部の定義を含んでいた場合は仮定の命題を使っていると判定する。
        # 外部の定義を含むかどうかをまず判定する。
        definition_names = [premise.fullName.split(".")[-1] for premise in hypothesisPremise]
        for type in types:
            for name in definition_names:
                if name in type:
                    return True
        # 次に論理演算子を含むかどうかを判定する。
        for type in types:
            for symbol in self.__logic_symbols__:
                if symbol in type:
                    return True
        # 最後に関係演算子を含むかどうかを判定する。
        for type in types:
            for symbol in self.__relationship_symbols__:
                if symbol in type:
                    return True
        # ここまで通過したら数字などの他の仮定であり命題ではないとする。
        return False
    def __set_case_analysis_state__(self, tacticInfo : TacticInfo) -> CaseAnalysisState:
        """
        タクティクの場合分けを行っているのが仮定に対してなのかゴールに対してなのかの状態を設定する。
        場合分けタクティク適用後に呼び出すこと。
        """
        # ゴールを抽出
        # 
        splitted = re.split("⊢|\n\n", tacticInfo.goalsBefore)
        goals = []
        for index in range(len(splitted)):
            if index % 2 == 1:
                goals.append(splitted[index].lstrip().rstrip())
        # 重複があればゴールが同じなので仮定の場合分けになる。
        if len(goals) != len(set(goals)):
            return CaseAnalysisState.Hypothesis
        return CaseAnalysisState.Goal

    def __proc_apply__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたapplyの適用の場合に適したテンプレートを取得する。
        """
        key = "apply_rw"
        if "no goals" in tacticInfo.goalsAfter:
            key = "apply_finish"
        component = tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, "")
        # 構成要素がなければそれ用のテンプレートを返す
        if component.replace(" ", "") == "":
            return self.__templates__[key]["NonComponent"]
        # 構成要素の成り立ちを確認
        isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        # それぞれで適切なテンプレートを返す
        if isAssumptionUsed and isTheoremUsed:
            return self.__templates__[key]["AssumptionAndTheorem"]
        elif isAssumptionUsed:
            return self.__templates__[key]["OnlyAssumption"]
        else:
            return self.__templates__[key]["OnlyTheorem"]

    def __proc_rewrite__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたrewriteの適用の場合に適したテンプレートを取得する。
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__proc_rewrite_with_no_goals__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
        return self.__proc_rewrite_with_remain_goals__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
    def __proc_rewrite_with_no_goals__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        ) -> str:
        """
        タクティク情報から与えられたrewrite(ゴール証明)の適用の場合に適したテンプレートを取得する。
        """
        isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        if isAssumptionUsed and isTheoremUsed:
            return self.__templates__["rw_with_no_goals"]["AssumptionAndTheorem"]
        elif isAssumptionUsed:
            return self.__templates__["rw_with_no_goals"]["Assumption"]
        else:
            return self.__templates__["rw_with_no_goals"]["Theorem"]

    def __proc_rewrite_with_remain_goals__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        ) -> str:
        """
        タクティク情報から与えられたrewrite(書き換えのみ)の適用の場合に適したテンプレートを取得する。
        """
        rewrittenComponentAttribute = ""
        usingComponentAttribute = ""
        # まず適用前と適用後でどこを書き換えたのかを見る。
        # appliedTactic に at が含まれていなければゴールのみ、 at が含まれている場合はそのあとの構成要素によって変わる
        if not (" at " in tacticInfo.appliedTactic):
            rewrittenComponentAttribute = "Goal"
        else:
            # at があったときはatの後の部分の構成要素を取得
            components = [item for item in tacticInfo.appliedTactic.split(" at ")[1].split(" ") if item != ""]
            # * が来ているときは全てに対して書き換えが入る
            if "*" in components:
                rewrittenComponentAttribute = "HypAndGoal"
            # ゴールに対する書き換えがあるならば
            elif "⊢" in components:
                rewrittenComponentAttribute = "HypAndGoal"
            # それ以外は何らかの仮定に対する書き換え
            else:
                rewrittenComponentAttribute = "Hyp"
        # 次に何を使って書き換えたのかを見る。
        isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.split(" at ")[0].replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        if isAssumptionUsed and isTheoremUsed:
            usingComponentAttribute = "AssumptionAndTheorem"
        elif isAssumptionUsed:
            usingComponentAttribute = "Assumption"
        else:
            usingComponentAttribute = "Theorem"
        # 最後に属性を By でつないで辞書のキーとする
        return self.__templates__["rw_with_remain_goals"][rewrittenComponentAttribute + "By" + usingComponentAttribute]
        
    # def __proc_let__(
    #         self, 
    #         tacticInfo : TacticInfo,
    #         goalsBeforeHypPremise : List[PremiseInfo],
    #         appliedTacticPremise : List[PremiseInfo]
    #     )->str:
    #     """
    #     タクティク情報から与えられたletの適用の場合に適したテンプレートを取得する。
    #     """
    #     # captured = self.__let_match__.findall(tacticInfo.appliedTactic)
    #     # isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, captured[0][1], goalsBeforeHypPremise)
    #     # if isAssumptionUsed:
    #     #     return self.__templates__["let"]["Assumption"]            
    #     return self.__templates__["let"]["Theorem"]

    def __proc_have__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたapplyの適用の場合に適したテンプレートを取得する。
        """
        m = self.__have_match__.match(tacticInfo.appliedTactic)
        if m != None and m.span()[0] == 0:
            return self.__templates__["have_with_by"]["Default"]
        return self.__templates__["have_without_by"]["Default"]
    def __proc_suffices__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたsufficesの適用の場合に適したテンプレートを取得する。
        """
        m = self.__suffices_by_match__.match(tacticInfo.appliedTactic)
        if m != None and m.span()[0] == 0:
            return self.__templates__["suffices_by"]["Default"]
        return self.__templates__["suffices_from"]["Default"]
    def __proc_exact__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたexactの適用の場合に適したテンプレートを取得する。
        """
        isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        # それぞれで適切なテンプレートを返す
        if isAssumptionUsed and isTheoremUsed:
            return self.__templates__["exact"]["AssumptionAndTheorem"]
        elif isAssumptionUsed:
            return self.__templates__["exact"]["Assumption"]
        else:
            return self.__templates__["exact"]["Theorem"]        
    
    def __proc_ring__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたringの適用の場合に適したテンプレートを取得する。
        """
        # 適用後にゴールが解決されているかどうかを先にチェック
        if "no goals" in tacticInfo.goalsAfter:
            return self.__templates__["ring"]["Proved"]
        if not (" at " in tacticInfo.appliedTactic):
            return self.__templates__["ring"]["Goal"]
        else:
            # at があったときはatの後の部分の構成要素を取得
            components = [item for item in tacticInfo.appliedTactic.split(" at ")[1].split(" ") if item != ""]
            # * が来ているときは全てに対して書き換えが入る
            if "*" in components:
                return self.__templates__["ring"]["HypAndGoal"]
            # ゴールに対する書き換えがあるならば
            if "⊢" in components:
                if len(components) == 1:
                    return self.__templates__["ring"]["Goal"]
                return self.__templates__["ring"]["HypAndGoal"]
            # それ以外は何らかの仮定に対する書き換え
            return self.__templates__["ring"]["Hyp"]
    
    def __proc_obtain__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたobtainの適用の場合に適したテンプレートを取得する。
        """
        m = self.__obtain_split_match__.match(tacticInfo.appliedTactic)
        if m != None and m.span()[0] == 0:
            return self.__templates__["obtain"]["HypSplit"]
        return self.__templates__["obtain"]["CaseAnalysis"]
    
    def __proc_cases__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたcasesの適用の場合に適したテンプレートを取得する。
        """
        # by_cases は P か ¬P の場合分けにしか使えないので場合分けのテンプレートを渡す
        if "by_cases" in tacticInfo.tacticCommand:
            return self.__templates__["cases"]["CaseAnalysis"]
        # case XX.zero と case XX.succのように増えているときはinduction, それ以外はcaseAnalysis
        # case の後の文字列をいったんすべて取得する.
        beforeCases = re.findall(self.__case_analysis_pattern__, tacticInfo.goalsBefore)
        afterCases = re.findall(self.__case_analysis_pattern__, tacticInfo.goalsAfter)
        # afterの各要素からbeforeの文字列を除く
        for item in afterCases:
            for removed in beforeCases:
                item = item.replace(removed, "")
        # 残った要素の最終要素を見る
        remain = []
        for item in afterCases:
            if item == "":
                continue
            remain.append(item.split(".")[-1])
        if "succ" in remain or "zero" in remain:
            return self.__templates__["cases"]["Induction"]
        else:
            return self.__templates__["cases"]["CaseAnalysis"]
    
    def __proc_rcases__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたrcasesの適用の場合に適したテンプレートを取得する。
        """
        m = self.__rcases_hyp_split_match__.match(tacticInfo.appliedTactic)
        if m != None and m.span()[0] == 0:
            return self.__templates__["rcases"]["HypSplit"]
        return self.__templates__["rcases"]["CaseAnalysis"]
    
    def __proc_simp__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたsimpの適用の場合に適したテンプレートを取得する。
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__proc_simp_finish__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
        return self.__proc_simp_rw__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
    
    def __proc_simp_finish__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )->str:
        """
        simpを適用して証明を完了させた場合のその適用方法に対応したテンプレートを取得する。
        """
        # simp [...] にマッチするかどうかをまず確認する
        groups = self.__simp_with_theorem_and_assumption_match__.findall(tacticInfo.appliedTactic)
        if len(groups) == 0:
            return self.__templates__["simp_finish"]["OnlySimp"]
        # マッチする場合はその中身を確認する only にもマッチングするので配列の中のタプルの1番目が中身に対応
        isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, groups[0][1], goalsBeforeHypPremise)
        isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        if isTheoremUsed and isAssumptionUsed:
            return self.__templates__["simp_finish"]["SimpWithAssumptionAndTheorem"]
        elif isTheoremUsed:
            return self.__templates__["simp_finish"]["SimpWithTheorem"]
        else:
            return self.__templates__["simp_finish"]["SimpWithAssumption"]

    def __proc_simp_rw__(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        )-> str:
        """
        simpを適用してゴールもしくは仮定を書き換えた場合のその適用内容に対応したテンプレートを取得する。
        """
        rewrittenComponentAttribute = ""
        usingComponentAttribute = ""
        # まず適用前と適用後でどこを書き換えたのかを見る。
        # appliedTactic に at が含まれていなければゴールのみ、 at が含まれている場合はそのあとの構成要素によって変わる
        if not (" at " in tacticInfo.appliedTactic):
            rewrittenComponentAttribute = "Goal"
        else:
            # at があったときはatの後の部分の構成要素を取得
            components = [item for item in tacticInfo.appliedTactic.split(" at ")[1].split(" ") if item != ""]
            # * が来ているときは全てに対して書き換えが入る
            if "*" in components:
                rewrittenComponentAttribute = "HypAndGoal"
            # ゴールに対する書き換えがあるならば
            elif "⊢" in components:
                rewrittenComponentAttribute = "HypAndGoal"
            # それ以外は何らかの仮定に対する書き換え
            else:
                rewrittenComponentAttribute = "Hyp"
        # 次に何を使って書き換えたのかを見る。
        m = self.__simp_with_theorem_and_assumption_match__.match(tacticInfo.appliedTactic)
        if not (m != None and m.span()[0] == 0):
            usingComponentAttribute = "OnlySimp"
        else:
            isAssumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, m[0][1], goalsBeforeHypPremise)
            isTheoremUsed = self.__is_theorem_used__(appliedTacticPremise)
            if isAssumptionUsed and isTheoremUsed:
                usingComponentAttribute = "AssumptionAndTheorem"
            elif isAssumptionUsed:
                usingComponentAttribute = "Assumption"
            else:
                usingComponentAttribute = "Theorem"
        return self.__templates__["simp_rw"][rewrittenComponentAttribute + "By" + usingComponentAttribute]
        
    def __proc_push_neg__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたpush_negの適用の場合に適したテンプレートを取得する。
        """
        # push_neg at ... の形かどうかで確認する
        if not " at " in tacticInfo.appliedTactic:
            return self.__templates__["push_neg"]["Goal"]
        else:
            # at があったときはatの後の部分の構成要素を取得
            components = [item for item in tacticInfo.appliedTactic.split(" at ")[1].split(" ") if item != ""]
            # * が来ているときは全てに対して書き換えが入る
            if "*" in components:
                return self.__templates__["push_neg"]["HypAndGoal"]
            # ゴールに対する書き換えがあるならば
            if "⊢" in components:
                if len(components) == 1:
                    return self.__templates__["rpush_neging"]["Goal"]
                return self.__templates__["push_neg"]["HypAndGoal"]
            # それ以外は何らかの仮定に対する書き換え
            return self.__templates__["push_neg"]["Hyp"]        
    
    def __proc_norm_num__(
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo]
        )->str:
        """
        タクティク情報から与えられたnorm_numの適用の場合に適したテンプレートを取得する。
        """
        if "no goals" in tacticInfo.goalsAfter:
            return self.__templates__["norm_num_finish"]["Default"]
        # norm_num at ... の形かどうかで確認する
        if not " at " in tacticInfo.appliedTactic:
            return self.__templates__["norm_num_rw"]["Goal"]
        else:
            # at があったときはatの後の部分の構成要素を取得
            components = [item for item in tacticInfo.appliedTactic.split(" at ")[1].split(" ") if item != ""]
            # * が来ているときは全てに対して書き換えが入る
            if "*" in components:
                return self.__templates__["norm_num_rw"]["HypAndGoal"]
            # ゴールに対する書き換えがあるならば
            if "⊢" in components:
                if len(components) == 1:
                    return self.__templates__["norm_num_rw"]["Goal"]
                return self.__templates__["norm_num_rw"]["HypAndGoal"]
            # それ以外は何らかの仮定に対する書き換え
            return self.__templates__["norm_num_rw"]["Hyp"]  
    def __proc_dot__(            
            self, 
            tacticInfo : TacticInfo,
            _ : List[PremiseInfo],
            __ : List[PremiseInfo])->str:
        """
        タクティク情報から与えられたdotの適用の場合に適したテンプレートを取得する。
        """
        # ゴールが複数ある時は判定関数を呼んで状態を保存しておく
        # ゴールが残り一つになった時にどっちの場合分けかがわからなくなってしまう問題があったため、
        # このような形で状態を一時保存しておく。
        if tacticInfo.goalsBefore.count("⊢") > 1:
            self.__case_analysis_state__ = self.__set_case_analysis_state__(tacticInfo)
        return self.__templates__["dot"][self.__case_analysis_state__.name]
    def __proc_refine__(            
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo])->str:
        # ゴールを証明したかどうかで分岐させる
        if "no goals" in tacticInfo.goalsAfter:
            return self.__proc_refine_finish__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
        return self.__proc_refine_rw__(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
    def __proc_refine_finish__(            
        self, 
        tacticInfo : TacticInfo,
        goalsBeforeHypPremise : List[PremiseInfo],
        appliedTacticPremise : List[PremiseInfo])->str:
        theoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        assumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        if theoremUsed and assumptionUsed:
            return self.__templates__["refine_finish"]["WithTheoremsAndAssumptions"]
        elif theoremUsed:
            return self.__templates__["refine_finish"]["WithTheorem"]
        return self.__templates__["refine_finish"]["WithAssumptions"]
    def __proc_refine_rw__(            
        self, 
        tacticInfo : TacticInfo,
        goalsBeforeHypPremise : List[PremiseInfo],
        appliedTacticPremise : List[PremiseInfo])->str:
        # 仮定が増えているかどうかをチェックする
        goalsBefore = re.split("⊢|\n\n", tacticInfo.goalsBefore)
        hypBeforeContexts = "\n".join([goalsBefore[index] for index in range(len(goalsBefore)) if index % 2 == 0])
        hypBeforeContexts = re.sub(self.__case_replace__, "", hypBeforeContexts)
        goalsAfter = re.split("⊢|\n\n", tacticInfo.goalsAfter)
        hypAfterContexts = "\n".join([goalsAfter[index] for index in range(len(goalsAfter)) if index % 2 == 0])
        hypAfterContexts = re.sub(self.__case_replace__, "", hypAfterContexts)
        # もし文字が増えていたならば仮定が増えていると判定する
        isHypothesisExtended = len(hypBeforeContexts) < len(hypAfterContexts)
        # あとはfinishの時と同様にif文判定
        theoremUsed = self.__is_theorem_used__(appliedTacticPremise)
        assumptionUsed = self.__is_assumption_used__(tacticInfo.goalsBefore, tacticInfo.appliedTactic.replace(tacticInfo.tacticCommand, ""), goalsBeforeHypPremise)
        target = "GoalAndHypothesis" if isHypothesisExtended else "Goal"
        byInfo = ""
        if theoremUsed and assumptionUsed:
            byInfo = "TheoremsAndAssumptions"
        elif theoremUsed:
            byInfo = "Theorem"
        elif assumptionUsed:
            byInfo = "Assumptions"
        else:
            byInfo = "Nothing"
        return self.__templates__["refine_rw"][target + "With" + byInfo]
    def get(
            self, 
            tacticInfo : TacticInfo,
            goalsBeforeHypPremise : List[PremiseInfo],
            appliedTacticPremise : List[PremiseInfo]
        ) -> Optional[Tuple[TemplateInfo, AdditionalPremiseRequirement]]:
        """
        タクティク情報から逆形式化に使用するテンプレートを取得する
        """
        tactic = self.__get_correspond_key__(tacticInfo.tacticCommand.lstrip().rstrip())
        if tactic == None:
            return None
        template = ""
        if tactic in self.__tactic_need_branch__.keys():
            template = self.__tactic_need_branch__[tactic](tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
        else:
            template = self.__templates__[tactic]["Default"]
        if template == None:
            raise ValueError(f"テンプレートが取得できませんでした。与えられたタクティク : {tacticInfo.appliedTactic} タクティクコマンド : {tacticInfo.tacticCommand} タクティク : {tactic}")
        print(f"\n template : {template}")
        tokenInfos = getTokenInfo(template)
        additionalFlag = AdditionalPremiseRequirement.none
        tokenDict = {}
        for tokenInfo in tokenInfos:
            tokenDict[tokenInfo.token] = tokenInfo.description
            if tokenInfo.token == "[goalsBefore]":
                if additionalFlag != AdditionalPremiseRequirement.none:
                    additionalFlag |= AdditionalPremiseRequirement.goalBefore
                    continue
                additionalFlag = AdditionalPremiseRequirement.goalBefore
                continue
            if tokenInfo.token == "[goalsAfter]":
                if additionalFlag != AdditionalPremiseRequirement.none:
                    additionalFlag |= AdditionalPremiseRequirement.goalAfter
                    continue
                additionalFlag = AdditionalPremiseRequirement.goalAfter
        return (TemplateInfo(template, tokenDict), additionalFlag)
        
