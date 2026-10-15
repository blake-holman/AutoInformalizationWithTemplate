import tqdm
from typing import List, Optional, Tuple, Dict
import re
from pathlib import Path
from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo
from DependencyInjection.Container import DependencyContainer
from DomainService.IOpenAIAPICommunicator import IOpenAIAPICommunicator
from DomainService.PromptFactories import TacticInformalizationPromptFactoryWithTemplates, TacticInformalizationPromptFactory
from DomainService.CompletionParser import CompletionParser
from DomainService.IPremiseExtractor import IPremiseExtractor
from DomainService.IFewShotExampleRepository import ITacticFewShotExampleRepository, TacticExampleState, TacticExampleInfo
from DomainService.DomainExtractor import DomainExtractor
from DomainModel.DomainInfo import DomainInfo
from ApplicationService.TreeStructureReconstructor import TacticInfoTree, TacticInfoNode
from DomainService.ITemplateRepository import ITemplateRepository, AdditionalPremiseRequirement
from enum import Enum
import Levenshtein
import asyncio
from ApplicationService.CorrespondencePremiseExtractor import CorrespondencePremiseExtractor

class DomainLevel(Enum):
    SameSourceFile = 1
    SameDomain = 0.75
    Unrelated = 0.5

class TacticInformalizer():
    """
    TacticInfoに含まれている情報をLLMに与え非形式化する処理を実装したクラス。
    """
    def __init__(self) -> None:
        dependency = DependencyContainer()
        self.__client__ : IOpenAIAPICommunicator = dependency[IOpenAIAPICommunicator]()
        self.correspondenceExtractor = CorrespondencePremiseExtractor()
        self.__factory__ = TacticInformalizationPromptFactoryWithTemplates()
        self.__factory_without_templates__ = TacticInformalizationPromptFactory()
        self.__parser__ = CompletionParser()
        self.__premise_extractor__ : IPremiseExtractor = dependency[IPremiseExtractor]()
        self.__few_shot_repository__ : ITacticFewShotExampleRepository = dependency[ITacticFewShotExampleRepository]()
        self.__domain_extractor__ : DomainExtractor = DomainExtractor()
        self.__template_repository__ : ITemplateRepository = dependency[ITemplateRepository]()
        self.__have_preprocess_capture__ = re.compile(r"(have.*?:.*?):=[\\n|\s]*?by")
        self.__suffices_by_preprocess_capture__ = re.compile(r"(suffices.*?:?.*?)by", re.DOTALL)
        self.__suffices_from_preprocess_capture__ = re.compile(r"suffices.*?:?.*?from", re.DOTALL)
        self.__preprocess_tactic_dict__ = {
            'have' : self.__preprocess_have__,
            'suffices' : self.__preprocess_suffices__
        }
        self.__rewrite_tactic_list__ = [
            "rw",
            "erw",
            "nth_rw",
            "rw_mod_cast"
        ]
        self.rewrite_element_command = "rw_element"
        self.__ignore_premise_tactics__ = ["·", ".", "calc"]

    async def informalize(self, domainInfo : DomainInfo, tacticInfos : List[TacticInfo], premiseInfos : List[PremiseInfo], dependencyTree : TacticInfoTree, definitionPath : Path)-> Tuple[List[str], List[str], Dict, Dict[str, List[str]], List[Dict]] :
        """
        TacticInfoに含まれている情報からそのtacticの操作内容を説明する文章を生成する。
        """
        appliedTactics = []
        answers = []
        evaluation_data_list = []
        eval_dicts = {}
        premise_dicts = {}
        index = 0
        previousIndex = 0
        with tqdm.tqdm(total=len(tacticInfos)) as bar:
            while index < len(tacticInfos):
                previousIndex = index
                tacticInfo = tacticInfos[index]
                # ログ出力用にデータを取る
                appliedTactics.append(tacticInfo.appliedTactic)
                tqdm.tqdm.write(f"text {index} : {tacticInfo.appliedTactic} started.")
                # rw は別関数で処理する
                if tacticInfo.tacticCommand in self.__rewrite_tactic_list__:
                    # rw_element 部分を抽出
                    targetInfos = self.__extract_rw_elements__(dependencyTree, tacticInfo, tacticInfos, previousIndex)
                    # 逆形式化を行う
                    (informalized, eval_dict, premises_rewrite, evaluation_data) = await self.__informalize_rewrite__(domainInfo, targetInfos, premiseInfos, definitionPath)
                    # 各種出力用データに結果を追加
                    answers.append(informalized)
                    if tacticInfo.appliedTactic in eval_dict.keys():
                        eval_dicts[tacticInfo.appliedTactic].append(eval_dict)
                    else:
                        eval_dicts[tacticInfo.appliedTactic] = [eval_dict]
                    premise_dicts[tacticInfo.appliedTactic] = premises_rewrite
                    evaluation_data_list.append(evaluation_data)
                    # インデックスを更新
                    index += len(targetInfos) - 1
                else:
                    # データを取ってくる
                    examples = self.__few_shot_repository__.get(tacticInfo)
                    if examples.state == TacticExampleState.Skip:
                        answers.append("")
                    elif examples.state == TacticExampleState.NotExists:
                        # raise RuntimeError(f"Examples aren't implemented! : {tacticInfo.tacticCommand}")
                        raise RuntimeError(f"Unsupported tactic: {tacticInfo.tacticCommand}")
                    # 前処理が必要なコマンドへの対応
                    else:
                        # premiseを取得する 場合分けの · など、premiseが返って不必要になるtacticはこの工程を無視する
                        premises = []
                        if not (tacticInfo.tacticCommand.lstrip().rstrip() in self.__ignore_premise_tactics__):
                            premises = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
                        # premise を抽出する
                        premise_source = set()
                        for premise in premises:
                            extracted = self.__premise_extractor__.extract_description(premise, definitionPath)
                            if extracted != None:
                                premise_source.add(f"{premise.fullName} : {extracted.source}")
                        premise_list = list(premise_source)
                        # 逆形式化結果を出力用データに追加
                        (informalized, evaluation_data) = await self.get_informalize_result(tacticInfo, premiseInfos, examples, premise_list, definitionPath)
                        # (informalized, evaluation_data) =  await self.get_informalize_result_without_templates(tacticInfo, examples, premise_list)
                        answers.append(informalized)
                        premise_dicts[tacticInfo.appliedTactic] = premise_list
                        evaluation_data_list.append(evaluation_data)
                index += 1
                bar.update(index - previousIndex)
        return (appliedTactics, answers, eval_dicts, premise_dicts, evaluation_data_list)

    async def informalize_without_premise_library(self, domainInfo : DomainInfo, tacticInfos : List[TacticInfo], premiseInfos : List[PremiseInfo], dependencyTree : TacticInfoTree, definitionPath : Path)-> Tuple[List[str], List[str], Dict, Dict[str, List[str]], List[Dict]] :
        """
        TacticInfoに含まれている情報からそのtacticの操作内容を説明する文章を生成する。 w/o Premiseライブラリ
        """
        appliedTactics = []
        answers = []
        evaluation_data_list = []
        eval_dicts = {}
        premise_dicts = {}
        index = 0
        previousIndex = 0
        with tqdm.tqdm(total=len(tacticInfos)) as bar:
            while index < len(tacticInfos):
                previousIndex = index
                tacticInfo = tacticInfos[index]
                # ログ出力用にデータを取る
                appliedTactics.append(tacticInfo.appliedTactic)
                tqdm.tqdm.write(f"text {index} : {tacticInfo.appliedTactic} started.")
                # rw は別関数で処理する
                if tacticInfo.tacticCommand in self.__rewrite_tactic_list__:
                    # rw_element 部分を抽出
                    targetInfos = self.__extract_rw_elements__(dependencyTree, tacticInfo, tacticInfos, previousIndex)
                    # 逆形式化を行う
                    (informalized, eval_dict, premises_rewrite, evaluation_data) = await self.__informalize_rewrite_without_premise_library__(domainInfo, targetInfos, premiseInfos, definitionPath)
                    # 各種出力用データに結果を追加
                    answers.append(informalized)
                    if tacticInfo.appliedTactic in eval_dict.keys():
                        eval_dicts[tacticInfo.appliedTactic].append(eval_dict)
                    else:
                        eval_dicts[tacticInfo.appliedTactic] = [eval_dict]
                    premise_dicts[tacticInfo.appliedTactic] = premises_rewrite
                    evaluation_data_list.append(evaluation_data)
                    # インデックスを更新
                    index += len(targetInfos) - 1
                else:
                    # データを取ってくる
                    examples = self.__few_shot_repository__.get(tacticInfo)
                    if examples.state == TacticExampleState.Skip:
                        answers.append("")
                    elif examples.state == TacticExampleState.NotExists:
                        # raise RuntimeError(f"Examples aren't implemented! : {tacticInfo.tacticCommand}")
                        raise RuntimeError(f"Unsupported tactic: {tacticInfo.tacticCommand}")
                    # 前処理が必要なコマンドへの対応
                    else:
                        # premiseを取得する 場合分けの · など、premiseが返って不必要になるtacticはこの工程を無視する
                        premises = []
                        if not (tacticInfo.tacticCommand.lstrip().rstrip() in self.__ignore_premise_tactics__):
                            premises = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
                        # premise を抽出する
                        premise_source = set()
                        for premise in premises:
                            # Premise Library を ablation するので 定義をそのまま与える方法に変更
                            extracted = self.__premise_extractor__.extract_premise_data(premise)
                            if extracted != None:
                                premise_source.add(extracted.source)
                        premise_list = list(premise_source)
                        # 逆形式化結果を出力用データに追加
                        # (informalized, evaluation_data) = await self.get_informalize_result_without_premise_library(tacticInfo, premiseInfos, examples, premise_list, definitionPath)
                        (informalized, evaluation_data) = await self.get_informalize_result_without_templates(tacticInfo, examples, premise_list)
                        answers.append(informalized)
                        evaluation_data_list.append(evaluation_data)
                        premise_dicts[tacticInfo.appliedTactic] = premise_list
                index += 1
                bar.update(index - previousIndex)
        return (appliedTactics, answers, eval_dicts, premise_dicts, evaluation_data_list)

    async def get_informalize_result(
            self, 
            tacticInfo : TacticInfo, 
            premiseInfos : List[PremiseInfo],
            examples : TacticExampleInfo, 
            premises : List[str],
            definitionPath : Path
            ) -> Tuple[Optional[str], Dict]:
            """
            与えられた情報を使って証明ステップの逆形式化を行う

            premiseInfos : すべてのpremiseの情報をまとめたリスト
            premises : 逆形式化に使用するpremiseのLean上の形式定義文字列
            """
            # テンプレートを取得する。
            # テンプレート取得に当たり必要な情報を用意する
            (goalsBeforeHypPremise, goalsBeforeGoalPremise, goalsAfterHypPremise, goalsAfterGoalPremise) = self.correspondenceExtractor.extract_correspond_premise_in_goals(tacticInfo, premiseInfos)
            appliedTacticPremise = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
            # 情報を全て渡して判断させる。
            templateInfo = self.__template_repository__.get(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
            if templateInfo == None:
                return None
            # トークンに応じてpremiseを追加する。
            premise_source = set()
            (templateInfo, additionalPremiseRequirement) = templateInfo
            if additionalPremiseRequirement & AdditionalPremiseRequirement.goalBefore:
                premise_source = set()
                for premise in goalsBeforeGoalPremise:
                    extracted = self.__premise_extractor__.extract_description(premise, definitionPath)
                    if extracted != None:
                        premise_source.add(f"{premise.fullName} : {extracted.source}")             
            if additionalPremiseRequirement & AdditionalPremiseRequirement.goalAfter:  
                for premise in goalsAfterGoalPremise:
                    extracted = self.__premise_extractor__.extract_description(premise, definitionPath)
                    if extracted != None:
                        premise_source.add(f"{premise.fullName} : {extracted.source}")
            premises.extend(list(premise_source))
            prompt = self.__factory__.make_informalize_prompt(
            tacticInfo,
            examples,
            templateInfo,
            premises
                )
            answer_result = await self.__client__.get_response(
                prompt, 
                0.4
            )
            evaluation_data = {
                "AppliedTactic" : tacticInfo.appliedTactic,
                "GoalsBefore" : tacticInfo.goalsBefore,
                "GoalsAfter" : tacticInfo.goalsAfter,
                "GivenPremises" : premises,
                "Template" : templateInfo.template,
                "TokenInfos" : templateInfo.tokenInfos,
                "Result" : answer_result.content
            }
            return (answer_result.content, evaluation_data)
    async def get_informalize_result_without_premise_library(
            self, 
            tacticInfo : TacticInfo, 
            premiseInfos : List[PremiseInfo],
            examples : TacticExampleInfo, 
            premises : List[str],
            definitionPath : Path
            ) -> Tuple[Optional[str], Dict]:
            """
            与えられた情報を使って証明ステップの逆形式化を行う

            premiseInfos : すべてのpremiseの情報をまとめたリスト
            premises : 逆形式化に使用するpremiseのLean上の形式定義文字列
            """
            # テンプレートを取得する。
            # テンプレート取得に当たり必要な情報を用意する
            (goalsBeforeHypPremise, goalsBeforeGoalPremise, goalsAfterHypPremise, goalsAfterGoalPremise) = self.correspondenceExtractor.extract_correspond_premise_in_goals(tacticInfo, premiseInfos)
            appliedTacticPremise = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
            # 情報を全て渡して判断させる。
            templateInfo = self.__template_repository__.get(tacticInfo, goalsBeforeHypPremise, appliedTacticPremise)
            if templateInfo == None:
                return None
            # トークンに応じてpremiseを追加する。
            premise_source = set()
            (templateInfo, additionalPremiseRequirement) = templateInfo
            if additionalPremiseRequirement & AdditionalPremiseRequirement.goalBefore:
                premise_source = set()
                for premise in goalsBeforeGoalPremise:
                    extracted = self.__premise_extractor__.extract_premise_data(premise)
                    if extracted != None:
                        premise_source.add(f"{premise.fullName} : {extracted.source}")             
            if additionalPremiseRequirement & AdditionalPremiseRequirement.goalAfter:  
                for premise in goalsAfterGoalPremise:
                    extracted = self.__premise_extractor__.extract_premise_data(premise)
                    if extracted != None:
                        premise_source.add(f"{premise.fullName} : {extracted.source}")
            premises.extend(list(premise_source))
            prompt = self.__factory__.make_informalize_prompt(
            tacticInfo,
            examples,
            templateInfo,
            premises
                )
            answer_result = await self.__client__.get_response(
                prompt, 
                0.4
            )
            evaluation_data = {
                "AppliedTactic" : tacticInfo.appliedTactic,
                "GoalsBefore" : tacticInfo.goalsBefore,
                "GoalsAfter" : tacticInfo.goalsAfter,
                "GivenPremises" : premises,
                "Template" : templateInfo.template,
                "TokenInfos" : templateInfo.tokenInfos,
                "Result" : answer_result.content
            }
            return (answer_result.content, evaluation_data)
    async def get_informalize_result_without_templates(self, tacticInfo : TacticInfo, examples : TacticExampleInfo, premises : List[str]) -> Tuple[Optional[str], Dict]:
            """
            与えられた情報を使って証明ステップの逆形式化を行う w/o テンプレート
            """
            prompt = self.__factory_without_templates__.make_informalize_prompt_new(
            tacticInfo,
            examples,
            premises
                )
            answer_result = await self.__client__.get_response(
                prompt, 
                0.4
            )
            evaluation_data = {
                "AppliedTactic" : tacticInfo.appliedTactic,
                "GoalsBefore" : tacticInfo.goalsBefore,
                "GoalsAfter" : tacticInfo.goalsAfter,
                "GivenPremises" : premises,
                "Result" : answer_result.content
            }
            return (answer_result.content, evaluation_data)

    def __extract_rw_elements__(self, dependencyTree : TacticInfoTree, targetTacticInfo : TacticInfo, tacticInfos : List[TacticInfo], currentIndex : int)-> List[TacticInfo]:
        """
        rwの子にあるrw_elementをすべて取得する。
        rw_elementのtacticInfo配列が返される。
        """
        # 対応するノードを取得
        node = dependencyTree.search_tree(targetTacticInfo)
        if node == None:
            raise RuntimeError("木構造探索エラー")
        # ノードの子の最後尾のtacticInfoを取得
        tail = self.__find_rewrite_tail__(node)
        targetInfos = [targetTacticInfo]
        #最後尾のInfoと一致するものをtacticInfosから探す
        for info in tacticInfos[currentIndex + 1:]:
            if info == tail:
                targetInfos.append(info)
                break
            targetInfos.append(info)
        return targetInfos

    def __preprocess_have__(self, info : TacticInfo):
        m = self.__have_preprocess_capture__.search(info.appliedTactic)
        if m != None:
            info.appliedTactic = m.group(1)
        return info

    def __preprocess_suffices__(self, info : TacticInfo):
        m_by = self.__suffices_by_preprocess_capture__.search(info.appliedTactic)
        m_from = self.__suffices_from_preprocess_capture__.search(info.appliedTactic)
        if m_by != None and m_from != None:
            # 両方マッチングしているときは短い方を確認する。
            # suffices A by ... (show B from ...) のような場合への対応
            byInfo = m_by.group(1)
            fromInfo = m_from.group(1)
            # suffices by の構文だった場合はbyの手前までを渡す
            if len(byInfo) < len(fromInfo):
                info.appliedTactic = byInfo
        # suffices by の構文だった場合はbyの手前までを渡す
        elif m_by != None:
            info.appliedTactic = m_by.group(1)
        return info

    async def __informalize_rewrite__(self, domainInfo : DomainInfo, tacticInfos : List[TacticInfo], premiseInfos : List[PremiseInfo], definitionPath : Path) -> Tuple[str, Dict, List[str], Dict]:
        """
        rw関連のtacticの逆形式化に関する特別なロジック
        """
        assert(tacticInfos[0].tacticCommand in self.__rewrite_tactic_list__)
        # 各 rw_elementに対して重要度を計算する
        evaluation_dict : Dict[str, float] = {}
        premise_dict : Dict [str, List[PremiseInfo]]= {}
        for tacticInfo in tacticInfos[1:]:
            extracted_premises = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
            premises = []
            for premise in extracted_premises:
                if premise.kind in ["theorem", "definition"]:
                    premises.append(premise)
            if len(premises) == 0:
                continue
            # PremiseInfoは辞書のキーにできないので別途保存する
            premise_dict[premises[0].fullName] = premises
            # ドメインボーナス
            domain_bonus = 0
            for premise in premises:
                domain_level = self.__check_domain__(domainInfo, premises[0]).value
                if domain_level > domain_bonus:
                    domain_bonus = domain_level
            evaluation_dict[premises[0].fullName] = domain_bonus     
            # rw_elementの編集量をボーナスとして加算する
            # 正規化する
            evaluation_dict[premises[0].fullName] *= Levenshtein.distance(tacticInfo.goalsBefore, tacticInfo.goalsAfter) / (max(len(tacticInfo.goalsBefore), len(tacticInfo.goalsAfter)) * 1.00)
        # 逆形式化のpremiseとして与えるものを選択する
        eval_sorted = dict(sorted(evaluation_dict.items(), key=lambda x:x[1], reverse=True))
        #とりあえず上位2個を与える 要検討
        targets = list(dict.fromkeys(list(eval_sorted.keys())))[:2]
        given_premises : List[PremiseInfo] = []
        for target in targets:
            given_premises.extend(premise_dict[target])
        premise_source = set()
        for premise in given_premises:
            extracted = self.__premise_extractor__.extract_description(premise, definitionPath)
            if extracted != None:
                premise_source.add(f"{premise.fullName} : {extracted.source}")
        premise_list = list(premise_source)
        (informalized, evaluation_data) = await self.get_informalize_result(tacticInfos[0], premiseInfos, self.__few_shot_repository__.get(tacticInfos[0]), premise_list, definitionPath)
        # (informalized, evaluation_data) = await self.get_informalize_result_without_templates(tacticInfos[0], self.__few_shot_repository__.get(tacticInfos[0]), premise_list)
        return (informalized, eval_sorted, premise_list, evaluation_data)

    async def __informalize_rewrite_without_premise_library__(self, domainInfo : DomainInfo, tacticInfos : List[TacticInfo], premiseInfos : List[PremiseInfo], definitionPath : Path) -> Tuple[str, Dict, List[str], Dict]:
        """
        rw関連のtacticの逆形式化に関する特別なロジック w/o Premise ライブラリ
        """
        assert(tacticInfos[0].tacticCommand in self.__rewrite_tactic_list__)
        # 各 rw_elementに対して重要度を計算する
        evaluation_dict : Dict[str, float] = {}
        premise_dict : Dict [str, List[PremiseInfo]]= {}
        for tacticInfo in tacticInfos[1:]:
            extracted_premises = self.correspondenceExtractor.extract_correspond_premise_in_applied_tactic(tacticInfo, premiseInfos)
            premises = []
            for premise in extracted_premises:
                if premise.kind in ["theorem", "definition"]:
                    premises.append(premise)
            if len(premises) == 0:
                continue
            # PremiseInfoは辞書のキーにできないので別途保存する
            premise_dict[premises[0].fullName] = premises
            # ドメインボーナス
            domain_bonus = 0
            for premise in premises:
                domain_level = self.__check_domain__(domainInfo, premises[0]).value
                if domain_level > domain_bonus:
                    domain_bonus = domain_level
            evaluation_dict[premises[0].fullName] = domain_bonus     
            # rw_elementの編集量をボーナスとして加算する
            # 正規化する
            evaluation_dict[premises[0].fullName] *= Levenshtein.distance(tacticInfo.goalsBefore, tacticInfo.goalsAfter) / (max(len(tacticInfo.goalsBefore), len(tacticInfo.goalsAfter)) * 1.00)
        # 逆形式化のpremiseとして与えるものを選択する
        eval_sorted = dict(sorted(evaluation_dict.items(), key=lambda x:x[1], reverse=True))
        #とりあえず上位2個を与える 要検討
        targets = list(dict.fromkeys(list(eval_sorted.keys())))[:2]
        given_premises : List[PremiseInfo] = []
        for target in targets:
            given_premises.extend(premise_dict[target])
        premise_source = set()
        for premise in given_premises:
            extracted = self.__premise_extractor__.extract_premise_data(premise)
            if extracted != None:
                premise_source.add(extracted.source)
        premise_list = list(premise_source)
        # (informalized, evaluation_data) = await self.get_informalize_result_without_premise_library(tacticInfos[0], premiseInfos, self.__few_shot_repository__.get(tacticInfos[0]), premise_list, definitionPath)
        (informalized, evaluation_data) = await self.get_informalize_result_without_templates(tacticInfos[0], self.__few_shot_repository__.get(tacticInfos[0]), premise_list)
        return (informalized, eval_sorted, premise_list, evaluation_data)

    
    def __check_domain__(self, domainInfo : DomainInfo, premise : PremiseInfo) -> DomainLevel:
        extractedDomainInfo = self.__domain_extractor__.extract_domain_roots(Path(premise.definitionPath)) 
        if extractedDomainInfo.rootDomain != domainInfo.rootDomain:
            return DomainLevel.Unrelated
        count = 0
        for target, extracted in zip(domainInfo.subDomains, extractedDomainInfo.subDomains):
            if target != extracted:
                break
            count += 1
        if count == 0:
            return DomainLevel.Unrelated
        elif count == max(len(domainInfo.subDomains), len(extractedDomainInfo.subDomains)):
            return DomainLevel.SameSourceFile
        else:
            return DomainLevel.SameDomain
    def __find_rewrite_tail__(self, node : TacticInfoNode) -> TacticInfo:
        tail = node
        while len(tail.children) != 0:
            tail = tail.children[-1]
        return tail.info

    async def informalize_mock(self, domainInfo : DomainInfo, tacticInfos : List[TacticInfo], premiseInfos : List[PremiseInfo], dependencyTree : TacticInfoTree)-> List[str] :
        """
        TacticInfoに含まれている情報からそのtacticの操作内容を説明する文章を生成する。
        """
        answers = []
        index = 0
        previousIndex = 0
        with tqdm.tqdm(total=len(tacticInfos)) as bar:
            while index < len(tacticInfos):
                previousIndex = index
                tacticInfo = tacticInfos[index]
                tqdm.tqdm.write(f"text {index} : {tacticInfo.appliedTactic} started.")
                # rw は別関数で処理する
                if tacticInfo.tacticCommand in self.__rewrite_tactic_list__:
                    # rw 部分を抽出
                    # 対応するノードを取得
                    node = dependencyTree.search_tree(tacticInfo)
                    if node == None:
                        raise RuntimeError("木構造探索エラー")
                    # ノードの子の最後尾のtacticInfoを取得
                    tail = self.__find_rewrite_tail__(node)
                    targetInfos = [tacticInfo]
                    #最後尾のInfoと一致するものをtacticInfosから探す
                    for info in tacticInfos[index + 1:]:
                        if info == tail:
                            targetInfos.append(info)
                            break
                        targetInfos.append(info)
                    answers.append(tacticInfo.appliedTactic)
                    index += len(targetInfos) - 1
                else:
                    # データを取ってくる
                    examples = self.__few_shot_repository__.get(tacticInfo)
                    if examples.state == TacticExampleState.Skip:
                        answers.append("")
                    elif examples.state == TacticExampleState.NotExists:
                        # raise RuntimeError(f"Examples aren't implemented! : {tacticInfo.tacticCommand}")
                        raise RuntimeError(f"Unsupported tactic: {tacticInfo.tacticCommand}")
                    # 前処理が必要なコマンドへの対応
                    else:
                        if tacticInfo.tacticCommand in self.__preprocess_tactic_dict__.keys():
                            tacticInfo = self.__preprocess_tactic_dict__[tacticInfo.tacticCommand](tacticInfo)
                        # premiseを取得する 場合分けの · など、premiseが返って不必要になるtacticはこの工程を無視する
                        premises = []
                        if not (tacticInfo.tacticCommand.lstrip().rstrip() in self.__ignore_premise_tactics__):
                            premises = self.__extract_correspond_premise_in_applied_tactic__(tacticInfo, premiseInfos)
                        premise_source = set()
                        for premise in premises:
                            extracted = self.__premise_extractor__.extract_description(premise)
                            if extracted != None:
                                premise_source.add(f"{premise.fullName} : {extracted.source}")
                        premise_list = list(premise_source)
                        answers.append(tacticInfo.appliedTactic)
                index += 1
                bar.update(index - previousIndex)
                await asyncio.sleep(0.01)
        return answers