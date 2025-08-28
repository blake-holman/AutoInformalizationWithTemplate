from DependencyInjection.Container import DependencyContainer
from DomainService.IOpenAIAPICommunicator import IOpenAIAPICommunicator
from DomainService.PromptFactories import TacticInformalizationPromptFactory
from DomainService.CompletionParser import CompletionParser
from typing import Tuple, List
from tqdm import tqdm
from dataclasses import dataclass
from ApplicationService.TreeStructureReconstructor import TacticInfoTree, TacticInfoNode
from DomainModel.ParseDataStructure import PremiseInfo

@dataclass(frozen=True)
class ProgressExportInfo:
    appliedTactic : str
    summary : str

class InformalizationSummerizer():
    """
    非形式化を実行し得られた各文を一つの数学証明文として成形する処理を実装したクラス。
    """
    def __init__(self) -> None:
        dependency = DependencyContainer()
        self.__client__ : IOpenAIAPICommunicator= dependency[IOpenAIAPICommunicator]()
        self.__factory__ = TacticInformalizationPromptFactory()
        self.__parser__ = CompletionParser()
    
    async def summerize_answers(self, statement : str, premiseInfos : List[PremiseInfo], tree : TacticInfoTree) -> Tuple[str, List[ProgressExportInfo]]:
        """
        非形式化を実行し得られた各文を一つの数学証明文として成形する
        """
        results = []
        progress = []
        for subtree in tqdm(tree.nodes):
            # 部分要約を作成
            sub_summerize, sub_progress = await self.__summerize_subtree__(subtree, premiseInfos, progress)
            progress.extend(list(set(sub_progress) - set(progress)))
            results.append(sub_summerize)   
        # 部分要約を集めて全体の要約を作成  
        summerize = await self.__client__.get_response(self.__factory__.make_summerize_prompts(statement, results), 1)
        return (summerize.content, progress)
    async def summerize_answers_without_structure(self, statement : str, answers) -> str:
        summerize = await self.__client__.get_response(self.__factory__.make_summerize_prompts(statement, answers), 1)
        return summerize.content

    async def __summerize_subtree__(self, subtree_root : TacticInfoNode, premises : List[PremiseInfo],progress : List[ProgressExportInfo]) -> Tuple[str, List[ProgressExportInfo]]:
        """
        部分要約を作成する。
        """
        # 子を持つならば部分要約を作成する
        if len(subtree_root.children) != 0:
            results = []
            for child in subtree_root.children:
                result, sub_progress = await self.__summerize_subtree__(child, premises, progress)
                progress.extend(list(set(sub_progress) - set(progress)))
                results.append(result)
            # if subtree_root.info.tacticCommand != 'rw':
            #     # rw 以外は tactic を適用した後のゴールに対して後続のタクティクで操作を行うのでgoalsAfter
            #     statement = await self.__statement_informalizer__.informalize(subtree_root.info.goalsAfter, premises)
            # else :
            #     statement = await self.__statement_informalizer__.informalize(subtree_root.info.goalsBefore, premises)
            summerize = await self.__client__.get_response(self.__factory__.make_summerize_prompts(subtree_root.informalized, results))
            progress.append(ProgressExportInfo(subtree_root.info.appliedTactic, summerize.content))
            return (summerize.content, progress)
        else:
            return (subtree_root.informalized, progress)

        
    

    