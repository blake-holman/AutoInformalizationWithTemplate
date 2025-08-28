from typing import List
import re
from DomainModel.ParseDataStructure import PremiseInfo
from DependencyInjection.Container import DependencyContainer
from DomainService.IOpenAIAPICommunicator import IOpenAIAPICommunicator
from DomainService.PromptFactories import StatementInformalizationPromptyFactory
from DomainService.IPremiseExtractor import IPremiseExtractor
from DomainService.IFewShotExampleRepository import IStatementFewShotExampleRepository, StatementInfo
from pathlib import Path

class StatementInformalizer():
    """
    TacticInfoに含まれている情報をLLMに与え非形式化する処理を実装したクラス。
    """
    def __init__(self) -> None:
        dependency = DependencyContainer()
        self.__client__ : IOpenAIAPICommunicator = dependency[IOpenAIAPICommunicator]()
        self.__factory__ = StatementInformalizationPromptyFactory()
        self.__premise_extractor__ : IPremiseExtractor = dependency[IPremiseExtractor]()
        self.__few_shot_repository__ : IStatementFewShotExampleRepository = dependency[IStatementFewShotExampleRepository]()

    async def informalize(self, statement : str, premiseInfos : List[PremiseInfo], definitionPath : Path)-> str :
        """
        対象となる命題の逆形式化を行う。
        """
        # 関係のある定義を抽出する
        correspond_definitions = self.extract_correspond_premise(statement, premiseInfos)
        extracted_premises = [f"{definition.fullName} : {self.__premise_extractor__.extract_description(definition, definitionPath).source}" for definition in correspond_definitions]
        info = StatementInfo(
            statement=statement,
            definitions=extracted_premises
        )
        few_shots = self.__few_shot_repository__.get(statement)
        prompts = self.__factory__.make_informalize_prompt(few_shots, info)
        result = await self.__client__.get_response(prompts)
        return result.content
    def extract_correspond_premise(self, statement : str, premiseInfos : List[PremiseInfo])-> List[PremiseInfo]:
        """
        命題で使用されている定義を抽出する
        """
        result = {}
        for premiseInfo in premiseInfos:
            # 定義名は前後に空白がある(独立した状態である)場合でないとキャプチャしない
            target = re.escape(premiseInfo.fullName.split('.')[-1])
            if premiseInfo.kind == 'definition':
                # 定義名は前後に空白もしくは特定の記号があるときだけマッチングする
                regex = r"(?<![^\[\s,.])"+rf"{target}"+r"(?![^\]\s,])"
                try:
                    captured = re.findall(regex, statement)
                except re.PatternError as e:
                    print(regex)
                    raise e
                if len(captured) > 0 and not (premiseInfo.fullName in result.keys()) and premiseInfo.kind in ["definition", "constructor", "theorem"]:
                    result[premiseInfo.fullName] = premiseInfo
        return list(result.values())