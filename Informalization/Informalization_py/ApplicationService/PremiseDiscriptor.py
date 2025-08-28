from pathlib import Path
from typing import List
from DomainModel.ParseDataStructure import PremiseInfo
from injector import singleton, inject
from Infrastructure.PremiseLibrary import PremiseLibrary
from Infrastructure.PremiseExtractor import PremiseExtractor
import re
from DomainService.PromptFactories import PremiseInformalizationPromptFactory
from DomainService.IOpenAIAPICommunicator import IOpenAIAPICommunicator
from DependencyInjection.Container import DependencyContainer
from DomainModel.PremiseLibraryDataStructure import Explanatory
from tqdm import tqdm

class PremiseDescriptor:
    @inject
    def __init__(self, extractor : PremiseExtractor):
        self.__library__ = PremiseLibrary()
        self.__premise_extractor__ = extractor
        self.__prompt_factory__ = PremiseInformalizationPromptFactory()
        container = DependencyContainer()
        self.__communicator__ : IOpenAIAPICommunicator = container[IOpenAIAPICommunicator]()

    async def proc_description(self, target : PremiseInfo, premises : List[PremiseInfo], definitionPath : Path) -> str:
        # すでにあるものは処理しない
        if self.__library__.check_existence(target):
            return
        # 定義抽出
        premiseSource = self.__premise_extractor__.extract_premise_data(target)
        # 依存定義を抽出
        if premiseSource == None:
            dependencies = []
        else:
            dependencies = self.extract_correspond_premise(premiseSource.source, target, premises)
        # 循環参照の場合に対応するため、premise自身は依存Premiseから除く
        removed = []
        for d in dependencies:
            if d.fullName in target.fullName:
                removed.append(d)
        for r in removed:
            dependencies.remove(r)
        # 依存定義の説明文を取得
        explanatories = []
        for dependency in dependencies:
                dependency_data = self.__premise_extractor__.extract_description(dependency, definitionPath)
                if not dependency_data == None:
                    explanatories.append(Explanatory(dependency.fullName, dependency_data.source))
        # 説明文を生成
        fewShots = self.__library__.get_fewshots(target, 3)
        prompt = self.__prompt_factory__.make_description(target, explanatories, fewShots)
        description = (await self.__communicator__.get_response(prompt)).content
        if description == None:
            return
        if premiseSource == None:
            self.__library__.save_data(target, "", explanatories, description)
        else:
            self.__library__.save_data(target, premiseSource.source, explanatories, description)
        return description

    async def proc_definition_descriptions(self, definitionPath : Path, premises : List[PremiseInfo]) -> None:
        """
        definitionPathで与えられているLeanファイルで定義されているDefinitionを抽出し、ライブラリを拡張する
        """
        def_path = definitionPath.absolute().as_posix()
        isModuleLoadChecked = False
        for premise in tqdm(premises):
            premise_path = Path(premise.definitionPath).absolute().as_posix()
            # 該当leanファイル内で定義されているものを生成対象とする
            if def_path in premise_path:
                # すでに生成済みのpremise情報があるかどうかをチェックし、あれば読み込んでおく
                # 生成の重複防止
                if not isModuleLoadChecked:
                    isModuleLoadChecked = True
                    if self.__library__.check_data_existence(premise):
                        self.__library__.load_data(premise.moduleName)
                if premise.kind == "definition":
                    _ = await self.proc_description(premise, premises, definitionPath)
        self.__library__.write_to_file()

    def extract_correspond_premise(self, targetSentence : str, targetPremise: PremiseInfo, premiseInfos : List[PremiseInfo]) -> List[PremiseInfo]:
        """
        指定文字列内に含まれているpremiseの情報を取得する。
        """
        result = {}
        for premiseInfo in premiseInfos:
            target = re.escape(premiseInfo.fullName.split('.')[-1])
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