from DependencyInjection.Container import DependencyContainer
from DomainService.IInfoLoader import ITacticInfoLoader, IPremiseInfoLoader
import os
import subprocess
from pathlib import Path
from typing import Optional, List
from DomainService.FileWriterInterfaces import IFileWriter, IInformalizationDataExporter
from ApplicationService.TacticInformalizer import TacticInformalizer
from ApplicationService.InformalizationSummerizer import InformalizationSummerizer
from ApplicationService.TreeStructureReconstructor import TacticDependencyTreeHandler
from ApplicationService.TacticInfoSeparator import TacticInfoSeparator
from DomainService.IAbstractSyntaxTreeLoader import IAbstractSyntaxTreeLoader
from DomainService.AbstractSyntaxTreeSearcher import AbstractSyntaxTreeSearcher
from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo, Position
from DomainModel.AbstractSyntaxTree import Node
from tqdm import tqdm
from datetime import datetime, timezone, timedelta
from DomainService.DomainExtractor import DomainExtractor
from injector import Injector
from ApplicationService.StatementInformalizer import StatementInformalizer
from injector import inject
from Infrastructure.PremiseLibrary import PremiseLibrary
from ApplicationService.PremiseDiscriptor import PremiseDescriptor
import json

class InformalizationService():
    """
    非形式化 / 要約までの一連の処理を各クラスの処理を呼び出すことで実行するクラス。
    """
    @inject
    def __init__(self) -> None:
        dependency = DependencyContainer()
        self.__tactic_info_loader__ : ITacticInfoLoader = dependency[ITacticInfoLoader]()
        self.__premise_info_loader__ : IPremiseInfoLoader = dependency[IPremiseInfoLoader]()
        self.__informalize_result_writer__ : IInformalizationDataExporter = dependency[IInformalizationDataExporter]()
        self.__file_writer__ : IFileWriter = dependency[IFileWriter]()
        self.__tactic_informalizer__ = TacticInformalizer()
        self.__informalization_summerizer__ = InformalizationSummerizer()
        self.__dependency_tree_handler__ = TacticDependencyTreeHandler()
        self.__ast_loader__ : IAbstractSyntaxTreeLoader = dependency[IAbstractSyntaxTreeLoader]()
        self.__ast_seacher__ = AbstractSyntaxTreeSearcher()
        self.__tactic_info_separator__ = TacticInfoSeparator()
        self.__domain_extractor__ = DomainExtractor()
        self.__statement_informalizer__ = StatementInformalizer()
        self.__library__ = PremiseLibrary()
        inj = Injector()
        self.__premise_descriptor__ = inj.get(PremiseDescriptor)

    async def informalize(self, path : Path) -> None:
        """
        与えられたleanファイル(のパス)内の tactic を使用した定理に対して非形式化を行い、数学証明として出力する。
        """
        self.__validate_file_path__(path)
        filePath = self.__make_path_to_tactic_info__(path)
        if not filePath.exists():
            self.__make_info__(path)
        # 各種情報の出力
        tacticInfos = self.__tactic_info_loader__.load(filePath)
        premiseInfos = self.__premise_info_loader__.load(self.__make_path_to_premise_info__(path))
        ast = self.__ast_loader__.load(self.__make_path_to_ast_info__(path))
        domainInfo = self.__domain_extractor__.extract_domain_roots(path)
        # タクティク情報から定理の証明に使われているタクティクでないものを除く
        self.__preprocess_tactic_info__(tacticInfos, ast)
        # ファイル内の定義をすべてライブラリに抽出する
        await self.__premise_descriptor__.proc_definition_descriptions(path, premiseInfos)
        # 命題ごとにタクティク情報の要素を分割する。
        separated = self.__tactic_info_separator__.separate_tactic_infos(ast, tacticInfos)
        # 各定理のtacticInfoに対して非形式化 - 要約処理を実行する。
        for tacticData in tqdm(separated, "Informalize Progress"):
            theorem_name = self.__ast_seacher__.get_theorem_name(tacticData[0], ast)
            indents = self.__ast_seacher__.search_tactic_indents(tacticData, ast)
            dependency_tree = self.__dependency_tree_handler__.construct_tactic_info_tree(tacticData, indents)
            (appliedTactics, answers, eval_dicts, premise_dicts, evaluation_data_list) = await self.__tactic_informalizer__.informalize(domainInfo, tacticData, premiseInfos, dependency_tree, path)
            # (appliedTactics, answers, eval_dicts, premise_dicts, evaluation_data_list) = await self.__tactic_informalizer__.informalize_without_premise_library(domainInfo, tacticData, premiseInfos, dependency_tree, path)
            # 未実装のタクティク等によってanswersが空になることがある。そのため、その時は以降の処理をスキップする
            if len(answers) == 0:
                continue
            # 木からrwの子を全て除去する
            self.__dependency_tree_handler__.remove_specific_tactic_node_children(dependency_tree.nodes, "rw")
            # 出力をパースする
            self.__dependency_tree_handler__.parse_informalized(dependency_tree.nodes, answers.copy())
            # 命題の説明文を得る このときライブラリに逆形式化中の定理の情報も保存される。
            statement = await self.__get_statement__(path, theorem_name, premiseInfos)  
            (summary, progress) = await self.__informalization_summerizer__.summerize_answers(statement, premiseInfos, dependency_tree)
            # summary = await self.__informalization_summerizer__.summerize_answers_without_structure(statement, answers.copy())
            
            self.__informalize_result_writer__.save_data(filePath, theorem_name, appliedTactics, answers, summary)
            fileName = filePath.parent.name
            now = datetime.now(timezone(timedelta(hours=+9))).strftime('%Y_%b_%d_%H_%M_%S')
            dir = Path(__file__).resolve().parent.parent.parent
            store_path = dir.joinpath("ExportData",fileName, theorem_name, now, "Progress")
            progress_txt = "" 
            for sub in progress :
                progress_txt += f"[applied Tactic]\n{sub.appliedTactic}\n\n[answer]\n{sub.summary}\n"
            self.__file_writer__.save_file(store_path, "progress.txt", progress_txt)
            self.__file_writer__.save_dict(store_path, "evals.json", eval_dicts)
            self.__file_writer__.save_dict(store_path, "premise.json", premise_dicts)
            self.__file_writer__.save_file(store_path, "evaluation_data.json", json.dumps(evaluation_data_list, ensure_ascii=False, indent = 2))
        self.__library__.write_to_file()

    async def __get_statement__(self, definition_path : Path, theorem_name : str, premiseInfos : List[PremiseInfo]) -> str:
        # 対象のpremiseを探す
        target_premise = None
        def_path = definition_path.absolute().as_posix()
        for premiseInfo in premiseInfos:
            target_path = Path(premiseInfo.definitionPath).absolute()
            if target_path.as_posix() == def_path and theorem_name in premiseInfo.fullName:
                target_premise = premiseInfo
                break
        if target_premise == None:
            referencePremise = None
            for premiseInfo in premiseInfos:
                target_path = Path(premiseInfo.definitionPath).absolute()
                if target_path.as_posix() == def_path:
                    referencePremise = premiseInfo
                    break
            target_premise = self.__make_premise_info_of_statement__(definition_path, theorem_name, referencePremise)
        return await self.__premise_descriptor__.proc_description(target_premise, premiseInfos, definition_path)
    def __make_premise_info_of_statement__(self, definition_path : Path, theorem_name : str, reference : PremiseInfo) -> PremiseInfo:
        # defitinitionStartPos.line と declaration だけは埋める
        theorem_line = 0
        declaration = ""
        isLineSet = False
        with open(definition_path, "r", encoding="utf-8") as f:
            codes = f.readlines()
        for line_no, code in enumerate(codes, start=1):
            if theorem_name in code and not isLineSet:
                theorem_line = line_no
                isLineSet = True
            if ":=" in code and isLineSet:
                declaration += code.split(":=")[0]
                break
            if isLineSet:
                declaration += code
        declaration = declaration.replace("theorem", "").replace("lemma", "").lstrip().rstrip()
        return PremiseInfo(
            fullName=theorem_name,
            definitionStartPos= Position(
                line=theorem_line,
                column=0
            ),
            definitionEndPos=Position(
                line= 0,
                column=0
            ),
            moduleName= reference.moduleName if reference != None else "",
            definitionPath=reference.definitionPath if reference != None else "",
            startPos=0,
            endPos=0,
            kind = "theorem",
            declaration=declaration,
            description=None
        )
    def __validate_file_path__(self, path: Path) -> Path:
        """
        引数に渡されたパスが存在する .lean ファイルを指しているかをチェックする。
        """
        ext = os.path.splitext(path)
        if ext[1] != ".lean" or not path.exists:
            raise RuntimeError("Given file path doesn't point to .lean file.")

    def __make_path_to_tactic_info__(self, path : Path) -> Path:
        """
        .leanファイルのパスから tacticInfo.jsonまでのファイルパスを作成する
        """
        dirPath = self.__make_path_to_info_directory__(path)
        if dirPath == None:
            raise RuntimeError(f'illegal path was given. path : {path}')
        return dirPath.joinpath("tacticInfo.json")
    def __make_path_to_ast_info__(self, path) -> Path:
        """
        .leanファイルのパスから abstractSyntaxTreeInfo.jsonまでのファイルパスを作成する
        """
        dirPath = self.__make_path_to_info_directory__(path)
        if dirPath == None:
            raise RuntimeError(f'illegal path was given. path : {path}')
        return dirPath.joinpath("abstractSyntaxTreeInfo.json")
    def __make_path_to_premise_info__(self, path) -> Path:
        """ 
        .leanファイルのパスから premiseInfo.jsonまでのファイルパスを作成する
        """
        dirPath = self.__make_path_to_info_directory__(path)
        if dirPath == None:
            raise RuntimeError(f'illegal path was given. path : {path}')
        return dirPath.joinpath("premiseInfo.json")
    def __make_path_to_info_directory__(self, path : Path) -> Optional[Path]:
        fileName = path.name
        for i, dir in enumerate(path.parents):
            # ディレクトリをさかのぼってExportInfosに行きついたらそこからjsonが入ったディレクトリまでのパスを構成する
            # ExportInfos/Export/(.leanファイルまでのディレクトリパス)/(ファイル名)/XXX.json に出力されている
            if dir.name == "ExportInfos":
                tacticInfoDir = Path.joinpath(dir, "Export")
                # ファイルパスのディレクトリで ExportInfos までのものを取得する
                # C:/XXX/YYY/ZZZ/ExportInfos/HOGE/FUGA/Basic.leanの場合は、
                #dirs = ["C:/XXX/YYY/ZZZ/ExportInfos/HOGE/FUGA", C:/XXX/YYY/ZZZ/ExportInfos/HOGE"] となる
                dirs = path.parents[:i]
                # 逆からたどってディレクトリ名を結合することでパスを再構成する
                # 上の例だと C:/XXX/YYY/ZZZ/ExportInfos/Export + HOGE + FUGA となる
                for d in reversed(dirs):
                    tacticInfoDir = tacticInfoDir.joinpath(d.name)
                tacticInfoDir = tacticInfoDir.joinpath(fileName)
                return tacticInfoDir
        return None
    def __make_info__(self, filePath : Path):
        """
        .leanのデータ抽出コマンドをたたいて各種情報を抽出する
        """
        p = Path(os.getcwd())
        # lean カーネルがあるフォルダまで一度移動する
        os.chdir(p.joinpath("ExportInfos"))
        subprocess.run(['lake', 'env', 'lean', '--run', 'DataExtraction.lean', filePath.relative_to(os.getcwd()).as_posix()], stdout=subprocess.PIPE)
        # python の実行ディレクトリに戻る
        os.chdir(os.path.dirname(os.path.abspath(__file__)))
    def __preprocess_tactic_info__(self, infos : List[TacticInfo], ast : List[Node])->None:
        """
        tacticInfo に対して前処理を行う。
        """
        #
        remove_targets = []
        for index in range(len(infos)):
            if not self.__ast_seacher__.is_proof_tactic_info(infos[index], ast):
                remove_targets.append(infos[index])
        for target in remove_targets:
            infos.remove(target)
        
        # dot タクティクの出力バグに対する暫定的対応
        # dotタクティクのgoalsAfterの値をその次のgoalsBeforeの値で上書きすることで正しい出力にする。
        for index, info in enumerate(infos):
            if info.tacticCommand in [" . ", " · "]:
                info.goalsAfter = infos[index + 1].goalsBefore
                