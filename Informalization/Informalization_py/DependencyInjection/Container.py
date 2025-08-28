import injector
from typing import Type, TypeVar, Callable 
from Infrastructure import OpenAIAPICommunicator
from Infrastructure.InfoLoader import TacticInfoLoader
from DomainService import IOpenAIAPICommunicator
from DomainService.IInfoLoader import ITacticInfoLoader
from DomainService.FileWriterInterfaces import IFileWriter, IInformalizationDataExporter
from Infrastructure.FileWriters import FileWriter, InformalizationDataExporter
from DomainService.IAbstractSyntaxTreeLoader import IAbstractSyntaxTreeLoader
from DomainService.ITemplateRepository import ITemplateRepository
from Infrastructure.TemplateRepository import TemplateRepository
from Infrastructure.AbstractSyntaxTreeLoader import AbstractSyntaxTreeLoader
from DomainService.IInfoLoader import IPremiseInfoLoader
from Infrastructure.InfoLoader import PremiseInfoLoader
from DomainService.IPremiseExtractor import IPremiseExtractor
from Infrastructure.PremiseExtractor import PremiseExtractor
from DomainService.IFewShotExampleRepository import ITacticFewShotExampleRepository, IStatementFewShotExampleRepository
from Infrastructure.FewShotExampleRepository import TacticFewShotExampleRepository, StatementFewShotExampleRepository

T = TypeVar('T')
class DependencyContainer:
    def __init__(self) -> None:
        self.injector = injector.Injector(self.__class__.configure)
    @classmethod
    def configure(self, binder : injector.Binder):
        binder.bind(interface=IOpenAIAPICommunicator.IOpenAIAPICommunicator, to=OpenAIAPICommunicator.OpenAIAPICommunicator)
        binder.bind(interface=ITacticInfoLoader, to=TacticInfoLoader)
        binder.bind(interface=IFileWriter, to=FileWriter)
        binder.bind(interface=IInformalizationDataExporter, to=InformalizationDataExporter)
        binder.bind(interface=IAbstractSyntaxTreeLoader, to=AbstractSyntaxTreeLoader)
        binder.bind(interface=IPremiseInfoLoader, to=PremiseInfoLoader)
        binder.bind(interface=IPremiseExtractor, to=PremiseExtractor)
        binder.bind(interface=ITacticFewShotExampleRepository, to=TacticFewShotExampleRepository)
        binder.bind(interface=IStatementFewShotExampleRepository, to=StatementFewShotExampleRepository)
        binder.bind(interface=ITemplateRepository, to=TemplateRepository)

    def __getitem__(self, classType : Type[T]) -> Callable:
        return lambda: self.injector.get(classType)


        