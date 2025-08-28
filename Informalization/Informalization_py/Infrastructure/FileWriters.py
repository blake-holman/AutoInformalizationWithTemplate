from DomainService.FileWriterInterfaces import IFileWriter, IInformalizationDataExporter
from typing import List, Dict
from pathlib import Path
from DomainModel.ParseDataStructure import TacticInfo
from datetime import datetime, timezone, timedelta
import os
import json

class FileWriter(IFileWriter):
    def save_file(self, directory_path : Path, file_name : str, data : str):
        if data == None:
            return
        if not os.path.exists(directory_path):
            os.makedirs(directory_path)
        path = directory_path.joinpath(file_name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(data)
    def save_dict(self, directory_path : Path, file_name : str, data : Dict):
        if data == None:
            return
        if not os.path.exists(directory_path):
            os.makedirs(directory_path)
        path = directory_path.joinpath(file_name)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent = 2)

class InformalizationDataExporter(IInformalizationDataExporter):
    def __init__(self) -> None:
        self.__file_writer__ = FileWriter()
    def save_data(self, filePath : Path, theorem_name : str, applied_tactics : List[str], answers : List[str], summary : str) -> None:
        fileName = filePath.parent.name
        now = datetime.now(timezone(timedelta(hours=+9))).strftime('%Y_%b_%d_%H_%M_%S')
        dir = Path(__file__).resolve().parent.parent.parent
        store_path = dir.joinpath("ExportData",fileName, theorem_name, now) 
        informalize = ""
        for tactic, answer in zip(applied_tactics, answers):
            informalize += f"[appliedTactic]\n{tactic}\n[answer]\n{answer}\n"
        self.__file_writer__.save_file(store_path, 'informalize.txt', informalize)
        self.__file_writer__.save_file(store_path, 'summary.txt', summary)