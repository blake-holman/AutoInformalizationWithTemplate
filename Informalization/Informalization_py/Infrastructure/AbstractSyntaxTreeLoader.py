from DomainModel.AbstractSyntaxTree import Node, NodeType, AtomNode, IdentNode, NodeInfo, NodeBase
from DomainService.IAbstractSyntaxTreeLoader import IAbstractSyntaxTreeLoader
from pathlib import Path
from typing import List, Dict
import json

class AbstractSyntaxTreeLoader(IAbstractSyntaxTreeLoader):
    """
    jsonの形で保存されている抽象木データをNodeBaseのリストの形にパースする処理を実装するクラス
    """
    def load(self, path : Path) -> List[NodeBase]:
        """
        抽象木の情報を持つjsonデータを読み込み、データ型に情報をパースする
        """
        path = path.resolve()
        if (not path.exists()) :
            raise RuntimeError(f"given path isn't exists : {path}")
        nodes = []
        with open(path.resolve().as_posix(), 'r',encoding="UTF-8") as f:
            loaded_json = json.load(f)
            for data_str in loaded_json:
                nodes.append(self.__parse__(data_str))
        return nodes
    def __parse__(self, json : Dict) ->NodeBase:
        match next(iter(json)):
            case "node":
                kind = json["node"]["kind"]
                info = json["node"]["info"]
                args = json["node"]["args"]
                arg_list = []
                for arg in args:
                    arg_list.append(self.__parse__(arg))
                return Node(NodeType.Node, kind if kind != "null" else None, info if info != "none" else None, arg_list)
            case "atom":
                val = json["atom"]["val"]
                return AtomNode(
                    NodeType.Atom,
                    val,
                    self.__parse_node_info__(json["atom"]["info"])
                )
            case "ident":
                val = json['ident']['val']
                rawVal = json['ident']['rawVal']
                preresolved = json['ident']['preresolved']
                return IdentNode(
                    NodeType.Ident,
                    val,
                    rawVal,
                    preresolved,
                    self.__parse_node_info__(json['ident']["info"]) 
                )
            case _:
                raise KeyError(f"Invalid key was given in AbstractSyntaxTreeLoader : {next(iter(json))}")

    def __parse_node_info__(self, info : Dict) -> NodeInfo:
        """
        AtomノードとIdentノードに出現するinfoキーに付随する情報をデータ構造にパースする
        """
        trailing = ""
        leading = ""
        pos = 0
        endPos = 0
        if "original" in info:
            trailing = info["original"]["trailing"]
            leading = info["original"]["leading"]
            pos = info["original"]["pos"]
            endPos = info["original"]["endPos"]
        elif "synthetic" in info:
            trailing = info["synthetic"]["trailing"]
            leading = info["synthetic"]["leading"]
            pos = info["synthetic"]["pos"]
            endPos = info["synthetic"]["endPos"]
        else:
            raise RuntimeError("unknown key is set in atom info.")
        return  NodeInfo(
            trailing if trailing != "" else None,
            pos,
            leading if leading != "" else None,
            endPos
        )