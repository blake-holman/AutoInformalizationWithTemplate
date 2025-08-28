from __future__ import annotations
from DomainModel.ParseDataStructure import TacticInfo
from typing import List

class TacticInfoNode:
    def __init__(self, info : TacticInfo, depth : int) -> None:
        self.parent = None
        self.info = info
        self.informalized = ""
        self.depth = depth
        self.children = []
    def add_child(self, child : TacticInfoNode) -> None:
        self.children.append(child)

class TacticInfoTree:
    def __init__(self) -> None:
        self.nodes : List[TacticInfoNode] = []
        self.count : int = 0
    def printTree(self):
        self.__print_nodes__(self.nodes)
    def print_nodes(self, children : List[TacticInfoNode]):
        for child in children:
            indentStr = "  " * (child.depth - 1) + "└" 
            print(indentStr + child.info.appliedTactic[:10] + f"    informalized : {child.informalized[:10]}")
            self.__print_nodes__(child.children)
    def search_tree(self, info : TacticInfo):
        for child in self.nodes:
            if child.info == info:
                return child
            if len(child.children) > 0:
                result = self.__search_tree_rec__(child.children, info)
                if result != None:
                    return result
        return None
    def __search_tree_rec__(self, nodes : List[TacticInfoNode], info : TacticInfo):
        for node in nodes:
            if node.info == info:
                return node
            if len(node.children) > 0:
                result = self.__search_tree_rec__(node.children, info)
                if result != None:
                    return result
        return None


class TacticDependencyTreeHandler():
    def construct_tactic_info_tree(self, tacticInfos : List[TacticInfo], indents : List[int])->TacticInfoTree:
        """
        インデント情報からtacticInfoの依存構造木を構成する
        """
        infoTree = TacticInfoTree()
        last : List[TacticInfoNode] = []
        top = -1
        bottom = -1
        for indent, tacticInfo in zip(indents, tacticInfos):
            node = TacticInfoNode(tacticInfo, indent)
            if top < indent and indent <= bottom + 1:
                index = indent - top
                bottom = indent
                if last[index - 1].children is None:
                    last[index - 1].children = []
                last[index - 1].add_child(node)
                if len(last) <= index:
                    last.append(node)
                else:
                    last[index] = node
                continue
            # infoTree に直接差し込むほう
            infoTree.nodes.append(node)
            if len(last) == 0:
                last.append(node)
            else:
                last[0] = node
            top = indent
            bottom = indent
        return infoTree
    def parse_informalized(self, tree : List[TacticInfoNode], informalized : List[str])->None:
        """
        木構造の各ノードに逆形式化結果を配置する。
        informalizedにはコピーしたデータを与えること！！！
        """
        for node in tree:
            if len(informalized) == 0:
                break
            node.informalized = informalized[0]
            informalized.pop(0)
            if len(node.children) > 0:
                self.parse_informalized(node.children, informalized)
    def remove_specific_tactic_node_children(self, tree : List[TacticInfoNode], tactic : str) -> None:
        """
        木構造中の指定されたタクティクの子ノードをすべて削除する
        """
        for node in tree:
            if tactic in node.info.tacticCommand:
                node.children.clear()
            if len(node.children) > 0:
                self.remove_specific_tactic_node_children(node.children, tactic)
    