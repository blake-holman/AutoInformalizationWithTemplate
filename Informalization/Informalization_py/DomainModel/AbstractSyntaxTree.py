from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, List
from enum import Enum

class NodeType(Enum):
    """
    ノードの種類を表す列挙型
    """
    Node = "Node"
    Atom = "Atom"
    Ident = "Ident"
    @classmethod
    def value_of(cls, target_value):
        for e in NodeType:
            if e.value == target_value:
                return e

@dataclass
class NodeBase:
    """
    ノードの基底クラス ノードの型のみをメンバ変数に持つ。
    """
    nodeType : NodeType

@dataclass
class Node(NodeBase):
    """
    { node : ... } で書かれる情報を格納するクラス
    """
    kind : Optional[str]
    info : Optional[str]
    args : List[NodeBase]

@dataclass
class AtomNode(NodeBase):
    """
    { atom : ...} で書かれる情報を格納するクラス
    original / synthetic の中身をNodeInfoに入れて直接持つようにしている
    """
    val : str
    info : NodeInfo

@dataclass
class IdentNode(NodeBase):
    """
    { ident : ...} で書かれる情報を格納するクラス
    original / synthetic の中身をNodeInfoに入れて直接持つようにしている
    """
    val : str
    rawVal : str
    preresolved : List
    info : NodeInfo

@dataclass
class NodeInfo:
    """
    ノードの情報（位置情報等）が格納されるクラス
    """
    trailing : Optional[str]
    pos : int
    leading : Optional[str]
    endPos : int
