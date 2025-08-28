from DomainModel.AbstractSyntaxTree import Node, NodeBase, NodeInfo, NodeType, AtomNode, IdentNode
from DomainModel.ParseDataStructure import TacticInfo
from typing import List, Optional, Tuple


class AbstractSyntaxTreeSearcher:
    """
    抽象木を探索して情報を抽出する機能を定義 / 提供するクラス
    """
    def search_tactic_indents(self, tacticInfos : List[TacticInfo], nodeInfos : List[NodeBase])->List[int]:
        """
        各種 tactic command の深さを抽象木から抽出する。
        引数に渡された tactic command 配列に対応する深さを表す整数値が格納された配列が返される
        """
        root = self.__search_tactic_root__(tacticInfos[0], nodeInfos)
        indents = []
        for tacticInfo in tacticInfos:
            result = self.search_pos(tacticInfo.startPos, [root])
            if result == None:
                raise RuntimeError("Given tactic doesn't exists under root node!!")
            node = root
            indent_count = 0
            # インデックスリストの最初の値は [root] を渡してるので必ず 0 
            # よって1番目以降だけ確認する
            for index in result[1][1:]:
                node = node.args[index]
                # tacticSeq1Indentedが来た時はインデントが下がった扱い
                # rwRuleSeqもインデントが下がった扱いにする（要約の関係）
                if node.nodeType == NodeType.Node and (node.kind == "Lean.Parser.Tactic.tacticSeq1Indented" or node.kind == "Lean.Parser.Tactic.rwRuleSeq"):
                    indent_count += 1
            indents.append(indent_count)
        return indents
    def __search_tactic_root__(self, headTacticInfo : TacticInfo, nodeInfos : List[NodeBase])-> NodeBase:
        """
        与えられた tactic command 配列のルートノードを探す
        """
        result = self.search_pos(headTacticInfo.startPos, nodeInfos)
        if result == None:
            raise RuntimeError("tacticInfo and nodeInfos don't match!!")
        root = None
        for i, index in enumerate(result[1]):
            if i == 0:
                root = nodeInfos[index]
            else:
                root = root.args[index]
            # := by ~~~ を表すnodeをrootとする
            if root.nodeType == NodeType.Node and root.kind == "Lean.Parser.Term.byTactic":
                return root
        raise RuntimeError("Given nodeInfos are illegal!!")

    def search_pos(self, pos : int, nodeInfos : List[NodeBase], parent : NodeBase = None, index_list : List[int] = []) -> Optional[Tuple[NodeBase, List[int]]]:
        """
        与えられた pos の情報を子に持つNodeを探す
        """
        for index, nodeInfo in enumerate(nodeInfos):
            if nodeInfo.nodeType != NodeType.Node:
                # Node ノードじゃないときは pos 情報を持つので比較を行う
                if nodeInfo.info.pos == pos:
                    return (parent, index_list + [index])
                continue
            # Node ノードのときは子要素に対して探索を行う
            data = self.search_pos(pos, nodeInfo.args, nodeInfo, index_list + [index])
            if data != None:
                return data
        # 見つからなかったときはNoneを返す
        return None

    def search_theorem_endPos(self, head : TacticInfo, ast : List[NodeBase]) -> int:
        """
        引数に渡されたtacticが使われている定理証明の最終位置(endPos)を取得する
        """
        tail_atom = self.search_tail_atom_node(head, ast)
        tail_ident = self.search_tail_ident_node(head, ast)
        if tail_atom == None and tail_ident == None:
            raise RuntimeError(f"illegal tree structure : {head.appliedTactic}")
        if tail_atom == None:
            return tail_ident.info.endPos
        if tail_ident == None:
            return tail_atom.info.endPos
        tail =  tail_ident if tail_atom.info.endPos < tail_ident.info.endPos else tail_atom
        assert tail.nodeType == NodeType.Atom or tail.nodeType == NodeType.Ident
        return tail.info.endPos

    def search_tail_atom_node(self, head : TacticInfo, ast : List[NodeBase])-> NodeBase:
        """
        最も木の最後尾に近いatomノードを返す
        """
        node = self.__search_tactic_root__(head, ast)
        assert node.nodeType == NodeType.Node
        return self.__search_tail_node__(node.args, NodeType.Atom)

    def search_tail_ident_node(self, head : TacticInfo, ast : List[NodeBase])-> NodeBase:
        """
        最も木の最後尾に近いidentノードを返す
        """
        node = self.__search_tactic_root__(head, ast)
        assert node.nodeType == NodeType.Node
        return self.__search_tail_node__(node.args, NodeType.Ident)

    def __search_tail_node__(self, nodes : List[NodeBase], targetType : NodeType)-> NodeBase:
        """
        最も木の最後尾に近い指定された型のNodeを返す
        ただしNodeは対応していない
        あくまでident と atom 用であることに注意
        """
        for node in reversed(nodes):
            if node.nodeType == NodeType.Node:
                if node.args == []:
                    continue
                result = self.__search_tail_node__(node.args, targetType)
                if result != None:
                    return result
            if node.nodeType == targetType:
                return node

    def is_proof_tactic_info(self, tacticInfo : TacticInfo, ast : List[NodeBase])->bool:
        """
        与えられたtacticInfoがtheoremの抽象木の子にあるかどうかを確認する。
        """
        pos_result = self.search_pos(tacticInfo.startPos, ast)
        if pos_result == None:
            raise RuntimeError("tacticInfo and nodeInfos don't match!!")
        theorem_target = ast[pos_result[1][0]].args[pos_result[1][1]]
        lemma_target = ast[pos_result[1][0]]
        return (theorem_target.nodeType == NodeType.Node and theorem_target.kind == "Lean.Parser.Command.theorem") or (lemma_target.nodeType == NodeType.Node and lemma_target.kind == "lemma") 
    def get_theorem_name(self, tacticInfo : TacticInfo, ast : List[NodeBase])->str:
        """
        定理名を取得する
        """
        pos_result = self.search_pos(tacticInfo.startPos, ast)
        if pos_result == None:
            raise RuntimeError("tacticInfo and nodeInfos don't match!!")
        target = ast[pos_result[1][0]].args[pos_result[1][1]].args[1]
        if target.nodeType == NodeType.Node and target.kind == "Lean.Parser.Command.declId":
            return target.args[0].val
        raise RuntimeError("Given nodeInfos are illegal!!")