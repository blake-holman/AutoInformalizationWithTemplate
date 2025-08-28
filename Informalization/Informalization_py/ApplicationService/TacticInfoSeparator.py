from DomainModel.AbstractSyntaxTree import NodeBase
from DomainModel.ParseDataStructure import TacticInfo
from typing import List, Tuple
from DomainService.AbstractSyntaxTreeSearcher import AbstractSyntaxTreeSearcher

class TacticInfoSeparator:
    def __init__(self):
        self.__ast_seacher__ = AbstractSyntaxTreeSearcher()
    def separate_tactic_infos(self, ast: List[NodeBase], tacticInfos : List[TacticInfo])->List[List[TacticInfo]]:
        """
        ファイル内に複数のtheoremが含まれていた場合に、tacticInfoの列を各定理ごとに分割する。
        """
        remain = tacticInfos
        infos = []
        while remain != []:
            endPos = self.__ast_seacher__.search_theorem_endPos(remain[0], ast)
            correspond_tactic, index = self.__search_endPos_correspond_tacticInfo__(remain, endPos)
            # if correspond_tactic.tacticCommand in ['rw', 'rwa', 'rw_mod_cast']:
            #     # rw のときだけrw_elemの最終要素のendPos の値が endPos - 最後尾から文字までの文字数の値になる
            #     # 例 : tacticCommand : rw, appliedTactic : rw [Nat.add_assoc], endPos : 100 のとき、
            #     # tacticCommand : rw_elem, appliedTactic : rw [ Nat.add_assoc, ], endPos : 99 (100 - ']') になる
            #     # 例2 : tacticCommand : rw, appliedTactic : rw [Nat.add_assoc ], endPos : 100 のとき、
            #     # tacticCommand : rw_elem, appliedTactic : rw [ Nat.add_assoc, ], endPos : 98 (100 - ' ]') になる
            #     # identノードのtrailing に末尾の空白が記録されているのでそれを見て最後尾から文字までの個数を決める
            #     tail_ident = self.__ast_seacher__.search_tail_ident_node(remain[0], ast)
            #     trail_length = len(tail_ident.info.trailing) if tail_ident.info.trailing != None else 0
            #     endPos = endPos - (trail_length + 1)
            #     correspond_tactic, index = self.__search_endPos_correspond_tacticInfo__(remain, endPos)
            # elif correspond_tactic.tacticCommand == "<;>":
            #     # induction l <;> [something] のような場合、 something の部分のtacticがなぜか抽出されない
            #     # そのため、induction l の部分までの情報を抜き出す必要がある。
            #     index += 1
            if index + 1 < len(remain):
                infos.append(remain[: index + 1])
                remain = remain[index + 1:]
                continue
            infos.append(remain)
            remain = []
            break
        return infos
            
    def __search_endPos_correspond_tacticInfo__(self, tacticInfos : List[TacticInfo], endPos : int)->Tuple[TacticInfo, int]:
        """
        引数に渡されたendPosを持つtacticInfoを探してそのインデックスと一緒に返す
        """
        for index, tacticInfo in enumerate(reversed(tacticInfos)):
            # all_goals norm_num とかが最後に来ると 同じendPosを持つtacticInfoが複数生成される
            # なので後ろから探す
            if tacticInfo.endPos <= endPos:
                return (tacticInfo, len(tacticInfos) - index - 1)
        raise RuntimeError(f"correspond tactic info doesn't exists! endPos : {endPos}")
    
            