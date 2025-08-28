from enum import Enum

class EvaluationType(Enum):
    """
    出力結果を評価方法を指定するために使用する列挙型
    """
    HUMAN = "Human"
    AI = "AI"
    NONE = "None"
    @classmethod
    def value_of(cls, target_value):
        for e in EvaluationType:
            if e.value == target_value:
                return e