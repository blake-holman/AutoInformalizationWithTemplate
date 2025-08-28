import re
from typing import Tuple, Optional
from openai.types.chat import ChatCompletionMessage

class CompletionParser():
    """
    OpenAI APIから返されたデータから思考データと解答データを抽出する処理を実装するクラス。
    """
    def __init__(self) -> None:
        self.normalThoughtCapture = re.compile('<thought>(.*)</thought>')
        self.normalAnswerCapture = re.compile('<answer>(.*)</answer>')

    def extract_data_from_completion(self, completion : ChatCompletionMessage) -> Tuple[str, str]:
        content = completion.content
        if content == None:
            return None
        content = content.replace('\n', '')
        content = content.strip()
        thought_result = self.parse_thought(content)
        answer_result = self.parse_answer(content)
        if answer_result == None:
            # なぜか </answer>だけ出力されないことがあるため、answer_resultが空の時は</answer>を末尾に追加して再度パースする
            content += "</answer>"
            answer_result = self.parse_answer(content)
        return (thought_result, answer_result)
    
    def parse_thought(self, data : str) -> Optional[str]:
        thought_result = None
        thought = self.normalThoughtCapture.findall(data)
        if thought != None :
            try :
                thought_result = thought[0].strip()
            except IndexError:
                thought_result = None
        return thought_result
    def parse_answer(self, data : str) -> Optional[str]:
        answer_result = None
        answer = self.normalAnswerCapture.findall(data)
        if answer != None :
            try :
                answer_result = answer[0].strip()
            except IndexError:
                answer_result = None
        return answer_result