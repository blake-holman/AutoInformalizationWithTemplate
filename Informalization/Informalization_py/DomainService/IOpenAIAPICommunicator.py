from openai.types.chat import ChatCompletionMessageParam, ChatCompletionMessage
import abc
from typing import Iterable

class IOpenAIAPICommunicator(metaclass=abc.ABCMeta) :
    """
    OpenAI の API との通信処理を外部から呼び出す際に使用する関数の宣言が定義されたインターフェース。
    """
    @abc.abstractmethod
    async def get_response(self, messages : Iterable[ChatCompletionMessageParam], temperature = 1.0) -> ChatCompletionMessage:
        """OpenAI の API と通信を行い、その結果を取得する。通信は await で待機できる。
        
        ## Args:

            messages (Iterable[AsyncOpenAI.ChatCompletionMessageParam])
            APIに対して渡すプロンプトの情報を持つ構造体の配列。

        ## Returns:

            AsyncOpenAI.ChatCompletion
            APIからの返答含む通信結果が格納された構造体
        """
        raise NotImplementedError()
    
