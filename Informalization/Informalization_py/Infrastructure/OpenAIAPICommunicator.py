from dotenv import load_dotenv
from openai import AsyncOpenAI
from openai.types.chat import ChatCompletionMessageParam, ChatCompletionMessage
import os
from typing import Iterable
import DomainService.IOpenAIAPICommunicator as interface
    

class OpenAIAPICommunicator(interface.IOpenAIAPICommunicator) :
    """
    OpenAI の API との通信処理を行うクラス。
    """
    def __init__(self) :
        """
        コンストラクタ。モデルの初期設定を行う。
        """
        load_dotenv()
        key = os.getenv('OPENAI_API_KEY')
        if key == None :
            raise EnvironmentError("OpenAI key doesn't find in Enviroment!!")
        self.client = AsyncOpenAI(api_key=key)
        self.model = "gpt-4.1-mini"
    
    async def get_response(self, messages : Iterable[ChatCompletionMessageParam], temperature = 1.0) -> ChatCompletionMessage :
        completion = await self.client.chat.completions.create(
            model = self.model,
            messages = messages,
            temperature=temperature
        )
        return completion.choices[0].message
    