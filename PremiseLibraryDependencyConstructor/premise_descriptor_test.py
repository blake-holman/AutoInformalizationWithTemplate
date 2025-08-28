from openai import OpenAI
from dotenv import load_dotenv
import os
import tiktoken
from dataclass import PremiseInfo, PremiseLibraryData, PremiseType, Explanatory
from typing import List

class PremiseDiscriptor:
    def __init__(self):
        load_dotenv()
        key = os.getenv('OPENAI_API_KEY')
        self.__client__ = OpenAI(api_key=key)
    def make_description(self, premiseInfo : PremiseInfo, explanatories : List[Explanatory], few_shots : List[PremiseLibraryData]):
        SYSTEM_PROMPT = """
**System Instruction**
You are a “Lean4 Summarizer”—an assistant that reads a single Lean4 definition or theorem (including comments and any attached explanatory text) and produces exactly one clear, concise English sentence that captures its mathematical or logical essence without using any formal Lean syntax, variable names, or code fragments.

---

**User Input**
You will receive:

1. **Item Type:** either `theorem` or `definition`.
2. **Lean4 Code Block:** the full Lean4 statement, including optional in-code comments and optional explanatory notes.
3. **(Optional) Extended Explanation:** any prose clarifying the context or intent of the code.

**Assistant Task**

* Read the code and any comments/explanations.
* Identify the core idea or result being stated.
* Write exactly **one** fluent, self-contained English sentence that explains “what this does” or “what this proves.”
* **Do not** include any Lean keywords (`def`, `theorem`, `∀`, `→`, etc.), notation (`x⁻¹`), or variable names (`G`, `x`, etc.).
* **Do not** quote or restate code.
* Focus solely on the **meaning**.

---

**Output Constraints**

* **Length:** 1 sentence.
* **Style:** Simple, direct, and precise.
* **Content:** Pure natural-language description of the mathematical or logical concept.

---
"""


        USER_PROMPT = """
**Few-Shot Examples**
"""
        for index, item in enumerate(few_shots):
            USER_PROMPT += f"""
Example {index + 1}

Input:

* Item Type: {item.type.value}
* Code: 
```lean
{item.code}
```
* Comment : 
{item.comment}
"""
            if item.type == PremiseType.Definition:
                USER_PROMPT += f"""
* Full Definition
{item.fullDefinition}
"""
            if item.explanatories != []:
                USER_PROMPT += """
* Explanatory
"""
                for ex in item.explanatories:
                    USER_PROMPT += f"""
{ex.name} : {ex.description}
"""
            USER_PROMPT += f"""
* Output:
{item.description}
"""
        kind = PremiseType.Definition.value if premiseInfo.kind == "definition" else PremiseType.Theorem.value
        USER_PROMPT += f"""

# Input

* Type: {kind}
* Code:
```
{premiseInfo.declaration}
```
* Comment
{premiseInfo.description}

"""
        if item.explanatories != []:
                USER_PROMPT += """
* Explanatory
"""
                for ex in item.explanatories:
                    USER_PROMPT += f"""
{ex.name} : {ex.description}
"""
        USER_PROMPT += f"""
* Full Definition
{premiseInfo.fullDefinition}

* Output:
"""
        result = self.__client__.chat.completions.create(
            model="gpt-4o-mini",
            messages=[
                {
                    "role": "system",
                    "content": SYSTEM_PROMPT,
                },
                {
                    "role": "user",
                    "content": USER_PROMPT,
                },
            ],
        )
        encoder = tiktoken.encoding_for_model("gpt-4o-mini")
        tokens = encoder.encode(SYSTEM_PROMPT + USER_PROMPT)
        input_tokens_count = len(tokens)
        output = result.choices[0].message.content
        output_tokens_count = len(encoder.encode(result.choices[0].message.content))
        return (input_tokens_count, output_tokens_count, output)