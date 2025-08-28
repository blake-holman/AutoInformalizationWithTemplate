from DomainModel.ParseDataStructure import TacticInfo, PremiseInfo
from typing import Iterable, List
from openai.types.chat import ChatCompletionUserMessageParam, ChatCompletionSystemMessageParam, ChatCompletionMessageParam
from DomainService.IFewShotExampleRepository import TacticExampleInfo, StatementInfo, StatementFewShotExample
from DomainService.ITemplateRepository import TemplateInfo
from DomainModel.PremiseLibraryDataStructure import PremiseLibraryData, PremiseType, Explanatory

class TacticInformalizationPromptFactory():
    """
    非形式化に用いるプロンプトを生成するための処理を実装する
    """

    def make_informalize_prompt_new(self, info : TacticInfo,  few_shots : TacticExampleInfo, premises : List[str] = None) -> Iterable[ChatCompletionMessageParam]:

        
        SYSTEM_PROMPT = """
You are an expert in Lean4 and formal mathematics. 
Transform the given Lean4 tactic into a clear and concise natural language explanation, accurately conveying the operation performed as a step in a mathematical proof without using the format of the formal language.

Ensure that any predicates from the formal language are not included in the explanation.

# Steps

1. **Understand the Applied Tactic**:
- Analyze the `Applied Tactic` to comprehend its function within the proof.
	 - If a tactic involves using one or more theorems or definitions, read the theorems listed under `Using Definitions and Theorems` and ensure you understand their content.

2. **Examine Hypotheses and Goals**:
- Compare `Hypotheses And Goals Before Tactic Application` with `Hypotheses And Goals After Tactic Application` to understand what changes in objectives occurred.
    - Hypotheses and goals are separated with the symbol '⊢'.
 
3. **Formulate the Explanation**:
- Describe what action the tactic took, referring only to what was altered based on the changes observed in the hypotheses and goals.
- Avoid directly referencing predicates from the formal language.
    - When referring to variables, be sure to explicitly use these variable names in the output.
        - (ex) Set \\( A \\) is Empty.
    - **Do not** include the names of theorems or definitions in formal languages, or variables used as aliases to specific expressions (like h : x = 2 * y) in the output. Instead, explain the content in natural language.

# Output Format

- Provide a natural language explanation summarizing the operation of the tactic and the immediate effects on the hypotheses and goals.
  - Provide all necessary information for the explanation in precise and detailed terms.
            """
        USER_PROMPT = """
# Examples
"""
        for i, example in enumerate(few_shots.examples):
            USER_PROMPT += f"""
### Example {i + 1}

**Input Information**:
- Applied Tactic: {example.appliedTactic}
- Hypotheses And Goals Before Tactic Application: {example.goalsBefore}
- Hypotheses And Goals After Tactic Application: {example.goalsAfter}

**Using Definitions and Theorems**

"""
            for premise in example.defintionsAndTheorems:
                USER_PROMPT += f"- {premise}\n"
            USER_PROMPT += f"""
**Output**: 
{example.output}
""" 
        USER_PROMPT += f"""
# Notes

- Always determine what assumptions or definitions are brought into effect or altered.
- Make sure explanations are precise to maintain clarity and avoid unnecessary details.
- Do not include expressions written in Lean's formal language in the output.  
  - In formal proofs, casts such as from natural numbers to integers are represented by \\( \\uparrow \\). Therefore, ensure that the output does not contain \\( \\uparrow \\) representing a cast.
- If you use explanations or citations to output formulas, please use TeX formatting for citations if the formulas are not complex, or use explanations written in natural language if the formulas are complex.

Using the example above as a reference, please explain the following input in natural language as one operation in a mathematical proof.

**Input Information**:
- Applied Tactic: {info.appliedTactic}
- Hypotheses And Goals Before Tactic Application: {info.goalsBefore}
- Hypotheses And Goals After Tactic Application: {info.goalsAfter}
"""
        USER_PROMPT += """
**Using Definitions and Theorems**
"""
        for premise in premises:
            USER_PROMPT += f"- {premise}\n"
        USER_PROMPT += """
**Output**:
"""
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts

    def make_summerize_prompts(self, goal : str, info : List[str]) -> Iterable[ChatCompletionMessageParam] : 
        SYSTEM_PROMPT = """
From now on, act like you're a mathematician and good at writing mathematical proofs.

Summarize the sequence of steps used to prove the given proposition into a coherent and natural narrative suitable for a mathematical proof.

# Steps

1. **Understand the essence of the mathematical proposition**: Comprehend the given proposition and identify the goal of the subsequent steps.  
2. **Understand the content of the proof steps**: Grasp the operations performed to prove the proposition.  
3. **Shape the steps into a coherent draft**: Combine the sequence of steps provided, adding appropriate conjunctions to form a natural and cohesive draft of the proof.
- When writing a proof, start with a sentence that clearly states the proposition you are going to prove (e.g., "We will show that...") and then continue with the proof in that form.

# Output Format

- A concise paragraph summarizing the mathematical proof based on provided sentences.
- Ensure it is well-structured and flows logically from premise to conclusion.

# Notes

- Ensure that all statements in the proof are directly supported by the information in the input.
- Be sure to include explanations of critical elements in constructing the proof, such as the introduction of variables and the use of important theorems.
- Avoid introducing new operations or assumptions not present in the input sentences.
"""
# 4. **Eliminate redundant explanations**: Remove any redundant parts from your draft.
# 5. **Omit mathematically trivial content**: Exclude mathematical expressions that are easy to understand without having to write them out, and write a proof that only introduces variables and writes important operations.
    # Please leave the following expressions:
    # - Introducing new variables and functions or definitions that are defined in the proof
    # - Propositions required for the proof and their concise proofs
    # The following expressions should be considered self-evident and should be removed:
    # - Equation transformation that is obvious without explicit explanation
        exp = ""
        for i, explanation in enumerate(info):
            exp += f"{i}. {explanation}"
            exp += "\n"
        USER_PROMPT = f"""

        # Input Information

        ### Statement

        {goal}

        ### Explanations

        {exp}

        **Output:**
        """
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts
class StatementInformalizationPromptyFactory():

    def make_informalize_prompt(self, examples : List[StatementFewShotExample], info : StatementInfo) -> Iterable[ChatCompletionMessageParam] :
        SYSTEM_PROMPT = """
You are a mathematician who is familiar with the grammar of Lean, a theorem proving assistant.
Translate a formal statement written in Lean4 into a natural-language explanation without using predicates from the formal language.

Ensure that predicates used in the formal language are not included in the final explanation. Provide all necessary information in the explanation without omitting essential details or adding extraneous commentary.

# Steps

1. **Understand the Formal statement**:
- Carefully read the statement to grasp its meaning and the implications of each part.
2. **Analyze Definitions**:
- Review any provided definitions of predicates or terms used in the formal statement to fully understand their meaning.
3. **Translate to Natural Language**:
- Convert the formal statement into a natural-language statement, respecting the constraints.
    - Please ensure that the information from the given definition is appropriately reflected in the proposition.
- Refrain from using the exact syntactic structure or any specific predicates from the formal statement in the natural-language version.
- Include all necessary details from the formal statement to provide a complete and clear explanation without adding unnecessary information.

# Output Format

A natural-language statement which contain reflect the content of formal statement.
        """

        USER_PROMPT = """
# Examples 
        """
        for i, example in enumerate(examples):
            USER_PROMPT += f"""
## Example {i + 1}
- **Input Information**: 
- Formal statement: {example.statement}
- Definitions: 
{"\n-".join(example.definitions)}
- **Output**: 
{example.output}
        """
        USER_PROMPT +="""
# Notes

- Focus on clarity and conciseness while ensuring a complete representation of the formal statement.
- Ensure that the transformation respects constraints and avoids using formal syntax or predicates/directly from the formal statement.

**Input Information**:
        """

        USER_PROMPT +=f"""
- Formal statement: {info.statement}
- Definitions: 
{"\n-".join(info.definitions)}
        """
        USER_PROMPT +="""
**Output**: 
        """
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts
    
    def make_summerize_prompts(self, goal : str, info : List[str]) -> Iterable[ChatCompletionMessageParam] : 
        SYSTEM_PROMPT = """
From now on, act like you're a mathematician and good at writing mathematical proofs.

Summarize the sequence of steps used to prove the given proposition into a coherent and natural narrative suitable for a mathematical proof.

# Steps

1. **Understand the essence of the mathematical proposition**: Comprehend the given proposition and identify the goal of the subsequent steps.  
2. **Understand the content of the proof steps**: Grasp the operations performed to prove the proposition.  
3. **Shape the steps into a coherent draft**: Combine the sequence of steps provided, adding appropriate conjunctions to form a natural and cohesive draft of the proof.
- When writing a proof, start with a sentence that clearly states the proposition you are going to prove (e.g., "We will show that...") and then continue with the proof in that form.

# Output Format

- Provide a natural language explanation summarizing the operation of the tactic and the immediate effects on the hypotheses and goals.
  - Provide all necessary information for the explanation in precise and detailed terms.

# Notes

- Ensure that all statements in the proof are directly supported by the information in the input.
- Be sure to include explanations of critical elements in constructing the proof, such as the introduction of variables and the use of important theorems.
- Avoid introducing new operations or assumptions not present in the input sentences.
"""
# 4. **Eliminate redundant explanations**: Remove any redundant parts from your draft.
# 5. **Omit mathematically trivial content**: Exclude mathematical expressions that are easy to understand without having to write them out, and write a proof that only introduces variables and writes important operations.
    # Please leave the following expressions:
    # - Introducing new variables and functions or definitions that are defined in the proof
    # - Propositions required for the proof and their concise proofs
    # The following expressions should be considered self-evident and should be removed:
    # - Equation transformation that is obvious without explicit explanation
        exp = ""
        for i, explanation in enumerate(info):
            exp += f"{i}. {explanation}"
            exp += "\n"
        USER_PROMPT = f"""

        # Input Information

        ### Statement

        {goal}

        ### Explanations

        {exp}

        **Output:**
        """
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts
class TacticInformalizationPromptFactoryWithTemplates:
    """
    非形式化に用いるプロンプトをテンプレートを用いて生成するための処理を実装する
    """

    def make_informalize_prompt(self, info : TacticInfo,  few_shots : TacticExampleInfo, templateInfo : TemplateInfo, premises : List[str]) -> Iterable[ChatCompletionMessageParam]:
        SYSTEM_PROMPT = """
You are an expert in Lean4 and formal mathematics. 
Transform the given Lean4 tactic into a clear and concise natural language explanation, accurately conveying the operation performed as a step in a mathematical proof without using the format of the formal language.

Ensure that any predicates from the formal language are not included in the explanation.

# Steps

1. **Understand the Applied Tactic**:
- Analyze the `Applied Tactic` to comprehend its function within the proof.
	 - If a tactic involves using one or more theorems or definitions, read the theorems listed under `Using Definitions and Theorems` and ensure you understand their content.

2. **Examine Hypotheses and Goals**:
- Compare `Hypotheses And Goals Before Tactic Application` with `Hypotheses And Goals After Tactic Application` to understand what changes in objectives occurred.
    - Hypotheses and goals are separated with the symbol '⊢'.

3. **Understand the output format**:
- Check the given output templates that should be followed.  
  - Some tactics may have multiple output templates. Each template specifies the conditions under which it should be used, so read the conditions carefully and select the appropriate template.  

- Each template contains tokens representing placeholders that need to be filled. Read the descriptions of each token provided below, along with the conditions that should be followed in the output, to understand what information needs to be generated.  

 
4. **Formulate the Explanation**:
- Describe what action the tactic took, referring only to what was altered based on the changes observed in the hypotheses and goals.
- Avoid directly referencing predicates from the formal language.
    - When referring to variables, be sure to explicitly use these variable names in the output.
        - (ex) Set \\( A \\) is Empty.
    - **Do not** include the names of theorems or definitions in formal languages, or variables used as aliases to specific expressions (like h : x = 2 * y) in the output. Instead, explain the content in natural language.
- You must output only the sentence with the filled-in template and **avoid** any additional text.

# Output Format

- Provide a natural language explanation summarizing the operation of the tactic and the immediate effects on the hypotheses and goals.
  - Provide all necessary information for the explanation in precise and detailed terms.
- You must output only the sentence with the filled-in template and **avoid** any additional text.
            """
        USER_PROMPT = """
# Examples
"""
        for i, example in enumerate(few_shots.examples):
            USER_PROMPT += f"""
### Example {i + 1}

**Input Information**:
- Applied Tactic: {example.appliedTactic}
- Hypotheses And Goals Before Tactic Application: {example.goalsBefore}
- Hypotheses And Goals After Tactic Application: {example.goalsAfter}

**Using Definitions and Theorems**

"""
            for premise in example.defintionsAndTheorems:
                USER_PROMPT += f"- {premise}\n"
            USER_PROMPT += f"""
**Output**: 
{example.output}
""" 
        USER_PROMPT += f"""
# Notes

- Always determine what assumptions or definitions are brought into effect or altered.
- Make sure explanations are precise to maintain clarity and avoid unnecessary details.
- You must output only the sentence with the filled-in template and **avoid** any additional text.
- Do not include expressions written in Lean's formal language in the output.  
  - In formal proofs, casts such as from natural numbers to integers are represented by \\( \\uparrow \\). Therefore, ensure that the output does not contain \\( \\uparrow \\) representing a cast.
- If you use explanations or citations to output formulas, please use TeX formatting for citations if the formulas are not complex, or use explanations written in natural language if the formulas are complex.

Using the example above as a reference, please explain the following input in natural language as one operation in a mathematical proof.

**Input Information**:
- Applied Tactic: {info.appliedTactic}
- Hypotheses And Goals Before Tactic Application: {info.goalsBefore}
- Hypotheses And Goals After Tactic Application: {info.goalsAfter}

**Output Templates**
"""
        USER_PROMPT += f"""

**Template**
{templateInfo.template}
						"""
        if len(templateInfo.tokenInfos) > 0:
            USER_PROMPT += "¥n**Token Information**¥n"
            for token, description in templateInfo.tokenInfos.items():
                USER_PROMPT += f"""
- **{token}** : {description}
						"""
        USER_PROMPT += """
**Using Definitions and Theorems**
"""
        for premise in premises:
            USER_PROMPT += f"- {premise}\n"
        USER_PROMPT += """
**Output**:
"""
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts
    
class StatementInformalizationPromptyFactory():

    def make_informalize_prompt(self, examples : List[StatementFewShotExample], info : StatementInfo) -> Iterable[ChatCompletionMessageParam] :
        SYSTEM_PROMPT = """
You are a mathematician who is familiar with the grammar of Lean, a theorem proving assistant.
Translate a formal statement written in Lean4 into a natural-language explanation without using predicates from the formal language.

Ensure that predicates used in the formal language are not included in the final explanation. Provide all necessary information in the explanation without omitting essential details or adding extraneous commentary.

# Steps

1. **Understand the Formal statement**:
- Carefully read the statement to grasp its meaning and the implications of each part.
2. **Analyze Definitions**:
- Review any provided definitions of predicates or terms used in the formal statement to fully understand their meaning.
3. **Translate to Natural Language**:
- Convert the formal statement into a natural-language statement, respecting the constraints.
    - Please ensure that the information from the given definition is appropriately reflected in the proposition.
- Refrain from using the exact syntactic structure or any specific predicates from the formal statement in the natural-language version.
- Include all necessary details from the formal statement to provide a complete and clear explanation without adding unnecessary information.

# Output Format

A natural-language statement which contain reflect the content of formal statement.
        """

        USER_PROMPT = """
# Examples 
        """
        for i, example in enumerate(examples):
            USER_PROMPT += f"""
## Example {i + 1}
- **Input Information**: 
- Formal statement: {example.statement}
- Definitions: 
{"\n-".join(example.definitions)}
- **Output**: 
{example.output}
        """
        USER_PROMPT +="""
# Notes

- Focus on clarity and conciseness while ensuring a complete representation of the formal statement.
- Ensure that the transformation respects constraints and avoids using formal syntax or predicates/directly from the formal statement.

**Input Information**:
        """

        USER_PROMPT +=f"""
- Formal statement: {info.statement}
- Definitions: 
{"\n-".join(info.definitions)}
        """
        USER_PROMPT +="""
**Output**: 
        """
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts

class PremiseInformalizationPromptFactory():
    def make_description(self, premiseInfo : PremiseInfo, explanatories : List[Explanatory], few_shots : List[PremiseLibraryData])-> Iterable[ChatCompletionMessageParam] :
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
        if explanatories != []:
                USER_PROMPT += """
* Explanatory
"""
                for ex in explanatories:
                    USER_PROMPT += f"""
{ex.name} : {ex.description}
"""
        USER_PROMPT += f"""

* Output:
"""
        prompts = [
            ChatCompletionSystemMessageParam(
                role="system",
                content=SYSTEM_PROMPT
            ),
            ChatCompletionUserMessageParam(
                role="user",
                content=USER_PROMPT
            )
        ]
        return prompts