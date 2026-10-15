"""The upstream response interface, backed only by subscription-authenticated Codex."""
import asyncio
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import tomllib

from openai.types.chat import ChatCompletionMessage
from DomainService.IOpenAIAPICommunicator import IOpenAIAPICommunicator


def subscription_environment():
    env = os.environ.copy()
    for key in ("OPENAI_API_KEY", "CODEX_API_KEY", "OPENAI_BASE_URL", "AZURE_OPENAI_API_KEY"):
        env.pop(key, None)
    return env


def conversation_prompt(messages):
    messages = list(messages)
    if not messages or any(not isinstance(m.get("content"), str) for m in messages):
        raise ValueError("Headless informalization requires nonempty text messages")
    return (
        "Complete the final user request in the conversation below. Earlier messages "
        "supply instructions, context, and examples. Return only the requested answer. "
        "All required material is supplied; do not use tools.\n\n"
        + json.dumps(messages, ensure_ascii=False)
    )


class CodexHeadlessCommunicator(IOpenAIAPICommunicator):
    backend = "codex-headless-chatgpt-v1"

    def __init__(self):
        self.executable = shutil.which(os.getenv("INFORMALIZATION_CODEX", "codex"))
        if not self.executable:
            raise EnvironmentError("Codex CLI was not found; no API fallback is available")
        config_file = Path(os.getenv("CODEX_HOME", str(Path.home() / ".codex"))) / "config.toml"
        config = tomllib.loads(config_file.read_text()) if config_file.exists() else {}
        # Only inherit model preferences, never provider, hooks, plugins, or MCP settings.
        self.model = os.getenv("INFORMALIZATION_MODEL") or config.get("model")
        if not self.model:
            raise EnvironmentError("Set a Codex model in config.toml or INFORMALIZATION_MODEL")
        self.effort = os.getenv("INFORMALIZATION_REASONING_EFFORT") or config.get("model_reasoning_effort")
        self.timeout = float(os.getenv("INFORMALIZATION_TIMEOUT_SECONDS", "900"))
        self.last_response_metadata = {}

    @property
    def request_identity(self):
        return {"backend": self.backend, "model": self.model, "reasoning_effort": self.effort,
                "temperature_applied": False}

    def check_authentication(self):
        result = subprocess.run([self.executable, "login", "status"],
                                env=subscription_environment(), capture_output=True,
                                text=True, timeout=30)
        status = result.stdout + result.stderr
        if result.returncode or "Logged in using ChatGPT" not in status:
            raise RuntimeError("Codex must be signed in through ChatGPT; paid API use is disabled")

    def command(self, directory, output):
        command = [self.executable, "exec", "--ignore-user-config", "--ignore-rules",
                   "--ephemeral", "--skip-git-repo-check", "--sandbox", "read-only",
                   "--color", "never", "--json", "--cd", str(directory),
                   "--output-last-message", str(output), "--model", self.model,
                   "-c", 'forced_login_method="chatgpt"', "-c", 'model_provider="openai"',
                   "-c", "project_doc_max_bytes=0", "-c", 'web_search="disabled"']
        for feature in ("shell_tool", "multi_agent", "apps", "plugins", "hooks",
                        "browser_use", "computer_use", "image_generation", "memories"):
            command.extend(["--disable", feature])
        if self.effort:
            command.extend(["-c", "model_reasoning_effort=" + json.dumps(self.effort)])
        return command + ["-"]

    async def get_response(self, messages, temperature=1.0):
        prompt = conversation_prompt(messages)
        await asyncio.to_thread(self.check_authentication)
        with tempfile.TemporaryDirectory(prefix="informalization-codex-") as directory:
            output = Path(directory) / "answer.txt"
            process = await asyncio.create_subprocess_exec(
                *self.command(directory, output), env=subscription_environment(),
                stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE, start_new_session=(os.name == "posix"))
            try:
                stdout, _stderr = await asyncio.wait_for(process.communicate(prompt.encode()), self.timeout)
            except BaseException:
                if process.returncode is None:
                    if os.name == "posix":
                        os.killpg(process.pid, signal.SIGKILL)
                    else:
                        process.kill()
                    await process.wait()
                raise
            if process.returncode:
                # Do not expose raw CLI errors, which can contain authentication material.
                raise RuntimeError(f"Headless Codex failed (exit {process.returncode}); no API fallback")
            events = []
            for line in stdout.decode().splitlines():
                try:
                    events.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
            completed = [event for event in events if event.get("type") == "turn.completed"]
            if not completed or not output.exists() or not output.read_text().strip():
                raise RuntimeError("Headless Codex did not complete with a nonempty answer")
            self.last_response_metadata = {
                **self.request_identity, "authentication": "chatgpt",
                "usage": completed[-1].get("usage"), "requested_temperature": temperature,
                "prompt_format": "conversation messages serialized as JSON in CLI stdin",
            }
            return ChatCompletionMessage(role="assistant", content=output.read_text())
