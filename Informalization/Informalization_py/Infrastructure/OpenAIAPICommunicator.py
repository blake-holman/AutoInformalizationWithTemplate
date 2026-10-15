"""Compatibility import for upstream services; this fork uses headless Codex."""
from Infrastructure.CodexHeadlessCommunicator import CodexHeadlessCommunicator

OpenAIAPICommunicator = CodexHeadlessCommunicator
