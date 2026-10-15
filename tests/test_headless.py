"""Offline checks for authentication, subprocess routing, and completion handling."""
import asyncio
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Informalization/Informalization_py"))
from Infrastructure.CodexHeadlessCommunicator import CodexHeadlessCommunicator


FAKE = '''#!/usr/bin/env python3
import json, os, pathlib, sys
assert 'OPENAI_API_KEY' not in os.environ
assert 'CODEX_API_KEY' not in os.environ
assert 'OPENAI_BASE_URL' not in os.environ
if sys.argv[1:] == ['login', 'status']:
    print('Logged in using ' + os.environ.get('TEST_AUTH', 'ChatGPT'))
else:
    assert '--ignore-user-config' in sys.argv
    assert 'forced_login_method="chatgpt"' in sys.argv
    assert 'model_provider="openai"' in sys.argv
    assert '--ephemeral' in sys.argv
    assert '--sandbox' in sys.argv and 'read-only' in sys.argv
    pathlib.Path(os.environ['TEST_INVOCATION']).write_text(json.dumps(sys.argv))
    messages = json.loads(sys.stdin.read().split('\\n\\n', 1)[1])
    output = pathlib.Path(sys.argv[sys.argv.index('--output-last-message') + 1])
    output.write_text(messages[-1]['content'])
    if os.environ.get('TEST_COMPLETE', '1') == '1':
        print(json.dumps({'type':'turn.completed', 'usage':{'input_tokens':20,'output_tokens':5}}))
'''


class HeadlessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        executable = self.directory / 'codex'
        executable.write_text(FAKE)
        executable.chmod(0o700)
        (self.directory / 'config.toml').write_text('model = "test-model"\nmodel_reasoning_effort = "medium"\n')
        self.marker = self.directory / 'invocation.json'
        self.environment = patch.dict(os.environ, {
            'CODEX_HOME': str(self.directory), 'INFORMALIZATION_CODEX': str(executable),
            'OPENAI_API_KEY': 'test-sentinel', 'CODEX_API_KEY': 'test-sentinel',
            'OPENAI_BASE_URL': 'https://invalid.example', 'TEST_INVOCATION': str(self.marker),
            'TEST_AUTH': 'ChatGPT', 'TEST_COMPLETE': '1',
        })
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def test_subscription_transport_preserves_messages_and_strips_api_configuration(self):
        communicator = CodexHeadlessCommunicator()
        response = asyncio.run(communicator.get_response([
            {'role':'system','content':'Explain the proof.'},
            {'role':'assistant','content':'An example.'},
            {'role':'user','content':'The bound is e × d.'},
        ], 0.4))
        self.assertEqual(response.content, 'The bound is e × d.')
        self.assertEqual(communicator.last_response_metadata['authentication'], 'chatgpt')
        self.assertFalse(communicator.last_response_metadata['temperature_applied'])
        self.assertEqual(communicator.last_response_metadata['usage']['input_tokens'], 20)
        self.assertTrue(self.marker.exists())

    def test_api_login_is_rejected_before_model_execution(self):
        with patch.dict(os.environ, {'TEST_AUTH':'API key'}):
            with self.assertRaisesRegex(RuntimeError, 'signed in through ChatGPT'):
                asyncio.run(CodexHeadlessCommunicator().get_response([{'role':'user','content':'test'}]))
        self.assertFalse(self.marker.exists())

    def test_missing_completion_is_rejected_even_when_output_exists(self):
        with patch.dict(os.environ, {'TEST_COMPLETE':'0'}):
            with self.assertRaisesRegex(RuntimeError, 'did not complete'):
                asyncio.run(CodexHeadlessCommunicator().get_response([{'role':'user','content':'test'}]))

    def test_legacy_service_import_uses_headless_transport(self):
        from Infrastructure.OpenAIAPICommunicator import OpenAIAPICommunicator
        self.assertIs(OpenAIAPICommunicator, CodexHeadlessCommunicator)


if __name__ == '__main__':
    unittest.main()
