"""Regression checks for the Python generation path; no API calls."""
import asyncio
from pathlib import Path
from types import SimpleNamespace
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Informalization/Informalization_py"))
from ApplicationService.PremiseDiscriptor import PremiseDescriptor
from ApplicationService.TacticInformalizer import TacticInformalizer
from Infrastructure.FewShotExampleRepository import TacticFewShotExampleRepository


class GenerationSupportTests(unittest.TestCase):
    def test_cached_description_is_returned(self):
        descriptor = object.__new__(PremiseDescriptor)
        descriptor.__library__ = SimpleNamespace(
            check_existence=lambda target: True,
            get_data=lambda target: SimpleNamespace(description="The cached statement."),
        )
        result = asyncio.run(descriptor.proc_description(object(), [], Path("unused")))
        self.assertEqual(result, "The cached statement.")

    def test_unsupported_tactic_is_rejected_without_shifting_answers(self):
        informalizer = object.__new__(TacticInformalizer)
        informalizer.__rewrite_tactic_list__ = []
        informalizer.__few_shot_repository__ = TacticFewShotExampleRepository()
        tactic = SimpleNamespace(tacticCommand="unsupported_test_tactic", appliedTactic="unsupported_test_tactic")
        with self.assertRaisesRegex(RuntimeError, "Unsupported tactic"):
            asyncio.run(informalizer.informalize(None, [tactic], [], None, Path("unused")))


if __name__ == "__main__":
    unittest.main()
