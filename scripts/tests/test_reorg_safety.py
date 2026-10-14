"""Regression coverage for preserving proofs during aggregator generation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("reorg", Path(__file__).parents[1] / "reorg.py")
reorg = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(reorg)


class AggregatorSafetyTests(unittest.TestCase):
    def test_new_topic_directory_does_not_overwrite_existing_proofs(self):
        declarations = {
            "theorem": "theorem preserved_result : True := True.intro\n",
            "scoped instance": (
                "namespace Preserved\n"
                "scoped instance preserved_result : Inhabited Nat := ⟨0⟩\n"
                "end Preserved\n"
            ),
            "local instance": "local instance preserved_result : Inhabited Nat := ⟨0⟩\n",
            "nonrec def": "nonrec def preserved_result : Nat := 0\n",
        }
        for kind, proof in declarations.items():
            with self.subTest(declaration=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                topic = root / "NLAlib/ForMathlib/Algebra/Polynomial"
                topic.mkdir(parents=True)
                existing = topic.with_suffix(".lean")
                existing.write_text(proof, encoding="utf-8")
                leaf = topic / "NewResult.lean"
                leaf_source = "theorem new_result : True := True.intro\n"
                leaf.write_text(leaf_source, encoding="utf-8")
                with patch.object(reorg, "ROOT", root):
                    with self.assertRaisesRegex(ValueError, "refusing to overwrite declarations"):
                        reorg.gen_aggregators(root / "NLAlib")
                self.assertEqual(existing.read_text(encoding="utf-8"), proof)
                self.assertEqual(leaf.read_text(encoding="utf-8"), leaf_source)
                self.assertFalse((root / "NLAlib/ForMathlib/Algebra.lean").exists())


if __name__ == "__main__":
    unittest.main()
