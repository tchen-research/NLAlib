"""Published coverage must not present a transitive sorry dependency as proved."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from coverage_status import annotate_coverage


class CoverageTrustTests(unittest.TestCase):
    def test_derived_declaration_is_unfinished_without_literal_scaffold_doc(self):
        index = {"items": [{"status": "nlalib", "decls": ["Derived"]}]}
        annotate_coverage(index, {}, {"Derived": {"sorry": True, "doc": "A corollary."}})
        self.assertEqual(index["items"][0]["status"], "scaffold")

    def test_atlas_only_reference_inherits_unfinished_status(self):
        index = {"items": [{"status": "partial", "atlas": ["open-result"]}]}
        annotate_coverage(index, {"open-result": {"status": "scaffold"}}, {})
        self.assertEqual(index["items"][0]["status"], "scaffold")

    def test_clean_decl_does_not_discharge_another_unfinished_reference(self):
        index = {"items": [{"status": "nlalib", "decls": ["Clean", "Open"]}]}
        annotate_coverage(index, {}, {"Clean": {"sorry": False}, "Open": {"sorry": True}})
        self.assertEqual(index["items"][0]["status"], "scaffold")

    def test_independent_proved_declaration_remains_proved(self):
        index = {"items": [{"status": "nlalib", "decls": ["Clean"]}]}
        annotate_coverage(index, {}, {"Clean": {"sorry": False}})
        self.assertEqual(index["items"][0]["status"], "nlalib")


if __name__ == "__main__":
    unittest.main()
