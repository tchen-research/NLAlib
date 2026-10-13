"""Complete theorem families must retain checked proof dependencies and linkage."""
import copy
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from atlas_proof_status import proof_family_status


class ProofFamilyTests(unittest.TestCase):
    def setUp(self):
        self.result = {"id": "result", "proof_family": {"clauses": [
            {"statement": "Existence", "decls": ["Exists"]},
            {"statement": "Uniqueness", "decls": ["Unique"]},
        ]}}
        self.declarations = {name: {
            "kind": "theorem", "atlas": ["result"], "atlas_partial": ["result"], "sorry": False
        } for name in ("Exists", "Unique")}

    def test_complete_family_of_partial_components_is_proved(self):
        self.assertEqual(proof_family_status(self.result, self.declarations), "proved")

    def test_transitive_unfinished_component_makes_whole_family_scaffold(self):
        self.declarations["Unique"]["sorry"] = True
        self.assertEqual(proof_family_status(self.result, self.declarations), "scaffold")

    def test_missing_or_untagged_component_is_an_error(self):
        for declarations in ({"Exists": self.declarations["Exists"]}, copy.deepcopy(self.declarations)):
            if "Unique" in declarations:
                declarations["Unique"]["atlas"] = []
            with self.assertRaises(ValueError):
                proof_family_status(self.result, declarations)

    def test_empty_clauses_cannot_certify_complete_coverage(self):
        for clauses in ([], [{"statement": "Existence", "decls": []}]):
            self.result["proof_family"]["clauses"] = clauses
            with self.assertRaises(ValueError):
                proof_family_status(self.result, self.declarations)

    def test_definition_cannot_supply_a_proof(self):
        self.declarations["Unique"]["kind"] = "def"
        with self.assertRaises(ValueError):
            proof_family_status(self.result, self.declarations)

    def test_blank_statement_and_duplicate_references_are_errors(self):
        for clause in ({"statement": " ", "decls": ["Exists"]},
                       {"statement": "Existence", "decls": ["Exists", "Exists"]}):
            self.result["proof_family"]["clauses"] = [clause]
            with self.assertRaises(ValueError):
                proof_family_status(self.result, self.declarations)

    def test_unreviewed_components_do_not_promote_a_result(self):
        self.assertIsNone(proof_family_status({"id": "result"}, self.declarations))


if __name__ == "__main__":
    unittest.main()
