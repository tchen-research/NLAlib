"""Boundary regressions: an unfinished import must never leak into the default surface."""
import importlib.util
import json
import pathlib
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parents[1] / "import_surface.py"
SPEC = importlib.util.spec_from_file_location("import_surface", SCRIPT)
surface = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(surface)


class ImportSurfaceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.old_root = surface.ROOT
        self.addCleanup(setattr, surface, "ROOT", self.old_root)
        surface.ROOT = pathlib.Path(self.temp.name)
        (surface.ROOT / "scripts").mkdir()
        (surface.ROOT / "atlas").mkdir()
        self.module("NLAlib.Matrix.Basic")
        self.module("NLAlib.Matrix.Open", "NLAlib.Matrix.Basic")
        self.module("NLAlib.Matrix.Consumer", "NLAlib.Matrix.Open")
        self.module("NLAlib.Matrix.Closed", "NLAlib.Matrix.Basic")
        self.module("NLAlib.Matrix", "NLAlib.Matrix.Consumer", "NLAlib.Matrix.Closed")
        (surface.ROOT / "scripts/experimental_modules.txt").write_text("NLAlib.Matrix.Open\n")

    def module(self, name, *imports):
        path = surface.ROOT / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("".join(f"import {i}\n" for i in imports))

    def test_excludes_transitive_consumers_but_preserves_shared_foundations(self):
        outputs = surface.surfaces()
        inventory = json.loads(outputs[surface.ROOT / "atlas/import_surface.json"])
        self.assertEqual(inventory["default_modules"],
                         ["NLAlib.Matrix.Basic", "NLAlib.Matrix.Closed"])
        self.assertEqual(inventory["excluded_modules"]["NLAlib.Matrix.Consumer"],
                         ["NLAlib.Matrix.Open"])
        default = outputs[surface.ROOT / "NLAlib.lean"]
        self.assertTrue(default.startswith("import NLAlib.Matrix.Closed\n"))
        self.assertNotIn("import NLAlib.Matrix.Consumer\n", default)

    def test_unknown_experimental_root_is_an_error(self):
        (surface.ROOT / "scripts/experimental_modules.txt").write_text("NLAlib.Missing\n")
        with self.assertRaisesRegex(ValueError, "Unknown experimental"):
            surface.surfaces()

    def test_content_cannot_import_umbrella(self):
        self.module("NLAlib.Matrix.Closed", "NLAlib.Experimental")
        with self.assertRaisesRegex(ValueError, "forbidden umbrella"):
            surface.surfaces()

    def test_safe_cycle_cannot_silently_disappear(self):
        self.module("NLAlib.Matrix.CycleA", "NLAlib.Matrix.CycleB")
        self.module("NLAlib.Matrix.CycleB", "NLAlib.Matrix.CycleA")
        with self.assertRaisesRegex(ValueError, "unreachable"):
            surface.surfaces()


if __name__ == "__main__":
    unittest.main()
