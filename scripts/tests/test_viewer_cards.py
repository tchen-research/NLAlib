"""Smoke-test all actual result cards, independent of optional CDN assets."""
import pathlib
import subprocess
import unittest


class ViewerCardTests(unittest.TestCase):
    def test_every_atlas_card_and_deep_link_opens(self):
        script = pathlib.Path(__file__).with_name("viewer_cards.js")
        result = subprocess.run(["node", str(script)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_area_cards_and_counts_follow_filters(self):
        script = pathlib.Path(__file__).with_name("viewer_areas.js")
        result = subprocess.run(["node", str(script)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
