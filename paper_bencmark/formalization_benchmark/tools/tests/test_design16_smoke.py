from __future__ import annotations

from pathlib import Path
import sys
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from design16_smoke import _routed_candidate_template  # noqa: E402


class Design16SmokeTests(unittest.TestCase):
    def test_primary_route_template_has_narrow_import_and_checks(self) -> None:
        rendered = _routed_candidate_template(
            {
                "retrieved_roots": [
                    {
                        "declaration": {
                            "name": "NumStability.root_bound",
                            "module": "NumStability.Algorithms.Horner",
                        },
                        "dependencies": [
                            {
                                "name": "NumStability.gamma_mono",
                                "module": "NumStability.Analysis.Rounding",
                            }
                        ],
                    }
                ]
            }
        )
        self.assertIn("import NumStability.Algorithms.Horner", rendered)
        self.assertIn("#check NumStability.root_bound", rendered)
        self.assertIn("#check NumStability.gamma_mono", rendered)
        self.assertIn("theorem target : True", rendered)


if __name__ == "__main__":
    unittest.main()
