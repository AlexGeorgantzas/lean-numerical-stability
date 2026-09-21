from __future__ import annotations

import json
from pathlib import Path
import tempfile
import types
import sys
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkError, sha256_file  # noqa: E402
from design16_matched import (  # noqa: E402
    SCIENTIFIC_STATUS,
    _atlas_declarations,
    _classify_atlas,
    _condition_order,
    condition_spec,
    _candidate_template,
)


def _write_atlas(root: Path, modules: list[str]) -> Path:
    root.mkdir()
    declarations = root / "declarations.jsonl"
    declarations.write_text(
        "".join(
            json.dumps(
                {
                    "name": f"{module}.sample",
                    "module": module,
                    "kind": "theorem",
                    "signature": "theorem sample : True",
                }
            )
            + "\n"
            for module in modules
        ),
        encoding="utf-8",
    )
    (root / "atlas.json").write_text(
        json.dumps(
            {
                "schema_version": "numstability-library-atlas-2",
                "declaration_count": len(modules),
                "declarations_sha256": sha256_file(declarations),
            }
        ),
        encoding="utf-8",
    )
    return root


class Design16MatchedTests(unittest.TestCase):
    def test_condition_order_requires_one_of_each(self) -> None:
        self.assertEqual(_condition_order("R1,R0"), ("R1", "R0"))
        with self.assertRaises(BenchmarkError):
            _condition_order("R0,R0")

    def test_mathlib_atlas_rejects_treatment_leakage(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            atlas = _write_atlas(root / "atlas", ["NumStability.Analysis.Gamma"])
            declarations = _atlas_declarations(atlas, label="Mathlib")
            with self.assertRaises(BenchmarkError):
                _classify_atlas(declarations, expect_numstability=False)

    def test_condition_specs_change_only_corpus_and_olean_visibility(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            mathlib = _write_atlas(root / "mathlib", ["Mathlib.Analysis.Normed.Ring.Basic"])
            treatment = _write_atlas(
                root / "numstability", ["NumStability.Analysis.Rounding"]
            )
            olean = root / "olean"
            olean.mkdir()
            deployment = types.SimpleNamespace(
                library_atlas=treatment,
                library_olean=olean,
            )
            r0 = condition_spec("R0", deployment=deployment, mathlib_atlas=mathlib)
            r1 = condition_spec("R1", deployment=deployment, mathlib_atlas=mathlib)
            self.assertEqual(r0.corpus_id, "mathlib-only")
            self.assertEqual(r1.corpus_id, "mathlib-plus-numstability")
            self.assertEqual(r0.compiler_condition, "N")
            self.assertEqual(r1.compiler_condition, "L")
            self.assertIsNone(r0.library_olean)
            self.assertEqual(r1.library_olean, olean)
            self.assertEqual(r0.atlas_paths, r1.atlas_paths[:1])
            self.assertEqual(SCIENTIFIC_STATUS, "UNSCORED_ENGINEERING_EXPLORATORY")

    def test_stale_atlas_hash_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            atlas = _write_atlas(root / "atlas", ["Mathlib.Data.Real.Basic"])
            (atlas / "declarations.jsonl").write_text("{}\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                _atlas_declarations(atlas, label="Mathlib")

    def test_statement_template_has_exactly_one_target_sorry(self) -> None:
        source = _candidate_template({"retrieved_roots": []}, statement_only=True)
        self.assertEqual(source.count("sorry"), 1)
        self.assertIn("theorem target : True := by\n  sorry", source)
        self.assertNotIn("trivial", source)


if __name__ == "__main__":
    unittest.main()
