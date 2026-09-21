from __future__ import annotations

import inspect
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
    _build_packet_olean_runtime,
    _library_exploration_policy,
    _condition_faithfulness_status,
    _run_statement_condition_attempts,
    _statement_pair_status,
    _submission_clock,
    _treatment_interface_check,
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
    def test_statement_submission_clock_includes_return_to_freeze_gap(self) -> None:
        clock = _submission_clock(
            active_started_perf_ns=1_000_000_000,
            active_ended_perf_ns=4_000_000_000,
            freeze_started_perf_ns=6_000_000_000,
            freeze_completed_perf_ns=7_000_000_000,
        )
        self.assertEqual(clock["model_active_seconds"], 3.0)
        self.assertEqual(clock["candidate_freeze_seconds"], 1.0)
        self.assertEqual(clock["post_turn_through_freeze_seconds"], 3.0)
        self.assertEqual(clock["contestant_active_seconds"], 6.0)

    def test_statement_submission_freezes_before_scans_and_caps_before_validation(self) -> None:
        source = inspect.getsource(_run_statement_condition_attempts)
        self.assertLess(
            source.index("frozen = freeze_candidate("),
            source.index("exploration_policy = _library_exploration_policy("),
        )
        self.assertLess(
            source.index('prevalidation_status = "ACTIVE_TIME_LIMIT"'),
            source.index("validation = validate_candidate("),
        )

    def test_statement_incidents_never_become_ineligible_benchmark_outcomes(self) -> None:
        self.assertEqual(
            _condition_faithfulness_status("AUDIT_SYSTEM_INCIDENT"),
            "NOT_DECIDED_INFRASTRUCTURE",
        )
        self.assertEqual(
            _statement_pair_status("ACCEPTED_FAITHFUL", "AUDIT_SYSTEM_INCIDENT"),
            ("PAIR_INCIDENT", "NOT_DECIDED_INFRASTRUCTURE"),
        )
        self.assertEqual(
            _statement_pair_status("ACCEPTED_FAITHFUL", "ATTEMPT_LIMIT_UNFAITHFUL"),
            ("AUDITED_PAIR_INELIGIBLE", "PAIR_NOT_BOTH_FAITHFUL"),
        )

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

    def test_treatment_interface_rejects_unlisted_direct_dependency(self) -> None:
        composition = {
            "retrieved_roots": [
                {
                    "declaration": {
                        "name": "NumStability.allowed",
                        "module": "NumStability.Allowed",
                    },
                    "dependencies": [],
                }
            ]
        }
        private = {
            "raw_semantic_report": {
                "dependencies": [
                    {
                        "name": "NumStability.hidden",
                        "owner_module": "NumStability.Hidden",
                    }
                ],
                "edges": [
                    {
                        "parent": "HighamBenchCandidate.target",
                        "child": "NumStability.hidden",
                    }
                ],
            }
        }
        result = _treatment_interface_check(
            candidate_text="import NumStability.Hidden\n",
            composition=composition,
            private_dossier=private,
        )
        self.assertFalse(result["pass"])
        self.assertEqual(result["forbidden_imports"], ["NumStability.Hidden"])
        self.assertEqual(
            result["forbidden_direct_declarations"], ["NumStability.hidden"]
        )
        for source in (
            "public import NumStability.Hidden\n",
            "import NumStability.Hidden -- hidden\n",
            "import Mathlib NumStability.Hidden\n",
        ):
            with self.subTest(source=source):
                self.assertFalse(
                    _treatment_interface_check(
                        candidate_text=source,
                        composition=composition,
                        private_dossier=private,
                    )["pass"]
                )

    def test_treatment_interface_allows_transitive_dependency_of_listed_root(self) -> None:
        composition = {
            "retrieved_roots": [
                {
                    "declaration": {
                        "name": "NumStability.allowed",
                        "module": "NumStability.Allowed",
                    },
                    "dependencies": [],
                }
            ]
        }
        private = {
            "raw_semantic_report": {
                "dependencies": [
                    {
                        "name": "NumStability.allowed",
                        "owner_module": "NumStability.Allowed",
                    },
                    {
                        "name": "NumStability.internal",
                        "owner_module": "NumStability.Internal",
                    },
                ],
                "edges": [
                    {
                        "parent": "HighamBenchCandidate.target",
                        "child": "NumStability.allowed",
                    },
                    {
                        "parent": "NumStability.allowed",
                        "child": "NumStability.internal",
                    },
                ],
            }
        }
        result = _treatment_interface_check(
            candidate_text="import NumStability.Allowed\n",
            composition=composition,
            private_dossier=private,
        )
        self.assertTrue(result["pass"])

    def test_library_exploration_policy_rejects_mounted_library_search(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            events = Path(raw) / "events.jsonl"
            events.write_text(
                json.dumps(
                    {
                        "params": {
                            "item": {
                                "type": "commandExecution",
                                "command": "/usr/bin/bash -lc 'find /library-olean -type f'",
                            }
                        }
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            result = _library_exploration_policy(events)
            self.assertFalse(result["pass"])
            self.assertEqual(result["command_count"], 1)

    def test_library_exploration_policy_allows_workspace_compilation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            events = Path(raw) / "events.jsonl"
            events.write_text(
                json.dumps(
                    {
                        "params": {
                            "item": {
                                "type": "commandExecution",
                                "command": "lean --root . -o Candidate.olean Candidate.lean",
                            }
                        }
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            self.assertTrue(_library_exploration_policy(events)["pass"])

    def test_library_exploration_policy_rejects_probe_and_path_discovery(self) -> None:
        for command in (
            "lean Probe.lean",
            'ls "$LEAN_PATH"',
            "env | sed -n /LEAN_PATH/p",
        ):
            with self.subTest(command=command), tempfile.TemporaryDirectory() as raw:
                events = Path(raw) / "events.jsonl"
                events.write_text(
                    json.dumps(
                        {
                            "params": {
                                "item": {
                                    "type": "commandExecution",
                                    "command": command,
                                }
                            }
                        }
                    )
                    + "\n",
                    encoding="utf-8",
                )
                self.assertFalse(_library_exploration_policy(events)["pass"])

    def test_packet_olean_runtime_contains_only_import_closure(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "source" / "NumStability"
            olean = root / "olean"
            (source / "A").mkdir(parents=True)
            (source / "Core").mkdir(parents=True)
            (source / "A" / "Selected.lean").write_text(
                "import NumStability.Core.Base\nimport Mathlib\n",
                encoding="utf-8",
            )
            (source / "Core" / "Base.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            for module, payload in (
                ("NumStability.A.Selected", b"selected"),
                ("NumStability.Core.Base", b"base"),
                ("NumStability.Hidden", b"hidden"),
            ):
                path = olean / Path(*module.split(".")).with_suffix(".olean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(payload)
            composition = {
                "retrieved_roots": [
                    {
                        "declaration": {
                            "name": "NumStability.selected",
                            "module": "NumStability.A.Selected",
                        },
                        "dependencies": [],
                    }
                ]
            }
            destination = root / "runtime"
            manifest = _build_packet_olean_runtime(
                composition=composition,
                source_root=source,
                olean_root=olean,
                destination=destination,
            )
            self.assertEqual(
                manifest["closure_modules"],
                ["NumStability.A.Selected", "NumStability.Core.Base"],
            )
            self.assertTrue(
                (destination / "NumStability" / "A" / "Selected.olean").is_file()
            )
            self.assertFalse(
                (destination / "NumStability" / "Hidden.olean").exists()
            )


if __name__ == "__main__":
    unittest.main()
