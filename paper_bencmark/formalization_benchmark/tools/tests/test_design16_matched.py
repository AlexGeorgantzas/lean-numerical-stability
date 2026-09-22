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
    _packet_treatment_allowlist,
    _parse_signature_interface_report,
    _parse_signature_render_report,
    _signature_render_source,
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
        for source in (
            "import\n  NumStability.Hidden\n",
            "import /- hidden syntax -/ NumStability.Hidden\n",
        ):
            with self.subTest(source=source):
                result = _treatment_interface_check(
                    candidate_text=source,
                    composition=composition,
                    private_dossier=private,
                )
                self.assertFalse(result["pass"])
                self.assertEqual(result["noncanonical_import_lines"], [1])

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

    def test_treatment_interface_allows_frozen_signature_closure_only(self) -> None:
        composition = {
            "retrieved_roots": [
                {
                    "declaration": {
                        "name": "NumStability.fl_rootProductEval_forward_error_bound",
                        "module": "NumStability.RootProduct",
                    },
                    "dependencies": [],
                }
            ],
            "signature_interface": {
                "schema_version": "formalization-design17-signature-interface-1",
                "seed_declarations": [
                    {
                        "name": "NumStability.fl_rootProductEval_forward_error_bound",
                        "module": "NumStability.RootProduct",
                        "kind": "theorem",
                        "readable_signature": (
                            "NumStability.fl_rootProductEval_forward_error_bound : True"
                        ),
                    }
                ],
                "direct_type_declarations": [
                    {
                        "name": "NumStability.FPModel",
                        "module": "NumStability.FloatingPoint",
                    },
                    {
                        "name": "NumStability.FPModel.u",
                        "module": "NumStability.FloatingPoint",
                    },
                    {
                        "name": "NumStability.gamma",
                        "module": "NumStability.Gamma",
                    },
                    {
                        "name": "NumStability.gammaValid",
                        "module": "NumStability.Gamma",
                    },
                ],
                "allowed_declarations": [
                    "NumStability.FPModel",
                    "NumStability.FPModel.u",
                    "NumStability.fl_rootProductEval_forward_error_bound",
                    "NumStability.gamma",
                    "NumStability.gammaValid",
                ],
            },
        }
        names = [
            "NumStability.FPModel",
            "NumStability.FPModel.u",
            "NumStability.gamma",
            "NumStability.gammaValid",
            "NumStability.hidden_same_module_result",
        ]
        private = {
            "raw_semantic_report": {
                "dependencies": [
                    {
                        "name": name,
                        "owner_module": (
                            "NumStability.RootProduct"
                            if name.endswith("hidden_same_module_result")
                            else "NumStability.Signature"
                        ),
                    }
                    for name in names
                ],
                "edges": [
                    {"parent": "HighamBenchCandidate.target", "child": name}
                    for name in names
                ],
            }
        }
        result = _treatment_interface_check(
            candidate_text="import NumStability.RootProduct\n",
            composition=composition,
            private_dossier=private,
        )
        self.assertEqual(
            result["forbidden_direct_declarations"],
            ["NumStability.hidden_same_module_result"],
        )
        self.assertIn("NumStability.FPModel", result["allowed_declarations"])
        self.assertFalse(result["pass"])

    def test_h5_one_hop_elaborated_interface_is_exact_and_nonrecursive(self) -> None:
        seed_names = [
            "NumStability.fl_rootProductEvalFrom_forward_error_bound",
            "NumStability.fl_rootProductEval_forward_error_bound",
            "NumStability.Ch14RectProductTree.roundedEval_RectMatProdError_gamma_operationBudget",
            "NumStability.fl_rootProductEvalFrom",
            "NumStability.rootProductEvalFrom",
            "NumStability.fl_rootProductEval",
            "NumStability.rootProductEval",
            "NumStability.gammaValid_mono",
            "NumStability.gamma_mono",
            "NumStability.gamma_nonneg",
            "NumStability.Ch14RectProductTree.RectMatProdError",
            "NumStability.Ch14RectProductTree.operationBudget",
        ]
        exposed = [
            {"name": name, "module": "NumStability.H5.Packet"}
            for name in seed_names
        ]
        direct = [
            ("NumStability.FPModel", "NumStability.Core.FP", "inductive"),
            ("NumStability.gamma", "NumStability.Core.Gamma", "def"),
            ("NumStability.gammaValid", "NumStability.Core.Gamma", "def"),
            (
                "NumStability.Ch14RectProductTree",
                "NumStability.Chapter14",
                "inductive",
            ),
            (
                "NumStability.Ch14RectProductTree.exactAbsProduct",
                "NumStability.Chapter14",
                "def",
            ),
            (
                "NumStability.Ch14RectProductTree.exactEval",
                "NumStability.Chapter14",
                "def",
            ),
            (
                "NumStability.Ch14RectProductTree.roundedEval",
                "NumStability.Chapter14",
                "def",
            ),
        ]
        rows = ["format\t2"]
        rows.extend(
            f"seed\t{name}\tNumStability.H5.Packet\ttheorem"
            for name in seed_names
        )
        rows.extend(
            f"direct\t{seed_names[index]}\t{name}\t{module}\t{kind}"
            for index, (name, module, kind) in enumerate(direct)
        )
        rows.append(f"summary\t{len(seed_names)}\t{len(direct)}")
        interface = _parse_signature_interface_report("\n".join(rows) + "\n", exposed)
        self.assertEqual(
            {item["name"] for item in interface["direct_type_declarations"]},
            {name for name, _module, _kind in direct},
        )

        composition = {
            "retrieved_roots": [
                {
                    "declaration": exposed[0],
                    "dependencies": exposed[1:],
                }
            ],
            "signature_interface": interface,
        }
        allowed, allowed_imports = _packet_treatment_allowlist(composition)
        self.assertEqual(
            allowed,
            set(seed_names) | {name for name, _module, _kind in direct},
        )
        self.assertEqual(allowed_imports, {"NumStability.H5.Packet"})
        excluded = {
            "NumStability.FPModel.fl_mul",
            "NumStability.FPModel.fl_sub",
            "NumStability.Ch14RectProductTree.orderCoefficient",
            "NumStability.rectMatMul",
            "NumStability.unrelated_same_closure_result",
        }
        private = {
            "raw_semantic_report": {
                "dependencies": [
                    {"name": name, "owner_module": "NumStability.SomeOwner"}
                    for name in sorted(allowed | excluded)
                ],
                "edges": [
                    {"parent": "HighamBenchCandidate.target", "child": name}
                    for name in sorted(allowed | excluded)
                ],
            }
        }
        checked = _treatment_interface_check(
            candidate_text="import NumStability.H5.Packet\n",
            composition=composition,
            private_dossier=private,
        )
        self.assertEqual(
            set(checked["forbidden_direct_declarations"]), excluded
        )
        self.assertFalse(checked["pass"])

    def test_signature_interface_identity_fails_closed(self) -> None:
        base = {
            "retrieved_roots": [
                {
                    "declaration": {
                        "name": "NumStability.allowed",
                        "module": "NumStability.Allowed",
                    },
                    "dependencies": [],
                }
            ],
            "signature_interface": {
                "schema_version": "formalization-design17-signature-interface-1",
                "seed_declarations": [
                    {
                        "name": "NumStability.allowed",
                        "module": "NumStability.Allowed",
                        "kind": "theorem",
                        "readable_signature": "NumStability.allowed : True",
                    }
                ],
                "direct_type_declarations": [],
                "allowed_declarations": ["NumStability.allowed"],
            },
        }
        for mutation in ("schema", "allowlist"):
            composition = json.loads(json.dumps(base))
            if mutation == "schema":
                composition["signature_interface"]["schema_version"] = "bogus"
            else:
                composition["signature_interface"]["allowed_declarations"] = [
                    "NumStability.allowed",
                    "NumStability.hidden",
                ]
            with self.subTest(mutation=mutation), self.assertRaises(BenchmarkError):
                _packet_treatment_allowlist(composition)

    def test_r0_mathlib_seed_has_empty_treatment_allowlist(self) -> None:
        exposed = [
            {
                "name": "Mathlib.Analysis.someBound",
                "module": "Mathlib.Analysis.Bounds",
            }
        ]
        interface = _parse_signature_interface_report(
            "format\t2\n"
            "seed\tMathlib.Analysis.someBound\tMathlib.Analysis.Bounds\t"
            "theorem\n"
            "summary\t1\t0\n",
            exposed,
        )
        self.assertEqual(
            interface["allowed_declarations"], ["Mathlib.Analysis.someBound"]
        )
        composition = {
            "retrieved_roots": [
                {"declaration": exposed[0], "dependencies": []}
            ],
            "signature_interface": interface,
        }
        self.assertEqual(_packet_treatment_allowlist(composition), (set(), set()))

    def test_signature_render_uses_framed_command_frontend_output(self) -> None:
        exposed = [
            {
                "name": "NumStability.sample",
                "module": "NumStability.Sample",
            }
        ]
        source = _signature_render_source(exposed).decode("utf-8")
        self.assertIn("#check NumStability.sample", source)
        self.assertNotIn("ppExpr", source)
        output = (
            "HIGHAMBENCH_SIGNATURE_BEGIN\tNumStability.sample\n"
            "NumStability.sample (roots : List ℝ) :\n"
            "  2 * roots.length ≤ roots.length - 1\n"
            "HIGHAMBENCH_SIGNATURE_END\tNumStability.sample\n"
        )
        self.assertEqual(
            _parse_signature_render_report(output, exposed),
            {
                "NumStability.sample": (
                    "NumStability.sample (roots : List ℝ) :\n"
                    "  2 * roots.length ≤ roots.length - 1"
                )
            },
        )
        with self.assertRaises(BenchmarkError):
            _parse_signature_render_report(
                "unframed warning\n" + output, exposed
            )

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
            (source / "Types").mkdir(parents=True)
            (source / "A" / "Selected.lean").write_text(
                "import NumStability.Core.Base\n"
                "import NumStability.Types.FP\n"
                "import Mathlib\n",
                encoding="utf-8",
            )
            (source / "Core" / "Base.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            (source / "Types" / "FP.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            for module, payload in (
                ("NumStability.A.Selected", b"selected"),
                ("NumStability.Core.Base", b"base"),
                ("NumStability.Types.FP", b"fp"),
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
                ],
                "signature_interface": {
                    "schema_version": "formalization-design17-signature-interface-1",
                    "seed_declarations": [
                        {
                            "name": "NumStability.selected",
                            "module": "NumStability.A.Selected",
                            "kind": "theorem",
                            "readable_signature": "NumStability.selected : True",
                        }
                    ],
                    "direct_type_declarations": [
                        {
                            "name": "NumStability.FPModel",
                            "module": "NumStability.Types.FP",
                        },
                    ],
                    "allowed_declarations": [
                        "NumStability.FPModel",
                        "NumStability.selected",
                    ],
                },
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
                [
                    "NumStability.A.Selected",
                    "NumStability.Core.Base",
                    "NumStability.Types.FP",
                ],
            )
            self.assertEqual(
                manifest["signature_interface_modules"],
                ["NumStability.Types.FP"],
            )
            self.assertEqual(
                manifest["selected_modules"], ["NumStability.A.Selected"]
            )
            self.assertTrue(
                (destination / "NumStability" / "A" / "Selected.olean").is_file()
            )
            self.assertFalse(
                (destination / "NumStability" / "Hidden.olean").exists()
            )


if __name__ == "__main__":
    unittest.main()
