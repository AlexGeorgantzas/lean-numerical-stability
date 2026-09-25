from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from types import SimpleNamespace
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from audit_controller import (  # noqa: E402
    AuditController,
    _validate_adjudication,
    _validate_judgment,
    _validate_translation,
)
from codex_driver import ProviderCapabilityError  # noqa: E402
from common import BenchmarkError, sha256_file  # noqa: E402


PAPER_HASH = "a" * 64
SEMANTIC_HASH = "b" * 64


class FakeAuditController(AuditController):
    def __init__(self, outputs: list[dict]):
        self.outputs: dict[str, list[dict]] = {}
        for output in outputs:
            self.outputs.setdefault(str(output["role"]), []).append(output)
        self.roles: list[str] = []
        self._fake_lock = threading.Lock()
        self.forbidden_feedback_identifiers: set[str] = set()

    def _fresh_role(self, *, role, validate, **kwargs):
        del kwargs
        with self._fake_lock:
            self.roles.append(role)
            value = self.outputs[role].pop(0)
        validate(value)
        return value, {
            "role": role,
            "retry": 1,
            "wall_seconds": 0.1,
            "usage": {
                "input_tokens": 1,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 1,
                "reasoning_output_tokens": 0,
                "total_tokens": 2,
            },
            "tries": [{"usage_complete": True}],
            "thread_id": "fresh",
        }


DEPENDENCIES = [("D001", "Nat")]


def translation(*, unclear_dependency: bool = False) -> dict:
    return {
        "role": "blind-translation",
        "semantic_sha256": SEMANTIC_HASH,
        "dependency_coverage": [
            {
                "id": "D001",
                "name": "Nat",
                "meaning": "The natural-number type.",
                "effect_on_target": "Indexes the finite problem dimension.",
                "status": "unclear" if unclear_dependency else "understood",
            }
        ],
        "translation": {
            "binders": ["n is a natural number."],
            "hypotheses": [],
            "conclusions": ["The stated error bound holds."],
            "mathematical_definitions": [],
            "proposition_plain_english": (
                "For every admissible input, the stated error bound holds."
            ),
        },
        "ambiguities": [],
        "vacuity_risks": [],
    }


def semantic_checklist(*, direct: bool) -> list[dict]:
    evidence_field = "candidate_evidence" if direct else "translation_evidence"
    return [
        {
            "id": f"S{index:02d}",
            "status": "pass",
            "paper_evidence": "The selected source requirement is explicit.",
            evidence_field: "The corresponding candidate content is explicit.",
            "reasoning": "The two agree for this check.",
        }
        for index in range(1, 17)
    ]


def judgment(role: str, *, faithful: bool = True) -> dict:
    value = {
        "role": role,
        "paper_sha256": PAPER_HASH,
        "candidate_semantic_sha256": SEMANTIC_HASH,
        "semantic_checklist": semantic_checklist(direct=role == "direct-judge"),
        "implications": {
            "candidate_implies_source": {
                "verdict": "yes" if faithful else "no",
                "reasoning": "All source requirements follow." if faithful else "One is missing.",
            },
            "source_implies_candidate": {
                "verdict": "yes",
                "reasoning": "The source entails the candidate statement.",
            },
        },
        "classification": "faithful-equivalent" if faithful else "unfaithful-weaker",
        "accepted": faithful,
        "requires_adjudication": False,
        "mismatches": [] if faithful else [
            {
                "paper_requirement": "The result covers every admissible input.",
                "candidate_mismatch": "The candidate covers only a proper subset.",
                "severity": "major",
            }
        ],
        "uncertainties": [],
        "rationale": "All material requirements agree.",
    }
    if role == "direct-judge":
        value["dependency_coverage"] = [
            {
                "id": "D001",
                "name": "Nat",
                "interpretation": "The natural-number type.",
                "effect_on_target": "Indexes the problem dimension.",
                "paper_match": "Matches the source's dimension parameter.",
                "status": "pass",
            }
        ]
    return value


def unfaithful_adjudication(trigger: list[str]) -> dict:
    return {
        "role": "adjudicator",
        "paper_sha256": PAPER_HASH,
        "candidate_semantic_sha256": SEMANTIC_HASH,
        "trigger": trigger,
        "resolved_items": [
            {
                "item": trigger[0],
                "resolution": "The uncertainty exposes missing source-domain coverage.",
                "primary_evidence": "The source includes every no-overflow execution.",
            }
        ],
        "implications": {
            "candidate_implies_source": {
                "verdict": "no",
                "reasoning": "The candidate has an unsupported extra premise.",
            },
            "source_implies_candidate": {
                "verdict": "yes",
                "reasoning": "The full source result entails the restricted case.",
            },
        },
        "classification": "unfaithful-weaker",
        "verdict": "unfaithful",
        "mismatches": [
            {
                "paper_requirement": "The result covers every no-overflow execution.",
                "candidate_mismatch": (
                    "Successful partial operations are an extra premise without a "
                    "bridge from no overflow."
                ),
                "severity": "major",
            }
        ],
        "remaining_uncertainties": [],
        "rationale": "The candidate does not establish the paper's full domain coverage.",
    }


class AuditControllerPolicyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.paper = self.root / "paper.pdf"
        self.packet = self.root / "source_packet.md"
        self.dossier = self.root / "dossier.json"
        self.paper.write_bytes(b"%PDF synthetic")
        self.packet.write_text("source contract", encoding="utf-8")
        self.dossier.write_text(
            json.dumps(
                {
                    "semantic_sha256": SEMANTIC_HASH,
                    "dependencies": [{"id": "D001", "name": "Nat"}],
                }
            ),
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_vacuous_material_implication_is_unfaithful(self) -> None:
        for role in ("direct-judge", "roundtrip-judge"):
            with self.subTest(role=role):
                candidate = judgment(role)
                candidate["semantic_checklist"][-1]["status"] = "fail"
                candidate["implications"]["source_implies_candidate"]["verdict"] = "no"
                candidate["classification"] = "unfaithful-different"
                candidate["accepted"] = False
                candidate["mismatches"] = [{
                    "paper_requirement": "The source holds on an admissible case.",
                    "candidate_mismatch": "The candidate is inconsistent there.",
                    "severity": "major",
                }]
                _validate_judgment(
                    candidate,
                    role=role,
                    paper_sha256=PAPER_HASH,
                    semantic_sha256=SEMANTIC_HASH,
                    dependencies=DEPENDENCIES,
                )
                candidate["semantic_checklist"][-1]["status"] = "pass"
                with self.assertRaisesRegex(BenchmarkError, "classification contradicts"):
                    _validate_judgment(
                        candidate,
                        role=role,
                        paper_sha256=PAPER_HASH,
                        semantic_sha256=SEMANTIC_HASH,
                        dependencies=DEPENDENCIES,
                    )

    def run_audit(self, controller: FakeAuditController, name: str) -> dict:
        return controller.run(
            task_id="P01-T2",
            paper_path=self.paper,
            paper_sha256=PAPER_HASH,
            source_packet=self.packet,
            dossier_path=self.dossier,
            semantic_sha256=SEMANTIC_HASH,
            audit_root=self.root / name,
        )

    def test_clean_independent_agreement_accepts_without_adjudication(self) -> None:
        controller = FakeAuditController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "clean")
        self.assertTrue(decision["accepted"])
        self.assertFalse(decision["adjudicated"])
        self.assertEqual(
            set(controller.roles),
            {"blind-translation", "direct-judge", "roundtrip-judge"},
        )

    def test_unclear_dependency_forces_adjudication_and_domain_gap_gets_feedback(self) -> None:
        trigger = ["blind dependency interpretation remains unclear"]
        controller = FakeAuditController(
            [
                translation(unclear_dependency=True),
                judgment("direct-judge"),
                judgment("roundtrip-judge"),
                unfaithful_adjudication(trigger),
            ]
        )
        decision = self.run_audit(controller, "ambiguous")
        self.assertFalse(decision["accepted"])
        self.assertTrue(decision["adjudicated"])
        self.assertEqual(decision["verdict"], "unfaithful")
        self.assertFalse(decision["audit_incident"])
        self.assertEqual(
            decision["repair_feedback"]["issues"][0]["missing_paper_requirement"],
            "The result covers every no-overflow execution.",
        )
        self.assertEqual(controller.roles[-1], "adjudicator")

    def test_unclear_is_not_a_final_semantic_verdict(self) -> None:
        trigger = ["direct and round-trip classifications differ"]
        malformed_adjudication = unfaithful_adjudication(trigger)
        malformed_adjudication["verdict"] = "unclear"
        malformed_adjudication["mismatches"] = []
        malformed_adjudication["remaining_uncertainties"] = [
            "A domain bridge is missing."
        ]
        with self.assertRaisesRegex(BenchmarkError, "semantic contract"):
            _validate_adjudication(
                malformed_adjudication,
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                trigger=trigger,
            )

    def test_local_validator_rejects_malformed_nested_mismatch(self) -> None:
        malformed = judgment("direct-judge")
        malformed["mismatches"] = ["not-an-object"]
        with self.assertRaisesRegex(BenchmarkError, "semantic contract"):
            _validate_judgment(
                malformed,
                role="direct-judge",
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                dependencies=DEPENDENCIES,
            )

    def test_adjudicator_cannot_leave_uncertainty_on_unfaithful_verdict(self) -> None:
        trigger = ["direct and round-trip classifications differ"]
        malformed_adjudication = unfaithful_adjudication(trigger)
        malformed_adjudication["remaining_uncertainties"] = [
            "The disputed domain relationship remains unresolved."
        ]
        with self.assertRaisesRegex(BenchmarkError, "unresolved uncertainty"):
            _validate_adjudication(
                malformed_adjudication,
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                trigger=trigger,
            )

    def test_dependency_identity_is_ordered_id_not_descriptive_name(self) -> None:
        translated = translation()
        translated["dependency_coverage"][0]["name"] = "Natural-number dimension"
        _validate_translation(translated, SEMANTIC_HASH, DEPENDENCIES)

        judged = judgment("direct-judge")
        judged["dependency_coverage"][0]["name"] = "Natural-number dimension"
        _validate_judgment(
            judged,
            role="direct-judge",
            paper_sha256=PAPER_HASH,
            semantic_sha256=SEMANTIC_HASH,
            dependencies=DEPENDENCIES,
        )

        judged["dependency_coverage"][0]["id"] = "D002"
        with self.assertRaisesRegex(BenchmarkError, "does not match D001"):
            _validate_judgment(
                judged,
                role="direct-judge",
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                dependencies=DEPENDENCIES,
            )

    def test_unfaithful_requires_concrete_mismatch(self) -> None:
        malformed = judgment("roundtrip-judge", faithful=False)
        malformed["mismatches"] = []
        with self.assertRaisesRegex(BenchmarkError, "concrete mismatch"):
            _validate_judgment(
                malformed,
                role="roundtrip-judge",
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                dependencies=DEPENDENCIES,
            )

    def test_faithful_judgment_cannot_hide_a_failed_semantic_check(self) -> None:
        malformed = judgment("direct-judge")
        malformed["semantic_checklist"][3]["status"] = "fail"
        with self.assertRaisesRegex(BenchmarkError, "accepted despite"):
            _validate_judgment(
                malformed,
                role="direct-judge",
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                dependencies=DEPENDENCIES,
            )

    def test_adjudicator_must_resolve_every_trigger_in_order(self) -> None:
        trigger = [
            "direct and round-trip classifications differ",
            "direct semantic check remains unclear",
        ]
        malformed = unfaithful_adjudication(trigger)
        with self.assertRaisesRegex(BenchmarkError, "omitted one or more"):
            _validate_adjudication(
                malformed,
                paper_sha256=PAPER_HASH,
                semantic_sha256=SEMANTIC_HASH,
                trigger=trigger,
            )

    def test_failed_audit_role_telemetry_is_sealed_into_incident(self) -> None:
        audit_root = self.root / "failed"
        role_root = audit_root / "roles" / "direct-judge"
        role_root.mkdir(parents=True)
        telemetry_path = role_root / "telemetry.json"
        telemetry_path.write_text(
            json.dumps(
                {
                    "role": "direct-judge",
                    "tries": [
                        {
                            "usage": {
                                "input_tokens": 4,
                                "cached_input_tokens": 1,
                                "cache_write_input_tokens": 0,
                                "output_tokens": 2,
                                "reasoning_output_tokens": 1,
                                "total_tokens": 6,
                            },
                            "usage_complete": True,
                        }
                    ],
                    "usage": {
                        "input_tokens": 4,
                        "cached_input_tokens": 1,
                        "cache_write_input_tokens": 0,
                        "output_tokens": 2,
                        "reasoning_output_tokens": 1,
                        "total_tokens": 6,
                    },
                }
            ),
            encoding="utf-8",
        )
        controller = FakeAuditController([])
        incident = controller.seal_incident(
            audit_root=audit_root,
            task_id="P01-T2",
            paper_sha256=PAPER_HASH,
            semantic_sha256=SEMANTIC_HASH,
            error="synthetic auditor failure",
            wall_seconds=1.25,
        )
        incident_path = audit_root / "incident.json"
        self.assertEqual(incident["usage"]["total_tokens"], 6)
        self.assertTrue(incident["usage_complete"])
        self.assertEqual(
            incident["auditor_telemetry"][0]["sha256"], sha256_file(telemetry_path)
        )
        self.assertTrue(incident_path.is_file())

    def test_successful_decision_detects_mutated_underlying_evidence(self) -> None:
        controller = FakeAuditController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        self.run_audit(controller, "mutable")
        judgment_path = self.root / "mutable" / "direct_judgment.json"
        judgment_path.chmod(0o600)
        judgment_path.write_text("{}\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkError, "nonempty or incomplete"):
            self.run_audit(FakeAuditController([]), "mutable")

    def test_blind_and_direct_roles_begin_concurrently(self) -> None:
        barrier = threading.Barrier(2)
        started: set[str] = set()
        lock = threading.Lock()

        class ConcurrentStartController(FakeAuditController):
            def _fresh_role(inner_self, *, role, **kwargs):
                if role in {"blind-translation", "direct-judge"}:
                    with lock:
                        started.add(role)
                    barrier.wait(timeout=2)
                return super()._fresh_role(role=role, **kwargs)

        controller = ConcurrentStartController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "concurrent-start")
        self.assertTrue(decision["accepted"])
        self.assertEqual(started, {"blind-translation", "direct-judge"})

    def test_roundtrip_waits_for_frozen_translation_and_overlaps_direct(self) -> None:
        direct_started = threading.Event()
        roundtrip_started = threading.Event()
        direct_completed = threading.Event()
        saw_frozen_translation = threading.Event()

        class CriticalPathController(FakeAuditController):
            def _fresh_role(inner_self, *, role, workspace, **kwargs):
                if role == "blind-translation":
                    self.assertTrue(direct_started.wait(timeout=2))
                elif role == "direct-judge":
                    direct_started.set()
                    self.assertTrue(roundtrip_started.wait(timeout=2))
                elif role == "roundtrip-judge":
                    frozen = workspace / "blind_translation.json"
                    self.assertTrue(frozen.is_file())
                    self.assertEqual(
                        json.loads(frozen.read_text(encoding="utf-8")),
                        translation(),
                    )
                    saw_frozen_translation.set()
                    roundtrip_started.set()
                result = super()._fresh_role(
                    role=role, workspace=workspace, **kwargs
                )
                if role == "direct-judge":
                    direct_completed.set()
                return result

        controller = CriticalPathController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "roundtrip-gate")
        self.assertTrue(decision["accepted"])
        self.assertTrue(saw_frozen_translation.is_set())
        self.assertTrue(direct_completed.is_set())

    def test_adjudicator_starts_only_after_both_judgments_are_frozen(self) -> None:
        trigger = ["direct and round-trip classifications differ"]
        adjudicator_checked = threading.Event()

        class AdjudicationGateController(FakeAuditController):
            def _fresh_role(inner_self, *, role, workspace, **kwargs):
                if role == "adjudicator":
                    self.assertTrue((workspace / "direct_judgment.json").is_file())
                    self.assertTrue((workspace / "roundtrip_judgment.json").is_file())
                    self.assertTrue((workspace / "blind_translation.json").is_file())
                    adjudicator_checked.set()
                return super()._fresh_role(
                    role=role, workspace=workspace, **kwargs
                )

        controller = AdjudicationGateController(
            [
                translation(),
                judgment("direct-judge"),
                judgment("roundtrip-judge", faithful=False),
                unfaithful_adjudication(trigger),
            ]
        )
        decision = self.run_audit(controller, "adjudication-gate")
        self.assertTrue(decision["adjudicated"])
        self.assertTrue(adjudicator_checked.is_set())

    def test_role_failure_drains_inflight_branch_before_return(self) -> None:
        direct_started = threading.Event()
        direct_completed = threading.Event()

        class DrainingController(FakeAuditController):
            def _fresh_role(inner_self, *, role, **kwargs):
                if role == "blind-translation":
                    self.assertTrue(direct_started.wait(timeout=2))
                    raise BenchmarkError("synthetic blind failure")
                if role == "direct-judge":
                    direct_started.set()
                    time.sleep(0.05)
                    result = super()._fresh_role(role=role, **kwargs)
                    direct_completed.set()
                    return result
                return super()._fresh_role(role=role, **kwargs)

        controller = DrainingController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        with self.assertRaisesRegex(BenchmarkError, "synthetic blind failure"):
            self.run_audit(controller, "drained-failure")
        self.assertTrue(direct_completed.is_set())
        schedule = json.loads(
            (
                self.root
                / "drained-failure"
                / "roles"
                / "direct-judge"
                / "schedule.json"
            ).read_text(encoding="utf-8")
        )
        self.assertTrue(schedule["completed"])

    def test_completion_order_does_not_change_telemetry_order_or_usage(self) -> None:
        release_direct = threading.Event()

        class ReverseCompletionController(FakeAuditController):
            def _fresh_role(inner_self, *, role, **kwargs):
                if role == "direct-judge":
                    self.assertTrue(release_direct.wait(timeout=2))
                elif role == "roundtrip-judge":
                    release_direct.set()
                value, telemetry = super()._fresh_role(role=role, **kwargs)
                telemetry["thread_id"] = f"thread-{role}"
                return value, telemetry

        controller = ReverseCompletionController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "logical-telemetry")
        role_telemetry = decision["auditor_telemetry"]
        self.assertEqual(
            [item["role"] for item in role_telemetry],
            ["blind-translation", "direct-judge", "roundtrip-judge"],
        )
        self.assertEqual(
            sum(item["usage"]["total_tokens"] for item in role_telemetry),
            6,
        )

    def test_parallel_roles_keep_distinct_workspaces_and_threads(self) -> None:
        workspaces: dict[str, Path] = {}
        lock = threading.Lock()

        class IsolatedController(FakeAuditController):
            def _fresh_role(inner_self, *, role, workspace, **kwargs):
                with lock:
                    workspaces[role] = workspace
                value, telemetry = super()._fresh_role(
                    role=role, workspace=workspace, **kwargs
                )
                telemetry["thread_id"] = f"isolated-{role}"
                return value, telemetry

        controller = IsolatedController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "role-isolation")
        self.assertEqual(len(set(workspaces.values())), 3)
        self.assertEqual(
            len(
                {
                    item["thread_id"]
                    for item in decision["auditor_telemetry"]
                }
            ),
            3,
        )

    def test_audit_wall_records_parallel_critical_path_and_stays_excluded(self) -> None:
        class TimedController(FakeAuditController):
            def _fresh_role(inner_self, *, role, **kwargs):
                time.sleep(0.08)
                return super()._fresh_role(role=role, **kwargs)

        controller = TimedController(
            [translation(), judgment("direct-judge"), judgment("roundtrip-judge")]
        )
        decision = self.run_audit(controller, "critical-path-timing")
        role_wall_sum = sum(
            item["schedule"]["wall_seconds"]
            for item in decision["auditor_telemetry"]
        )
        self.assertLess(decision["audit_wall_seconds"], role_wall_sum)
        self.assertTrue(decision["auditor_tokens_excluded_from_benchmark"])
        self.assertEqual(decision["execution_plan"]["maximum_concurrent_roles"], 2)

    def test_provider_capability_failure_never_retries_a_fresh_auditor(self) -> None:
        for raises_early in (True, False):
            with self.subTest(raises_early=raises_early):
                calls: list[int] = []

                class IncompatibleDriver:
                    def __init__(self, **kwargs):
                        del kwargs

                    def run_turn(self, **kwargs):
                        del kwargs
                        calls.append(1)
                        if raises_early:
                            raise ProviderCapabilityError("single-agent gate missing")
                        return SimpleNamespace(
                            failure_kind="provider_capability_violation",
                            exit_code=70,
                            timed_out=False,
                            final_message="",
                            wall_seconds=0.01,
                            usage={"total_tokens": 1},
                            usage_complete=False,
                            thread_id="unsafe-thread",
                        )

                    def close(self, **kwargs):
                        del kwargs

                controller = AuditController(
                    codex_binary=self.root / "codex",
                    auth_file=self.root / "auth",
                    model="test",
                    reasoning_effort="high",
                    timeout_seconds=10,
                    maximum_infrastructure_retries=3,
                )
                role_root = self.root / f"capability-{raises_early}"
                with mock.patch("audit_controller.CodexDriver", IncompatibleDriver):
                    with self.assertRaisesRegex(
                        ProviderCapabilityError, "provider capability incompatibility"
                    ):
                        controller._fresh_role(
                            role="direct-judge",
                            prompt="test",
                            workspace=self.root,
                            role_root=role_root,
                            schema=self.root / "schema.json",
                            validate=lambda value: None,
                        )
                self.assertEqual(len(calls), 1)
                telemetry = json.loads(
                    (role_root / "telemetry.json").read_text(encoding="utf-8")
                )
                self.assertEqual(len(telemetry["tries"]), 1)


if __name__ == "__main__":
    unittest.main()
