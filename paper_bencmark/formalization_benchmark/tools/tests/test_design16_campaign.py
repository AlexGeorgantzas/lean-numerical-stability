from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import (  # noqa: E402
    BenchmarkError,
    file_tree_fingerprint,
    sha256_file,
    treatment_free_runtime_manifest,
    tree_manifest,
)
from deployment import Deployment  # noqa: E402
import design16_campaign as campaign_module  # noqa: E402
from design16_campaign import (  # noqa: E402
    EXPECTED_STRATA,
    EXPECTED_TASKS,
    _append_record,
    _read_journal,
    load_plan,
    run_campaign,
)


CONFIG = ROOT / "config.json"
READINESS = ROOT / "design16" / "higham13_readiness.json"


def _git_runner(root: Path) -> tuple[Path, str, str]:
    repository = root / "repo"
    repository.mkdir()
    runner = repository / "fake_runner.py"
    runner.write_text(
        """#!/usr/bin/env python3
import argparse, json
from pathlib import Path
p = argparse.ArgumentParser()
names = (
    'deployment', 'mathlib-atlas', 'task-id', 'condition-order',
    'output-root', 'model', 'reasoning-effort', 'time-limit-seconds',
    'validation-timeout-seconds', 'root-limit', 'dependency-limit',
    'maximum-packet-bytes', 'submission-limit', 'audit-model',
    'audit-reasoning-effort', 'audit-timeout-seconds',
    'audit-infrastructure-retries',
)
for name in names:
    p.add_argument('--' + name, required=True)
a = p.parse_args()
root = Path(a.output_root)
root.mkdir(parents=True)
failed = a.task_id == 'H22-5'
prompt = root / 'prompt.txt'
prompt.write_text('frozen prompt')
prompt_sha = __import__('hashlib').sha256(prompt.read_bytes()).hexdigest()
condition_reports = {}
for condition in ('R0', 'R1'):
    condition_root = root / condition
    workspace = condition_root / 'workspace'
    source = workspace / 'source'
    source.mkdir(parents=True)
    candidate = workspace / 'Candidate.lean'
    candidate.write_text('theorem test : True := by trivial\\n')
    candidate_sha = __import__('hashlib').sha256(candidate.read_bytes()).hexdigest()
    library_api = workspace / 'LIBRARY_API.md'
    library_api.write_text('api')
    composition = condition_root / 'composition-packet.json'
    composition.write_text('{}')
    (source / 'paper.pdf').write_bytes(b'pdf')
    (source / 'task.md').write_text('task')
    (condition_root / 'validation.json').write_text(json.dumps({'pass': True}))
    report_condition = {
        'task_id': a.task_id,
        'condition': condition,
        'benchmark_object': 'FORMALIZED_STATEMENT_AND_COMPLETE_PROOF',
        'source_contract': 'complete-kernel-checked-proof',
        'faithfulness_status': 'NOT_AUDITED',
        'result_status': 'COMPILED_AND_INTEGRITY_VALIDATED',
        'validation_pass': True,
        'prompt_sha256': prompt_sha,
        'candidate_sha256': candidate_sha,
        'composition_packet_sha256': __import__('hashlib').sha256(composition.read_bytes()).hexdigest(),
        'library_api_sha256': __import__('hashlib').sha256(library_api.read_bytes()).hexdigest(),
        'source_packet_sha256': 'a' * 64,
    }
    (condition_root / 'report.json').write_text(json.dumps(report_condition))
    condition_reports[condition] = report_condition
report = {
    'task_id': a.task_id,
    'pair_status': 'PAIR_INCIDENT' if failed else 'COMPILED_UNAUDITED',
    'condition_order': a.condition_order.split(','),
    'conditions_run_sequentially': True,
    'benchmark_object': 'FORMALIZED_STATEMENT_AND_COMPLETE_PROOF',
    'source_contract': 'complete-kernel-checked-proof',
    'faithfulness_status': 'NOT_AUDITED',
    'prompt_sha256': prompt_sha,
    'source_packet_sha256': 'a' * 64,
    'source_pdf_sha256': __import__('hashlib').sha256(b'pdf').hexdigest(),
    'condition_reports': condition_reports,
}
(root / 'pair-report.json').write_text(json.dumps(report))
raise SystemExit(7 if failed else 0)
""",
        encoding="utf-8",
    )
    subprocess.run(["git", "init", "-q", str(repository)], check=True)
    subprocess.run(["git", "-C", str(repository), "add", "fake_runner.py"], check=True)
    subprocess.run(
        [
            "git",
            "-C",
            str(repository),
            "-c",
            "user.name=Test",
            "-c",
            "user.email=test@example.invalid",
            "commit",
            "-qm",
            "runner",
        ],
        check=True,
    )
    commit = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    return runner, commit, sha256_file(runner)


def _atlas(root: Path) -> Path:
    atlas = root / "mathlib-atlas"
    atlas.mkdir()
    declarations = atlas / "declarations.jsonl"
    declarations.write_text(
        json.dumps({"name": "Mathlib.sample", "module": "Mathlib"}) + "\n",
        encoding="utf-8",
    )
    (atlas / "atlas.json").write_text(
        json.dumps(
            {
                "schema_version": "numstability-library-atlas-2",
                "declaration_count": 1,
                "declarations_sha256": sha256_file(declarations),
            }
        ),
        encoding="utf-8",
    )
    return atlas


def _args(root: Path, *, dry_run: bool) -> argparse.Namespace:
    runner, commit, digest = _git_runner(root)
    return argparse.Namespace(
        deployment=root / "deployment.json",
        mathlib_atlas=_atlas(root),
        campaign_root=root / "campaign",
        runner=runner,
        runner_commit=commit,
        runner_sha256=digest,
        controller_commit=None,
        controller_sha256=None,
        config=CONFIG,
        readiness=READINESS,
        host_lock=root / "host.lock",
        model="gpt-5.6-sol",
        reasoning_effort="xhigh",
        time_limit_seconds=18000,
        validation_timeout_seconds=600,
        root_limit=3,
        dependency_limit=5,
        maximum_packet_bytes=48 * 1024,
        submission_limit=4,
        audit_model="gpt-6-astra",
        audit_reasoning_effort="high",
        audit_timeout_seconds=7200.0,
        audit_infrastructure_retries=2,
        max_new_tasks=None,
        wave_task_ids=None,
        enforce_titan_envelope=False,
        statement_only=False,
        dry_run=dry_run,
    )


def _deployment_fixture(root: Path) -> tuple[argparse.Namespace, Deployment, dict[str, Path]]:
    source_root = root / "library" / "source"
    library_source = source_root / "NumStability"
    library_source.mkdir(parents=True)
    source_file = library_source / "Fixture.lean"
    source_file.write_text("theorem fixture : True := by trivial\n", encoding="utf-8")
    (source_root / "NumStability.lean").write_text(
        "import NumStability.Fixture\n", encoding="utf-8"
    )
    library_olean = root / "library" / "olean"
    library_olean.mkdir(parents=True)
    olean_file = library_olean / "Fixture.olean"
    olean_file.write_bytes(b"synthetic olean")
    build_root = root / "library" / "build"
    build_root.mkdir(parents=True)
    build_output = build_root / "build-output.log"
    build_output.write_text("fixture build\n", encoding="utf-8")
    gnu_time = build_root / "gnu-time.txt"
    gnu_time.write_text("elapsed 1\n", encoding="utf-8")
    generated_output_tree = {
        "present": True,
        **file_tree_fingerprint(library_olean),
    }
    generated_olean = {
        "present": True,
        **file_tree_fingerprint(library_olean, suffix=".olean"),
    }
    build_record = build_root / "build-record.json"
    build_record.write_text(
        json.dumps(
            {
                "generated_output_tree": generated_output_tree,
                "generated_olean": generated_olean,
                "build_output": {
                    "relative_path": build_output.name,
                    "sha256": sha256_file(build_output),
                    "bytes": build_output.stat().st_size,
                },
                "gnu_time": {
                    "relative_path": gnu_time.name,
                    "sha256": sha256_file(gnu_time),
                    "bytes": gnu_time.stat().st_size,
                },
            }
        ),
        encoding="utf-8",
    )
    config = json.loads(CONFIG.read_text(encoding="utf-8"))
    library_snapshot = root / "library" / "snapshot.json"
    library_snapshot.write_text(
        json.dumps(
            {
                "schema_version": "numstability-formalization-snapshot-1",
                "commit": config["numstability_commit"],
                "source": tree_manifest(source_root),
                "olean": tree_manifest(library_olean),
                "build": tree_manifest(build_root),
            }
        ),
        encoding="utf-8",
    )

    toolchain = root / "toolchain"
    (toolchain / "bin").mkdir(parents=True)
    toolchain_file = toolchain / "bin" / "lean"
    toolchain_file.write_bytes(b"synthetic lean")
    (toolchain / "bin" / "lake").write_bytes(b"synthetic lake")
    packages = root / "packages"
    packages.mkdir()
    package_file = packages / "mathlib.olean"
    package_file.write_bytes(b"synthetic mathlib")
    runtime_snapshot = root / "runtime-snapshot.json"
    runtime_snapshot.write_text(
        json.dumps(
            {
                "schema_version": "formalization-runtime-snapshot-1",
                "lean_toolchain": config["lean_toolchain"],
                "mathlib_commit": config["mathlib_commit"],
                "toolchain": tree_manifest(toolchain),
                "packages": tree_manifest(packages),
                "condition_n_treatment_absence": treatment_free_runtime_manifest(
                    {"packages": packages, "toolchain": toolchain}
                ),
            }
        ),
        encoding="utf-8",
    )

    bin_root = root / "bin"
    bin_root.mkdir()
    codex = bin_root / "codex"
    code_mode_host = bin_root / "codex-code-mode-host"
    bwrap = bin_root / "bwrap"
    offline_shell = bin_root / "offline-shell"
    for path in (codex, code_mode_host, bwrap, offline_shell):
        path.write_bytes(path.name.encode("utf-8"))
    visible_runtime = root / "visible-system.json"
    visible_runtime.write_text("{}\n", encoding="utf-8")
    for directory in (root / "runs", root / "pdfs", root / "atlas"):
        directory.mkdir()
    auth = root / "auth.json"
    auth.write_text("{}\n", encoding="utf-8")
    deployment_path = root / "deployment.json"
    deployment_record = {
        "library_snapshot_record": str(library_snapshot),
        "library_snapshot_record_sha256": sha256_file(library_snapshot),
        "library_build_record": str(build_record),
        "library_build_record_sha256": sha256_file(build_record),
        "runtime_snapshot_record": str(runtime_snapshot),
        "runtime_snapshot_record_sha256": sha256_file(runtime_snapshot),
        "visible_system_runtime_record": str(visible_runtime),
        "visible_system_runtime_record_sha256": sha256_file(visible_runtime),
        "codex_binary_sha256": sha256_file(codex),
        "code_mode_host_sha256": sha256_file(code_mode_host),
        "bwrap_binary_sha256": sha256_file(bwrap),
        "offline_shell_sha256": sha256_file(offline_shell),
    }
    deployment_path.write_text(json.dumps(deployment_record), encoding="utf-8")
    deployment = Deployment(
        path=deployment_path,
        run_root=root / "runs",
        pdf_root=root / "pdfs",
        codex_binary=codex,
        auth_file=auth,
        bwrap_binary=bwrap,
        offline_shell=offline_shell,
        toolchain_root=toolchain,
        packages_root=packages,
        library_source=library_source,
        library_olean=library_olean,
        library_atlas=root / "atlas",
        library_snapshot_record=library_snapshot,
        runtime_snapshot_record=runtime_snapshot,
        strict_hardware=False,
    )
    args = argparse.Namespace(deployment=deployment_path, config=CONFIG)
    return args, deployment, {
        "source": source_file,
        "olean": olean_file,
        "toolchain": toolchain_file,
        "packages": package_file,
        "runtime_record": runtime_snapshot,
    }


def _rewind_last_terminal(campaign_root: Path) -> None:
    for name in ("campaign-state.jsonl", "campaign-summary.jsonl"):
        path = campaign_root / name
        lines = path.read_text(encoding="utf-8").splitlines()
        path.write_text("\n".join(lines[:-1]) + "\n", encoding="utf-8")


class Design16CampaignTests(unittest.TestCase):
    def setUp(self) -> None:
        closure = {"test_only_frozen_input_closure": True}
        closure["closure_sha256"] = campaign_module._canonical_hash(closure)
        self._closure_patch = patch.object(
            campaign_module,
            "_frozen_input_closure",
            return_value=closure,
        )
        self._closure_patch.start()

    def tearDown(self) -> None:
        self._closure_patch.stop()

    def test_plan_preserves_alternation_and_exact_strata(self) -> None:
        plan = load_plan(CONFIG, READINESS)
        self.assertEqual(tuple(item["task_id"] for item in plan), EXPECTED_TASKS)
        self.assertEqual(plan[0]["condition_order"], ["R1", "R0"])
        self.assertEqual(plan[1]["condition_order"], ["R0", "R1"])
        for left, right in zip(plan, plan[1:]):
            self.assertNotEqual(left["condition_order"], right["condition_order"])
        observed = {
            stratum: tuple(item["task_id"] for item in plan if item["stratum"] == stratum)
            for stratum in EXPECTED_STRATA
        }
        self.assertEqual(observed, EXPECTED_STRATA)

    def test_hash_chained_journal_detects_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "journal.jsonl"
            _append_record(path, {"event_type": "ONE"})
            _append_record(path, {"event_type": "TWO"})
            self.assertEqual(len(_read_journal(path)), 2)
            lines = path.read_text(encoding="utf-8").splitlines()
            first = json.loads(lines[0])
            first["event_type"] = "ALTERED"
            lines[0] = json.dumps(first, sort_keys=True, separators=(",", ":"))
            path.chmod(0o600)
            path.write_text("\n".join(lines) + "\n", encoding="utf-8")
            with self.assertRaises(BenchmarkError):
                _read_journal(path)

    def test_deployment_admission_verifies_every_frozen_runtime_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            args, deployment, mutable_paths = _deployment_fixture(Path(raw))
            with patch.object(campaign_module, "validate_build_record"):
                identity = campaign_module._verify_deployment_runtime(
                    args, deployment=deployment
                )
                self.assertEqual(
                    identity["schema_version"],
                    "formalization-design17-verified-deployment-runtime-1",
                )
                self.assertRegex(identity["identity_sha256"], r"^[0-9a-f]{64}$")
                self.assertEqual(
                    set(identity["library_trees"]), {"source", "olean", "build"}
                )
                self.assertEqual(
                    set(identity["runtime_trees"]), {"toolchain", "packages"}
                )
                for label in ("source", "olean", "toolchain", "packages"):
                    path = mutable_paths[label]
                    original = path.read_bytes()
                    path.write_bytes(original + b"drift")
                    with self.subTest(label=label):
                        with self.assertRaisesRegex(BenchmarkError, "snapshot tree mismatch"):
                            campaign_module._verify_deployment_runtime(
                                args, deployment=deployment
                            )
                    path.write_bytes(original)

    def test_deployment_admission_rejects_mutated_runtime_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            args, deployment, mutable_paths = _deployment_fixture(Path(raw))
            mutable_paths["runtime_record"].write_text("{}\n", encoding="utf-8")
            with patch.object(campaign_module, "validate_build_record"):
                with self.assertRaisesRegex(
                    BenchmarkError, "runtime_snapshot_record changed"
                ):
                    campaign_module._verify_deployment_runtime(
                        args, deployment=deployment
                    )

    def test_resume_rejects_changed_verified_deployment_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 1

            def closure(tree_sha256: str) -> dict[str, object]:
                runtime = {
                    "schema_version":
                    "formalization-design17-verified-deployment-runtime-1",
                    "runtime_trees": {"packages": {"tree_sha256": tree_sha256}},
                }
                runtime["identity_sha256"] = campaign_module._canonical_hash(runtime)
                value: dict[str, object] = {
                    "verified_deployment_runtime": runtime,
                }
                value["closure_sha256"] = campaign_module._canonical_hash(value)
                return value

            with patch.object(
                campaign_module,
                "_frozen_input_closure",
                return_value=closure("a" * 64),
            ):
                run_campaign(args)
            with patch.object(
                campaign_module,
                "_frozen_input_closure",
                return_value=closure("b" * 64),
            ):
                with self.assertRaisesRegex(
                    BenchmarkError, "does not match the requested frozen inputs"
                ):
                    run_campaign(args)

    def test_dry_run_performs_no_campaign_writes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            result = run_campaign(args)
            self.assertTrue(result["dry_run"])
            self.assertFalse(result["writes_performed"])
            self.assertEqual(len(result["commands"]), 13)
            self.assertFalse(args.campaign_root.exists())

    def test_incident_continues_and_resume_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 3
            wave = run_campaign(args)
            self.assertEqual(
                sum(
                    stratum["formalization_complete_audit_pending_count"]
                    for stratum in wave["strata"].values()
                ),
                2,
            )
            self.assertEqual(
                sum(stratum["completed_count"] for stratum in wave["strata"].values()),
                0,
            )
            wave_pending = sum(
                stratum["pending_count"] for stratum in wave["strata"].values()
            )
            self.assertEqual(wave_pending, 10)
            self.assertFalse(
                any(
                    event["event_type"] == "CAMPAIGN_FORMALIZATION_COMPLETE"
                    for event in _read_journal(
                        args.campaign_root / "campaign-state.jsonl"
                    )
                )
            )
            args.max_new_tasks = None
            first = run_campaign(args)
            self.assertEqual(
                first["strata"]["excluded_collision_or_router_error"]["incident_task_ids"],
                ["H22-5"],
            )
            self.assertIsNone(first["pooled_effect_estimate"])
            state_path = args.campaign_root / "campaign-state.jsonl"
            before = state_path.read_bytes()
            second = run_campaign(args)
            self.assertEqual(before, state_path.read_bytes())
            self.assertEqual(first["strata"], second["strata"])
            terminals = [
                event
                for event in _read_journal(state_path)
                if event["event_type"].startswith("TASK_")
                and event["event_type"] != "TASK_STARTED"
            ]
            self.assertEqual(len(terminals), 13)
            self.assertTrue((args.campaign_root / "tasks" / "H15-3" / "pair").is_dir())

    def test_recovery_requires_and_verifies_campaign_pair_attestation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 1
            run_campaign(args)
            manifest = json.loads(
                (args.campaign_root / "campaign-manifest.json").read_text(encoding="utf-8")
            )
            self.assertRegex(manifest["campaign_nonce"], r"^[0-9a-f]{64}$")
            attestation = (
                args.campaign_root / "tasks" / "H22-11" / "campaign-pair-attestation.json"
            )
            self.assertTrue(attestation.is_file())
            _rewind_last_terminal(args.campaign_root)
            run_campaign(args)
            events = _read_journal(args.campaign_root / "campaign-state.jsonl")
            self.assertEqual(events[-1]["event_type"], "TASK_RECOVERED_FORMALIZATION_COMPLETE")
            self.assertEqual(events[-1]["outcome"], "FORMALIZATION_COMPLETE_AUDIT_PENDING")
            self.assertEqual(
                events[-1]["details"]["pair_attestation_sha256"], sha256_file(attestation)
            )

    def test_recovery_fails_closed_after_frozen_candidate_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=False)
            args.max_new_tasks = 1
            run_campaign(args)
            _rewind_last_terminal(args.campaign_root)
            candidate = (
                args.campaign_root
                / "tasks"
                / "H22-11"
                / "pair"
                / "R0"
                / "workspace"
                / "Candidate.lean"
            )
            candidate.write_text("theorem altered : False := by contradiction\n")
            run_campaign(args)
            events = _read_journal(args.campaign_root / "campaign-state.jsonl")
            self.assertEqual(events[-1]["event_type"], "TASK_RECOVERED_INCIDENT")
            self.assertEqual(events[-1]["outcome"], "INCIDENT")
            self.assertIn("candidate is absent, unsafe, or stale", events[-1]["details"]["reason"])

    def test_wave_subset_preserves_requested_task_order_and_frozen_condition_orders(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.wave_task_ids = ["H5-5", "H10-7", "H7-12"]
            result = run_campaign(args)
            self.assertEqual(
                [item["task_id"] for item in result["invocation_plan"]],
                ["H5-5", "H10-7", "H7-12"],
            )
            self.assertEqual(
                [item["condition_order"] for item in result["invocation_plan"]],
                [["R0", "R1"], ["R1", "R0"], ["R0", "R1"]],
            )
            self.assertFalse(args.campaign_root.exists())

    def test_wave_subset_rejects_duplicates(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.wave_task_ids = ["H5-5", "H5-5"]
            with self.assertRaises(BenchmarkError):
                run_campaign(args)

    def test_statement_only_mode_is_frozen_and_passed_to_every_condition(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            args = _args(root, dry_run=True)
            args.statement_only = True
            args.wave_task_ids = ["H5-5"]
            result = run_campaign(args)
            self.assertIn("--statement-only", result["commands"][0])

    def test_statement_only_non_dry_run_requires_titan_envelope(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            args = _args(Path(raw), dry_run=False)
            args.statement_only = True
            with self.assertRaisesRegex(BenchmarkError, "require --enforce-titan-envelope"):
                run_campaign(args)

    def test_statement_only_freezes_auditor_and_submission_limit(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            args = _args(Path(raw), dry_run=True)
            args.statement_only = True
            args.submission_limit = 3
            with self.assertRaisesRegex(BenchmarkError, "four submissions"):
                run_campaign(args)
            args.submission_limit = 4
            args.audit_model = "gpt-5.6-sol"
            with self.assertRaisesRegex(BenchmarkError, "gpt-6-astra"):
                run_campaign(args)

    def test_statement_pair_requires_audited_faithful_condition_closure(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            pair_root = Path(raw) / "pair"
            pair_root.mkdir()
            prompt = pair_root / "prompt.txt"
            prompt.write_text("statement prompt", encoding="utf-8")
            reports: dict[str, dict[str, object]] = {}
            for condition in ("R0", "R1"):
                condition_root = pair_root / condition
                source = condition_root / "workspace" / "source"
                source.mkdir(parents=True)
                (source / "paper.pdf").write_bytes(b"paper")
                (source / "task.md").write_text("task", encoding="utf-8")
                api = condition_root / "workspace" / "LIBRARY_API.md"
                api.write_text("api", encoding="utf-8")
                composition = condition_root / "composition-packet.json"
                composition.write_text("{}", encoding="utf-8")
                attempt_root = condition_root / "submissions" / "01"
                attempt_root.mkdir(parents=True)
                candidate = attempt_root / "Candidate.lean"
                candidate.write_text(
                    "theorem HighamBenchCandidate.target : True := by sorry\n",
                    encoding="utf-8",
                )
                validation = attempt_root / "validation.json"
                validation.write_text(json.dumps({"pass": True}), encoding="utf-8")
                candidate_record = {
                    "path": str(candidate),
                    "sha256": sha256_file(candidate),
                    "bytes": candidate.stat().st_size,
                    "lines": 1,
                }
                attempt = {
                    "attempt": 1,
                    "candidate": candidate_record,
                    "validation_sha256": sha256_file(validation),
                    "hardware_after": {"strict": True},
                    "status": "ACCEPTED_FAITHFUL",
                }
                report = {
                    "task_id": "H5-5",
                    "condition": condition,
                    "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
                    "source_contract": "statement-only-single-target-sorry",
                    "faithfulness_status": "FAITHFUL",
                    "result_status": "ACCEPTED_FAITHFUL",
                    "attempts": [attempt],
                    "submission_count": 1,
                    "hardware_envelope_required": True,
                    "hardware_snapshot": {"strict": True},
                    "candidate": candidate_record,
                    "candidate_sha256": sha256_file(candidate),
                    "composition_packet_sha256": sha256_file(composition),
                    "library_api_sha256": sha256_file(api),
                    "source_pdf_sha256": sha256_file(source / "paper.pdf"),
                    "staged_task_sha256": sha256_file(source / "task.md"),
                }
                (condition_root / "report.json").write_text(
                    json.dumps(report), encoding="utf-8"
                )
                reports[condition] = report
            pair_report = {
                "task_id": "H5-5",
                "condition_order": ["R0", "R1"],
                "conditions_run_sequentially": True,
                "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
                "source_contract": "statement-only-single-target-sorry",
                "faithfulness_status": "BOTH_FAITHFUL",
                "pair_status": "AUDITED_FAITHFUL_PAIR",
                "prompt_sha256": sha256_file(prompt),
                "source_packet_sha256": "a" * 64,
                "source_pdf_sha256": hashlib.sha256(b"paper").hexdigest(),
                "condition_reports": reports,
            }
            (pair_root / "pair-report.json").write_text(
                json.dumps(pair_report), encoding="utf-8"
            )
            outcome, details = campaign_module._inspect_pair(
                pair_root,
                task_id="H5-5",
                condition_order=["R0", "R1"],
                statement_only=True,
                require_titan_envelope=True,
            )
            self.assertEqual(outcome, "AUDITED_FAITHFUL_PAIR")
            self.assertRegex(details["pair_artifact_closure_sha256"], r"^[0-9a-f]{64}$")

            incident_report = dict(reports["R1"])
            incident_attempt = dict(incident_report["attempts"][0])
            incident_attempt["status"] = "AUDIT_SYSTEM_INCIDENT"
            incident_report["attempts"] = [incident_attempt]
            incident_report["result_status"] = "AUDIT_SYSTEM_INCIDENT"
            incident_report["faithfulness_status"] = "NOT_DECIDED_INFRASTRUCTURE"
            (pair_root / "R1" / "report.json").write_text(
                json.dumps(incident_report), encoding="utf-8"
            )
            pair_report["condition_reports"]["R1"] = incident_report
            pair_report["pair_status"] = "PAIR_INCIDENT"
            pair_report["faithfulness_status"] = "NOT_DECIDED_INFRASTRUCTURE"
            (pair_root / "pair-report.json").write_text(
                json.dumps(pair_report), encoding="utf-8"
            )
            outcome, details = campaign_module._inspect_pair(
                pair_root,
                task_id="H5-5",
                condition_order=["R0", "R1"],
                statement_only=True,
                require_titan_envelope=True,
            )
            self.assertEqual(outcome, "PAIR_INFRASTRUCTURE_INCIDENT")
            self.assertIn("infrastructure incident", details["reason"])
            task_root = pair_root.parent
            (task_root / "runner.stdout.log").write_text("", encoding="utf-8")
            (task_root / "runner.stderr.log").write_text("", encoding="utf-8")
            manifest = {
                "campaign_identity_sha256": "a" * 64,
                "campaign_nonce": "b" * 64,
                "campaign_core": {
                    "formalizer": {
                        "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
                        "source_contract": "statement-only-single-target-sorry",
                    }
                },
            }
            item = {"task_id": "H5-5", "condition_order": ["R0", "R1"]}
            campaign_module._attest_pair(
                task_root=task_root,
                manifest=manifest,
                pair_nonce="c" * 64,
                item=item,
                details=details,
                runner_return_code=0,
            )
            verified = campaign_module._verify_pair_attestation(
                task_root=task_root,
                manifest=manifest,
                pair_nonce="c" * 64,
                item=item,
                details=details,
            )
            self.assertRegex(verified["pair_attestation_sha256"], r"^[0-9a-f]{64}$")


if __name__ == "__main__":
    unittest.main()
