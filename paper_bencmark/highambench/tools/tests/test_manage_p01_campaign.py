from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import manage_p01_campaign as campaign  # noqa: E402
import run_matrix  # noqa: E402


def canonical_pair(pair_id: str) -> dict[str, object]:
    task_id, repetition = pair_id.rsplit("-rep-", 1)
    order = ["N", "L"]
    return {
        "pair_id": pair_id,
        "task_id": task_id,
        "repetition_id": f"rep-{repetition}",
        "condition_order": order,
        "run_ids": [f"{pair_id}-{condition}" for condition in order],
        "run_order_pair_sha256": "a" * 64,
    }


def run_order_pair(task_id: str, repetition_id: str) -> dict[str, object]:
    pair_id = f"{task_id}-{repetition_id}"
    order = ["N", "L"]
    return {
        "pair_id": pair_id,
        "task_id": task_id,
        "repetition_id": repetition_id,
        "condition_order": order,
        "run_ids": [f"{pair_id}-{condition}" for condition in order],
        "sha256": "a" * 64,
    }


def snapshot() -> dict[str, object]:
    pairs = [
        canonical_pair(f"P01-T{tier}-rep-0{repetition}")
        for tier in range(1, 4)
        for repetition in range(1, 4)
    ]
    policy = json.loads(json.dumps(run_matrix.HARDWARE_MATCHING_POLICY))
    return {
        "benchmark_id": "benchmark-fixture",
        "manifest": {"path": "metadata/manifest.json", "sha256": "b" * 64},
        "run_order": {"path": "metadata/run_order.json", "sha256": "c" * 64},
        "environment": {
            "path": "metadata/environment.json",
            "environment_id": "environment-fixture",
            "environment_bundle_sha256": "d" * 64,
        },
        "hardware_matching_policy": policy,
        "hardware_matching_policy_sha256": campaign.canonical_sha256(policy),
        "canonical_pairs": pairs,
    }


def fresh_index() -> dict[str, object]:
    return {
        "schema_version": 1,
        "kind": campaign.INDEX_KIND,
        **snapshot(),
        "committed_pairs": {},
        "failed_pair_attempts": [],
        "active_pair_attempt": None,
        "created_at_utc": "2026-08-13T00:00:00Z",
        "updated_at_utc": "2026-08-13T00:00:00Z",
    }


class CampaignManagerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "campaign"
        self.benchmark = Path(self.temporary.name) / "benchmark"
        self.benchmark.mkdir()

    def test_historical_pair_selection_ignores_t4_and_rejects_other_p01_tiers(self) -> None:
        pairs = [
            run_order_pair(f"P01-T{tier}", f"rep-0{repetition}")
            for tier in range(1, 4)
            for repetition in range(1, 4)
        ]
        pairs.append(run_order_pair("P01-T4", "rep-01"))
        selected = campaign.canonical_pairs({"pairs": pairs})
        self.assertEqual(len(selected), 9)
        self.assertEqual({item["task_id"] for item in selected}, set(campaign.EXPECTED_TASKS))

        pairs.append(run_order_pair("P01-T5", "rep-01"))
        with self.assertRaisesRegex(
            campaign.CampaignError, "outside the historical T1--T3 campaign"
        ):
            campaign.canonical_pairs({"pairs": pairs})

    def test_planned_assignments_do_not_parse_t4_task_catalog(self) -> None:
        metadata = self.benchmark / "metadata"
        metadata.mkdir()
        campaign.atomic_write_json(
            metadata / "config.json",
            {
                "repetitions": [
                    {"id": f"rep-0{number}", "backend_seed": number}
                    for number in range(1, 4)
                ]
            },
        )
        pairs = [
            run_order_pair(f"P01-T{tier}", f"rep-0{repetition}")
            for tier in range(1, 4)
            for repetition in range(1, 4)
        ]
        pairs.append(run_order_pair("P01-T4", "rep-01"))
        campaign.atomic_write_json(metadata / "run_order.json", {"pairs": pairs})
        with mock.patch.object(
            run_matrix,
            "load_task_catalog",
            side_effect=AssertionError("legacy catalog parser must not run"),
        ):
            assignments = campaign.planned_pair_assignments(
                self.benchmark, "P01-T1-rep-01"
            )
        self.assertEqual([item["condition"] for item in assignments], ["N", "L"])
        self.assertTrue(all(item["tier"] == "T1" for item in assignments))

    def test_index_self_hash_detects_tampering(self) -> None:
        index = campaign.bind_index_hash(fresh_index())
        campaign.verify_index_hash(index)
        index["benchmark_id"] = "tampered"
        with self.assertRaisesRegex(campaign.CampaignError, "self-hash is stale"):
            campaign.verify_index_hash(index)

    def test_recursive_tree_digest_is_exact_and_rejects_symlink(self) -> None:
        self.root.mkdir()
        (self.root / "a.txt").write_text("a", encoding="utf-8")
        (self.root / "nested").mkdir()
        (self.root / "nested" / "b.txt").write_text("bb", encoding="utf-8")
        first = campaign.recursive_tree_summary(self.root)
        self.assertEqual(first["file_count"], 2)
        self.assertEqual(first["total_bytes"], 3)
        (self.root / "a.txt").write_text("changed", encoding="utf-8")
        self.assertNotEqual(first["tree_sha256"], campaign.recursive_tree_summary(self.root)["tree_sha256"])
        (self.root / "link").symlink_to("a.txt")
        with self.assertRaisesRegex(campaign.CampaignError, "contains a symlink"):
            campaign.recursive_tree_summary(self.root)

    def test_resolve_below_rejects_symlink_component(self) -> None:
        self.root.mkdir()
        outside = Path(self.temporary.name) / "outside"
        outside.mkdir()
        (self.root / "pair_attempts").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(campaign.CampaignError, "symlink component"):
            campaign.resolve_below(
                self.root,
                "pair_attempts/P01-T1-rep-01/attempt-1-slurm-123",
                "attempt",
            )

    def test_cli_rejects_symlinked_campaign_root(self) -> None:
        actual = Path(self.temporary.name) / "actual-campaign"
        actual.mkdir()
        alias = Path(self.temporary.name) / "campaign-alias"
        alias.symlink_to(actual, target_is_directory=True)
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            self.assertEqual(
                campaign.main(
                    [
                        "--campaign-root",
                        str(alias),
                        "--benchmark-root",
                        str(self.benchmark),
                        "initialize",
                    ]
                ),
                2,
            )

    def test_launcher_holds_whole_job_nonblocking_lock(self) -> None:
        launcher = (
            TOOLS.parents[1] / "scratch_pad" / "run_highambench_p01_actual_ultra.sh"
        ).read_text(encoding="utf-8")
        self.assertIn('exec 9>"${RESULT_ROOT}/.launcher.lock"', launcher)
        self.assertIn('/usr/bin/flock -n 9', launcher)
        self.assertLess(
            launcher.index('/usr/bin/flock -n 9'),
            launcher.index('initial canary descriptors'),
        )

    def test_launcher_forbids_canary_replacement_after_campaign_index(self) -> None:
        launcher = (
            TOOLS.parents[1] / "scratch_pad" / "run_highambench_p01_actual_ultra.sh"
        ).read_text(encoding="utf-8")
        guard = 'if [[ -e "${RESULT_ROOT}/campaign_index.json"'
        replacement = 'if [[ "$ultra_status" == replacement_required ]]'
        self.assertIn(guard, launcher)
        self.assertIn(
            "existing campaign requires both frozen canary descriptors already passed",
            launcher,
        )
        self.assertLess(launcher.index(guard), launcher.index(replacement))

    def test_launcher_staging_recovery_and_descriptor_regex_are_ordered(self) -> None:
        launcher = (
            TOOLS.parents[1] / "scratch_pad" / "run_highambench_p01_actual_ultra.sh"
        ).read_text(encoding="utf-8")
        recovery = 'recover-staging \\\n  --slurm-job-id "$SLURM_JOB_ID"'
        self.assertIn(recovery, launcher)
        self.assertLess(launcher.index('/usr/bin/flock -n 9'), launcher.index(recovery))
        self.assertLess(launcher.index(recovery), launcher.index('readonly INITIAL_LEDGER='))
        descriptor_block = launcher[
            launcher.index("descriptor_status()") : launcher.index(
                "remaining_allocation_seconds()"
            )
        ]
        self.assertIn("import re", descriptor_block)

    def test_recover_staging_preserves_regular_index_temporary(self) -> None:
        self.root.mkdir()
        temporary = self.root / ".campaign_index.json.tmp-4321"
        temporary.write_text('{"partial":true}\n', encoding="utf-8")
        result = campaign.recover_launcher_staging(self.root, "123")
        destination = self.root / result["preserved_staging_artifacts"][0]
        self.assertFalse(temporary.exists())
        self.assertEqual(destination.read_text(encoding="utf-8"), '{"partial":true}\n')
        self.assertRegex(
            destination.name,
            r"campaign_index_write\.interrupted-pid-4321\.recovered-slurm-123\.json",
        )

    def test_recover_staging_rejects_symlink_dir_and_malformed_temporaries(self) -> None:
        cases = ("symlink", "directory", "malformed")
        for name in cases:
            with self.subTest(name=name):
                root = Path(self.temporary.name) / f"staging-{name}"
                root.mkdir()
                path = root / (
                    ".campaign_index.json.tmp-bad"
                    if name == "malformed"
                    else ".campaign_index.json.tmp-4321"
                )
                if name == "symlink":
                    target = root / "target"
                    target.write_text("{}", encoding="utf-8")
                    path.symlink_to(target)
                elif name == "directory":
                    path.mkdir()
                else:
                    path.write_text("{}", encoding="utf-8")
                with self.assertRaisesRegex(
                    campaign.CampaignError,
                    "unexpected entry|not a regular non-symlink",
                ):
                    campaign.recover_launcher_staging(root, "123")

    def test_recover_staging_preserves_first_unsealed_ledger_only_without_state(self) -> None:
        self.root.mkdir()
        audit = self.root / "runbook_audit"
        audit.mkdir()
        ledger = audit / campaign.INITIAL_LEDGER_NAME
        ledger.write_text("partial", encoding="utf-8")
        ledger.chmod(0o600)
        result = campaign.recover_launcher_staging(self.root, "123")
        self.assertFalse(ledger.exists())
        preserved = self.root / result["preserved_staging_artifacts"][0]
        self.assertEqual(preserved.read_text(encoding="utf-8"), "partial")

        for state in ("index", "attempt"):
            with self.subTest(state=state):
                root = Path(self.temporary.name) / f"ledger-with-{state}"
                audit = root / "runbook_audit"
                audit.mkdir(parents=True)
                partial = audit / campaign.INITIAL_LEDGER_NAME
                partial.write_text("partial", encoding="utf-8")
                partial.chmod(0o600)
                if state == "index":
                    (root / "campaign_index.json").write_text("{}", encoding="utf-8")
                else:
                    attempt = root / "pair_attempts" / "P01-T1-rep-01"
                    attempt.mkdir(parents=True)
                with self.assertRaisesRegex(
                    campaign.CampaignError, "coexists with .* state"
                ):
                    campaign.recover_launcher_staging(root, "123")

    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_initialize_and_begin_use_permanent_path_and_block_overlap(self, _snapshot: mock.Mock) -> None:
        index = campaign.initialize(self.root, self.benchmark)
        pair_id = "P01-T1-rep-01"
        index, attempt_root = campaign.begin_attempt(
            self.root, index, pair_id, "123", "watgpu108"
        )
        self.assertEqual(
            attempt_root.relative_to(self.root).as_posix(),
            "pair_attempts/P01-T1-rep-01/attempt-1-slurm-123",
        )
        self.assertTrue(attempt_root.is_dir())
        with self.assertRaisesRegex(campaign.CampaignError, "already has an active"):
            campaign.begin_attempt(self.root, index, pair_id, "124", "watgpu508")

    @mock.patch.object(
        run_matrix,
        "verify_pair_policy_compatible_freeze_checks",
        side_effect=run_matrix.BenchmarkToolError("outside-policy difference"),
    )
    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_rejects_cross_pair_freeze_incompatibility(
        self,
        _snapshot: mock.Mock,
        _verify_descriptor: mock.Mock,
        verify_compatible: mock.Mock,
    ) -> None:
        self.root.mkdir()
        index = fresh_index()
        committed: dict[str, object] = {}
        for serial, pair_id in enumerate(
            ("P01-T1-rep-01", "P01-T1-rep-02"), start=1
        ):
            relative = (
                Path("pair_attempts")
                / pair_id
                / f"attempt-1-slurm-12{serial}"
            )
            pair_root = self.root / relative
            pair_root.mkdir(parents=True)
            (pair_root / "freeze_check.json").write_text(
                json.dumps({"pair": pair_id}), encoding="utf-8"
            )
            committed[pair_id] = {
                "pair_id": pair_id,
                "path": relative.as_posix(),
                "attempt_id": f"attempt-1-slurm-12{serial}",
                "started_at_utc": f"2026-08-13T00:0{serial - 1}:00Z",
                "committed_at_utc": f"2026-08-13T00:0{serial}:00Z",
            }
        index["committed_pairs"] = committed
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        with self.assertRaisesRegex(
            campaign.CampaignError, "incompatible with the campaign reference pair"
        ):
            campaign.load_and_verify_index(self.root, self.benchmark)
        verify_compatible.assert_called_once()

    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_rejects_skipped_committed_prefix(
        self, _snapshot: mock.Mock
    ) -> None:
        self.root.mkdir()
        index = fresh_index()
        index["committed_pairs"] = {
            "P01-T1-rep-02": {"pair_id": "P01-T1-rep-02"}
        }
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        with self.assertRaisesRegex(campaign.CampaignError, "canonical prefix"):
            campaign.load_and_verify_index(self.root, self.benchmark)

    @mock.patch.object(
        run_matrix, "verify_pair_policy_compatible_freeze_checks"
    )
    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_rejects_overlapping_adjacent_committed_pairs(
        self,
        _snapshot: mock.Mock,
        _verify_descriptor: mock.Mock,
        _verify_compatible: mock.Mock,
    ) -> None:
        self.root.mkdir()
        index = fresh_index()
        committed: dict[str, object] = {}
        times = (
            ("2026-08-13T00:00:00Z", "2026-08-13T00:02:00Z"),
            ("2026-08-13T00:01:00Z", "2026-08-13T00:03:00Z"),
        )
        for serial, (pair_id, pair_times) in enumerate(
            zip(("P01-T1-rep-01", "P01-T1-rep-02"), times), start=1
        ):
            relative = (
                Path("pair_attempts")
                / pair_id
                / f"attempt-1-slurm-12{serial}"
            )
            pair_root = self.root / relative
            pair_root.mkdir(parents=True)
            (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
            committed[pair_id] = {
                "pair_id": pair_id,
                "path": relative.as_posix(),
                "attempt_id": f"attempt-1-slurm-12{serial}",
                "started_at_utc": pair_times[0],
                "committed_at_utc": pair_times[1],
            }
        index["committed_pairs"] = committed
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        with self.assertRaisesRegex(campaign.CampaignError, "overlaps or precedes"):
            campaign.load_and_verify_index(self.root, self.benchmark)

    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_rejects_pair_start_after_commit(
        self, _snapshot: mock.Mock, _verify_descriptor: mock.Mock
    ) -> None:
        self.root.mkdir()
        pair_id = "P01-T1-rep-01"
        relative = Path("pair_attempts") / pair_id / "attempt-1-slurm-123"
        pair_root = self.root / relative
        pair_root.mkdir(parents=True)
        (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
        index = fresh_index()
        index["committed_pairs"] = {
            pair_id: {
                "pair_id": pair_id,
                "path": relative.as_posix(),
                "started_at_utc": "2026-08-13T00:02:00Z",
                "committed_at_utc": "2026-08-13T00:01:00Z",
            }
        }
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        with self.assertRaisesRegex(campaign.CampaignError, "starts after"):
            campaign.load_and_verify_index(self.root, self.benchmark)

    @mock.patch.object(campaign, "verify_failed_index_descriptor")
    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_rejects_attempt_history_serial_and_time_tampering(
        self,
        _snapshot: mock.Mock,
        _verify_committed: mock.Mock,
        _verify_failed: mock.Mock,
    ) -> None:
        cases = (
            ("duplicate-serial", "unique and contiguous"),
            ("gap-serial", "unique and contiguous"),
            ("failed-reversed", "starts after its archive"),
            ("attempt-overlap", "overlaps or reverses chronology"),
            ("cross-pair-failed-start", "before the prior canonical pair commit"),
        )
        for name, message in cases:
            with self.subTest(name=name):
                root = Path(self.temporary.name) / f"history-{name}"
                root.mkdir()
                index = fresh_index()

                def historical(
                    pair_id: str,
                    serial: int,
                    job_id: str,
                    started: str,
                    terminal: str,
                    *,
                    committed: bool,
                ) -> dict[str, object]:
                    attempt_id = f"attempt-{serial}-slurm-{job_id}"
                    relative = Path("pair_attempts") / pair_id / attempt_id
                    pair_root = root / relative
                    pair_root.mkdir(parents=True)
                    if committed:
                        (pair_root / "freeze_check.json").write_text(
                            "{}", encoding="utf-8"
                        )
                    result: dict[str, object] = {
                        "pair_id": pair_id,
                        "attempt_id": attempt_id,
                        "path": relative.as_posix(),
                        "slurm_job_id": job_id,
                        "allocation_node": "watgpu108",
                        "started_at_utc": started,
                    }
                    result[
                        "committed_at_utc" if committed else "archived_at_utc"
                    ] = terminal
                    return result

                active: dict[str, object] | None = None
                if name == "duplicate-serial":
                    committed = historical(
                        "P01-T1-rep-01",
                        1,
                        "121",
                        "2026-08-13T00:00:00Z",
                        "2026-08-13T00:01:00Z",
                        committed=True,
                    )
                    failed = historical(
                        "P01-T1-rep-01",
                        1,
                        "122",
                        "2026-08-12T23:58:00Z",
                        "2026-08-12T23:59:00Z",
                        committed=False,
                    )
                    index["committed_pairs"] = {"P01-T1-rep-01": committed}
                    index["failed_pair_attempts"] = [failed]
                elif name == "gap-serial":
                    failed = historical(
                        "P01-T1-rep-01",
                        2,
                        "122",
                        "2026-08-13T00:00:00Z",
                        "2026-08-13T00:01:00Z",
                        committed=False,
                    )
                    index["failed_pair_attempts"] = [failed]
                elif name == "failed-reversed":
                    failed = historical(
                        "P01-T1-rep-01",
                        1,
                        "121",
                        "2026-08-13T00:02:00Z",
                        "2026-08-13T00:01:00Z",
                        committed=False,
                    )
                    index["failed_pair_attempts"] = [failed]
                elif name == "attempt-overlap":
                    failed = historical(
                        "P01-T1-rep-01",
                        1,
                        "121",
                        "2026-08-13T00:00:00Z",
                        "2026-08-13T00:02:00Z",
                        committed=False,
                    )
                    index["failed_pair_attempts"] = [failed]
                    active = historical(
                        "P01-T1-rep-01",
                        2,
                        "122",
                        "2026-08-13T00:01:00Z",
                        "2026-08-13T00:03:00Z",
                        committed=False,
                    )
                    active.pop("archived_at_utc")
                else:
                    committed = historical(
                        "P01-T1-rep-01",
                        1,
                        "121",
                        "2026-08-13T00:00:00Z",
                        "2026-08-13T00:02:00Z",
                        committed=True,
                    )
                    failed = historical(
                        "P01-T1-rep-02",
                        1,
                        "122",
                        "2026-08-13T00:01:00Z",
                        "2026-08-13T00:03:00Z",
                        committed=False,
                    )
                    index["committed_pairs"] = {"P01-T1-rep-01": committed}
                    index["failed_pair_attempts"] = [failed]
                index["active_pair_attempt"] = active
                campaign.atomic_write_json(
                    campaign.index_path(root), campaign.bind_index_hash(index)
                )
                with self.assertRaisesRegex(campaign.CampaignError, message):
                    campaign.load_and_verify_index(root, self.benchmark)

    def _active_deadline_fixture(self) -> tuple[dict[str, object], Path]:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        for relative in ("records", "incidents", "attempts"):
            (pair_root / relative).mkdir(parents=True, exist_ok=True)
        (pair_root / "runs.jsonl").write_text("", encoding="utf-8")
        status = {
            "schema_version": 1,
            "kind": "highambench-matrix-chunk-status",
            "status": "stopped_before_allocation_deadline",
            "next_pair_id": pair_id,
            "next_run_id": f"{pair_id}-N",
            "unfinished_runs_in_next_pair": 2,
            "allocation_end_epoch": 1,
            "remaining_seconds": -100.0,
            "required_seconds": 5418.0,
            "prompt_startup_timeout_seconds": 120.0,
            "startup_timeouts_reserved_per_unfinished_run": 2,
            "post_submission_validation_reserve_seconds": 369.0,
            "guard_seconds": 600.0,
        }
        (pair_root / "last_chunk_status.json").write_text(
            json.dumps(status), encoding="utf-8"
        )
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        return index, pair_root

    def _active_partial_final_fixture(
        self,
        *,
        record_pair_id: str = "P01-T1-rep-01",
        record_run_id: str = "P01-T1-rep-01-N",
        tamper_after_seal: bool = False,
    ) -> tuple[dict[str, object], Path]:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        (pair_root / "records").mkdir(parents=True)
        (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
        record: dict[str, object] = {
            "pair_id": record_pair_id,
            "run_id": record_run_id,
        }
        record["matrix_record_sha256"] = run_matrix.matrix_record_digest(record)
        if tamper_after_seal:
            record["tampered_after_seal"] = True
        (pair_root / "records" / f"{record_run_id}.json").write_text(
            json.dumps(record), encoding="utf-8"
        )
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)
        return index, pair_root

    def _active_two_final_fixture(
        self,
        *,
        with_commit_status: bool = False,
        mixed_allocation: bool = False,
        tamper_after_seal: bool = False,
    ) -> tuple[dict[str, object], Path, dict[str, object]]:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        (pair_root / "records").mkdir(parents=True)
        (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
        for condition in ("N", "L"):
            allocation = {"job_id": "123", "hostname": "watgpu108"}
            if condition == "L" and mixed_allocation:
                allocation = {"job_id": "124", "hostname": "watgpu508"}
            record: dict[str, object] = {
                "pair_id": pair_id,
                "run_id": f"{pair_id}-{condition}",
                "allocation_hardware": allocation,
            }
            record["matrix_record_sha256"] = run_matrix.matrix_record_digest(record)
            if condition == "L" and tamper_after_seal:
                record["tampered_after_seal"] = True
            (pair_root / "records" / f"{pair_id}-{condition}.json").write_text(
                json.dumps(record), encoding="utf-8"
            )
        commit: dict[str, object] = {"pair_commit_sha256": "a" * 64}
        if with_commit_status:
            commit_path = pair_root / "pair_commit.json"
            commit_path.write_text("{}", encoding="utf-8")
            commit_path.chmod(0o444)
            status = {
                "schema_version": 1,
                "kind": "highambench-matrix-chunk-status",
                "status": "stopped_after_requested_pair",
                "pair_id": pair_id,
                "completed_runs": 2,
                "planned_runs": 2,
                "pair_commit": run_matrix.pair_commit_descriptor(pair_root, commit),
            }
            (pair_root / "last_chunk_status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)
        return index, pair_root, commit

    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_deadline_attempt_is_archived_without_moving_root(self, _planned: mock.Mock) -> None:
        index, pair_root = self._active_deadline_fixture()
        campaign.write_matrix_exit_marker(pair_root, "P01-T1-rep-01", "123", run_matrix.CHUNK_INCOMPLETE_EXIT_CODE)
        updated = campaign.archive_failed_attempt(
            self.root,
            self.benchmark,
            index,
            "P01-T1-rep-01",
            "123",
            run_matrix.CHUNK_INCOMPLETE_EXIT_CODE,
            "allocation_deadline_before_pair",
        )
        self.assertTrue(pair_root.is_dir())
        self.assertIsNone(updated["active_pair_attempt"])
        self.assertEqual(updated["failed_pair_attempts"][0]["path"], pair_root.relative_to(self.root).as_posix())

    def test_deadline_validation_rejects_any_attempt_file(self) -> None:
        _index, pair_root = self._active_deadline_fixture()
        (pair_root / "attempts" / "started.json").write_text("{}", encoding="utf-8")
        status = json.loads((pair_root / "last_chunk_status.json").read_text(encoding="utf-8"))
        with self.assertRaisesRegex(campaign.CampaignError, "attempt directory is not empty"):
            campaign.validate_zero_work_deadline(
                pair_root,
                "P01-T1-rep-01",
                "P01-T1-rep-01-N",
                status,
                final_count=0,
                incident_count=0,
            )

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(run_matrix, "_authenticate_final_assignment_record")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_rc2_authenticated_partial_final_is_archived_for_whole_pair_rerun(
        self,
        _planned: mock.Mock,
        authenticate_final: mock.Mock,
        _verify_freeze: mock.Mock,
    ) -> None:
        index, pair_root = self._active_partial_final_fixture()
        updated = campaign.archive_failed_attempt(
            self.root,
            self.benchmark,
            index,
            "P01-T1-rep-01",
            "123",
            2,
            "matrix_error",
        )
        failed = updated["failed_pair_attempts"][0]
        self.assertEqual(failed["final_record_count"], 1)
        self.assertEqual(failed["outcome"], "matrix_error")
        self.assertEqual(failed["path"], pair_root.relative_to(self.root).as_posix())
        self.assertIsNone(updated["active_pair_attempt"])
        authenticate_final.assert_called_once()

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(run_matrix, "_authenticate_final_assignment_record")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_rc2_partial_final_rejects_tamper_and_foreign_identity(
        self,
        _planned: mock.Mock,
        authenticate_final: mock.Mock,
        _verify_freeze: mock.Mock,
    ) -> None:
        cases = (
            {
                "name": "tampered",
                "fixture": {"tamper_after_seal": True},
                "message": "self-hash is stale",
            },
            {
                "name": "foreign",
                "fixture": {
                    "record_pair_id": "P02-T1-rep-01",
                    "record_run_id": "P01-T1-rep-01-N",
                },
                "message": "belongs to another pair",
            },
        )
        for case in cases:
            with self.subTest(case["name"]):
                if self.root.exists():
                    # Each rejected archive retains its permanent evidence; use
                    # a distinct campaign root for the next negative case.
                    self.root = Path(self.temporary.name) / f"campaign-{case['name']}"
                index, _pair_root = self._active_partial_final_fixture(
                    **case["fixture"]
                )
                with self.assertRaisesRegex(campaign.CampaignError, case["message"]):
                    campaign.archive_failed_attempt(
                        self.root,
                        self.benchmark,
                        index,
                        "P01-T1-rep-01",
                        "123",
                        2,
                        "matrix_error",
                    )
        authenticate_final.assert_not_called()

    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_rc75_still_rejects_one_final(self, _planned: mock.Mock) -> None:
        index, pair_root = self._active_deadline_fixture()
        record = {"pair_id": "P01-T1-rep-01", "run_id": "P01-T1-rep-01-N"}
        record["matrix_record_sha256"] = run_matrix.matrix_record_digest(record)
        (pair_root / "records" / "P01-T1-rep-01-N.json").write_text(
            json.dumps(record), encoding="utf-8"
        )
        campaign.write_matrix_exit_marker(
            pair_root,
            "P01-T1-rep-01",
            "123",
            run_matrix.CHUNK_INCOMPLETE_EXIT_CODE,
        )
        with self.assertRaisesRegex(campaign.CampaignError, "zero-work"):
            campaign.archive_failed_attempt(
                self.root,
                self.benchmark,
                index,
                "P01-T1-rep-01",
                "123",
                run_matrix.CHUNK_INCOMPLETE_EXIT_CODE,
                "allocation_deadline_before_pair",
            )

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(run_matrix, "verify_pair_commit")
    @mock.patch.object(run_matrix, "create_or_verify_pair_commit")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {
                "run_id": "P01-T1-rep-01-N",
                "pair_id": "P01-T1-rep-01",
                "condition": "N",
            },
            {
                "run_id": "P01-T1-rep-01-L",
                "pair_id": "P01-T1-rep-01",
                "condition": "L",
            },
        ],
    )
    def test_recover_rc2_two_authenticated_finals_archives_without_promotion(
        self,
        _planned: mock.Mock,
        create_commit: mock.Mock,
        verify_commit: mock.Mock,
        _verify_freeze: mock.Mock,
    ) -> None:
        def authenticate(
            _root: Path,
            path: Path,
            _assignment: object,
            _freeze: object,
            **_kwargs: object,
        ) -> dict[str, object]:
            return json.loads(path.read_text(encoding="utf-8"))

        create_commit.side_effect = AssertionError(
            "rc2 recovery must not create/promote a pair commit"
        )
        with mock.patch.object(
            run_matrix,
            "_authenticate_final_assignment_record",
            side_effect=authenticate,
        ):
            for with_commit_status in (False, True):
                with self.subTest(with_commit_status=with_commit_status):
                    self.root = Path(self.temporary.name) / (
                        "campaign-two-with-commit"
                        if with_commit_status
                        else "campaign-two-no-commit"
                    )
                    index, pair_root, commit = self._active_two_final_fixture(
                        with_commit_status=with_commit_status
                    )
                    verify_commit.return_value = commit
                    updated = campaign.recover_active_attempt(
                        self.root, self.benchmark, index
                    )
                    failed = updated["failed_pair_attempts"][0]
                    self.assertEqual(failed["outcome"], "matrix_error")
                    self.assertEqual(failed["matrix_exit_code"], 2)
                    self.assertEqual(failed["final_record_count"], 2)
                    self.assertTrue(pair_root.is_dir())
                    self.assertIsNone(updated["active_pair_attempt"])
        create_commit.assert_not_called()
        verify_commit.assert_called_once()

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {
                "run_id": "P01-T1-rep-01-N",
                "pair_id": "P01-T1-rep-01",
                "condition": "N",
            },
            {
                "run_id": "P01-T1-rep-01-L",
                "pair_id": "P01-T1-rep-01",
                "condition": "L",
            },
        ],
    )
    def test_rc2_two_final_archive_rejects_tamper_and_mixed_allocation(
        self, _planned: mock.Mock, _verify_freeze: mock.Mock
    ) -> None:
        def authenticate(
            _root: Path,
            path: Path,
            _assignment: object,
            _freeze: object,
            **_kwargs: object,
        ) -> dict[str, object]:
            return json.loads(path.read_text(encoding="utf-8"))

        cases = (
            ("tampered-two", {"tamper_after_seal": True}, "self-hash is stale"),
            (
                "mixed-allocation",
                {"mixed_allocation": True},
                "one exact allocation descriptor",
            ),
        )
        with mock.patch.object(
            run_matrix,
            "_authenticate_final_assignment_record",
            side_effect=authenticate,
        ):
            for name, fixture, message in cases:
                with self.subTest(name=name):
                    self.root = Path(self.temporary.name) / f"campaign-{name}"
                    index, _pair_root, _commit = self._active_two_final_fixture(
                        **fixture
                    )
                    with self.assertRaisesRegex(Exception, message):
                        campaign.archive_failed_attempt(
                            self.root,
                            self.benchmark,
                            index,
                            "P01-T1-rep-01",
                            "123",
                            2,
                            "matrix_error",
                        )

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_failed_root_retains_exact_runner_write_temporaries(
        self, _planned: mock.Mock, _verify_freeze: mock.Mock
    ) -> None:
        for directory_name, temporary_name in (
            ("records", ".P01-T1-rep-01-N.json.tmp-4321"),
            ("incidents", ".P01-T1-rep-01-N.attempt-1.json.tmp-4321"),
        ):
            with self.subTest(directory=directory_name):
                self.root = Path(self.temporary.name) / f"temp-{directory_name}"
                pair_id = "P01-T1-rep-01"
                pair_root = (
                    self.root
                    / "pair_attempts"
                    / pair_id
                    / "attempt-1-slurm-123"
                )
                (pair_root / directory_name).mkdir(parents=True)
                (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
                (pair_root / directory_name / temporary_name).write_text(
                    "partial", encoding="utf-8"
                )
                index = fresh_index()
                index["active_pair_attempt"] = {
                    "pair_id": pair_id,
                    "attempt_id": "attempt-1-slurm-123",
                    "path": pair_root.relative_to(self.root).as_posix(),
                    "slurm_job_id": "123",
                    "allocation_node": "watgpu108",
                    "started_at_utc": "2026-08-13T00:00:00Z",
                }
                campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)
                updated = campaign.archive_failed_attempt(
                    self.root,
                    self.benchmark,
                    index,
                    pair_id,
                    "123",
                    2,
                    "matrix_error",
                )
                self.assertEqual(
                    updated["failed_pair_attempts"][0]["outcome"], "matrix_error"
                )
                self.assertTrue((pair_root / directory_name / temporary_name).is_file())

    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_failed_root_rejects_symlink_and_foreign_write_temporaries(
        self, _planned: mock.Mock
    ) -> None:
        cases = (
            ("symlink", ".P01-T1-rep-01-N.json.tmp-4321"),
            ("foreign", ".P02-T1-rep-01-N.json.tmp-4321"),
        )
        for name, temporary_name in cases:
            with self.subTest(name=name):
                root = Path(self.temporary.name) / f"write-temp-{name}"
                pair_root = (
                    root
                    / "pair_attempts"
                    / "P01-T1-rep-01"
                    / "attempt-1-slurm-123"
                )
                records = pair_root / "records"
                records.mkdir(parents=True)
                temporary = records / temporary_name
                if name == "symlink":
                    target = pair_root / "target"
                    target.write_text("partial", encoding="utf-8")
                    temporary.symlink_to(target)
                else:
                    temporary.write_text("partial", encoding="utf-8")
                with self.assertRaisesRegex(
                    campaign.CampaignError, "foreign/unsafe write temporary"
                ):
                    campaign.validate_failed_runner_temporaries(
                        pair_root,
                        [
                            {"run_id": "P01-T1-rep-01-N"},
                            {"run_id": "P01-T1-rep-01-L"},
                        ],
                    )

    @mock.patch.object(run_matrix, "_authenticate_matrix_incident")
    def test_failed_root_accepts_exact_authenticated_incident_artifact(
        self, authenticate_incident: mock.Mock
    ) -> None:
        pair_root = (
            self.root
            / "pair_attempts"
            / "P01-T1-rep-01"
            / "attempt-1-slurm-123"
        )
        incidents = pair_root / "incidents"
        incidents.mkdir(parents=True)
        incident_path = incidents / "P01-T1-rep-01-N.attempt-1.json"
        incident_path.write_text("{}", encoding="utf-8")
        artifact = incidents / (
            "P01-T1-rep-01-N-unscorable-attempt-1.attempt-1."
            "P01-T1-rep-01-N.attempt-1.agent_log.artifact"
        )
        artifact.write_bytes(b"authenticated retained log\n")
        digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
        authenticated = {
            "agent_log": artifact.relative_to(pair_root).as_posix(),
            "agent_log_sha256": digest,
            "validation_log": None,
            "validation_log_sha256": None,
        }
        authenticate_incident.return_value = authenticated
        assignments = [
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ]
        values = campaign.authenticate_present_incidents(
            pair_root, assignments, {}
        )
        campaign.validate_failed_runner_temporaries(
            pair_root,
            assignments,
            authenticated_incidents=values,
        )
        authenticate_incident.assert_called_once_with(
            pair_root,
            incident_path,
            assignments[0],
            {},
            expected_attempt=1,
        )

    @mock.patch.object(campaign, "verify_pair_freeze_against_metadata")
    @mock.patch.object(run_matrix, "_authenticate_matrix_incident")
    @mock.patch.object(
        campaign,
        "planned_pair_assignments",
        return_value=[
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ],
    )
    def test_archive_accepts_incident_authenticated_retained_artifact(
        self,
        _planned: mock.Mock,
        authenticate_incident: mock.Mock,
        _verify_freeze: mock.Mock,
    ) -> None:
        pair_id = "P01-T1-rep-01"
        pair_root = (
            self.root
            / "pair_attempts"
            / pair_id
            / "attempt-1-slurm-123"
        )
        incidents = pair_root / "incidents"
        incidents.mkdir(parents=True)
        (pair_root / "freeze_check.json").write_text("{}", encoding="utf-8")
        artifact = incidents / "retained.agent_log.artifact"
        artifact.write_bytes(b"authenticated retained log\n")
        incident: dict[str, object] = {
            "planned_run_id": f"{pair_id}-N",
            "matrix_attempt": 1,
            "matrix_incident": {
                "status": "aborted_after_unscorable_useful_work",
                "retry_allowed": False,
                "scored": False,
                "final_assignment_record_written": False,
            },
            "failure_code": "NO_SUBMISSION",
            "useful_work_started": True,
            "agent_log": artifact.relative_to(pair_root).as_posix(),
            "agent_log_sha256": hashlib.sha256(artifact.read_bytes()).hexdigest(),
            "validation_log": None,
            "validation_log_sha256": None,
        }
        incident["matrix_incident_sha256"] = run_matrix.matrix_incident_digest(
            incident
        )
        incident_path = incidents / f"{pair_id}-N.attempt-1.json"
        incident_path.write_text(json.dumps(incident), encoding="utf-8")
        authenticate_incident.return_value = incident
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": "attempt-1-slurm-123",
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)

        updated = campaign.archive_failed_attempt(
            self.root,
            self.benchmark,
            index,
            pair_id,
            "123",
            2,
            "matrix_error",
        )

        failed = updated["failed_pair_attempts"][0]
        self.assertEqual(failed["final_record_count"], 0)
        self.assertEqual(len(failed["incidents"]), 1)
        self.assertEqual(failed["outcome"], "matrix_error")
        self.assertIsNone(updated["active_pair_attempt"])
        self.assertGreaterEqual(authenticate_incident.call_count, 2)

    def test_failed_root_rejects_unbound_symlinked_or_tampered_incident_artifact(
        self,
    ) -> None:
        assignments = [
            {"run_id": "P01-T1-rep-01-N"},
            {"run_id": "P01-T1-rep-01-L"},
        ]
        for name in ("unbound", "symlink", "tampered", "outside", "wrong-suffix"):
            with self.subTest(name=name):
                pair_root = Path(self.temporary.name) / f"artifact-{name}"
                incidents = pair_root / "incidents"
                incidents.mkdir(parents=True)
                incident_path = incidents / "P01-T1-rep-01-N.attempt-1.json"
                incident_path.write_text("{}", encoding="utf-8")
                artifact = incidents / "retained.agent_log.artifact"
                target = pair_root / "target.log"
                target.write_bytes(b"retained log\n")
                if name == "symlink":
                    artifact.symlink_to(target)
                else:
                    artifact.write_bytes(target.read_bytes())
                digest = hashlib.sha256(b"retained log\n").hexdigest()
                authenticated = []
                if name != "unbound":
                    authenticated = [
                        {
                            "agent_log": (
                                "attempts/retained.agent_log.artifact"
                                if name == "outside"
                                else (
                                    "incidents/retained.agent_log.txt"
                                    if name == "wrong-suffix"
                                    else artifact.relative_to(pair_root).as_posix()
                                )
                            ),
                            "agent_log_sha256": (
                                "0" * 64 if name == "tampered" else digest
                            ),
                            "validation_log": None,
                            "validation_log_sha256": None,
                        }
                    ]
                with self.assertRaises(campaign.CampaignError):
                    campaign.validate_failed_runner_temporaries(
                        pair_root,
                        assignments,
                        authenticated_incidents=authenticated,
                    )

    @mock.patch.object(campaign, "planned_pair_assignments", return_value=[])
    def test_recover_empty_active_attempt_retains_and_indexes_path(self, _planned: mock.Mock) -> None:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        pair_root.mkdir(parents=True)
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        updated = campaign.recover_active_attempt(self.root, self.benchmark, index)
        self.assertTrue(pair_root.is_dir())
        self.assertEqual(updated["failed_pair_attempts"][0]["outcome"], "interrupted_job")

    @mock.patch.object(campaign, "planned_pair_assignments", return_value=[])
    @mock.patch.object(campaign, "metadata_snapshot", side_effect=lambda _root: snapshot())
    def test_index_first_missing_root_survives_status_then_cli_recovery(
        self, _snapshot: mock.Mock, _planned: mock.Mock
    ) -> None:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        relative = Path("pair_attempts") / pair_id / attempt_id
        self.root.mkdir()
        (self.root / "pair_attempts").mkdir()
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": relative.as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        arguments = [
            "--campaign-root",
            str(self.root),
            "--benchmark-root",
            str(self.benchmark),
        ]
        with redirect_stdout(io.StringIO()):
            self.assertEqual(campaign.main([*arguments, "status"]), 0)
            self.assertEqual(campaign.main([*arguments, "recover-active"]), 0)
        recovered = campaign.load_and_verify_index(self.root, self.benchmark)
        self.assertIsNone(recovered["active_pair_attempt"])
        self.assertEqual(
            recovered["failed_pair_attempts"][0]["outcome"], "interrupted_job"
        )
        self.assertTrue((self.root / relative).is_dir())

    @mock.patch.object(campaign, "planned_pair_assignments", return_value=[])
    def test_recover_uses_existing_nonzero_exit_marker(self, _planned: mock.Mock) -> None:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        pair_root.mkdir(parents=True)
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)
        updated = campaign.recover_active_attempt(self.root, self.benchmark, index)
        self.assertEqual(updated["failed_pair_attempts"][0]["outcome"], "matrix_error")
        self.assertEqual(updated["failed_pair_attempts"][0]["matrix_exit_code"], 2)

    @mock.patch.object(campaign, "planned_pair_assignments", return_value=[])
    def test_matrix_error_without_terminal_or_active_evidence_is_rejected(self, _planned: mock.Mock) -> None:
        pair_id = "P01-T1-rep-01"
        attempt_id = "attempt-1-slurm-123"
        pair_root = self.root / "pair_attempts" / pair_id / attempt_id
        pair_root.mkdir(parents=True)
        index = fresh_index()
        index["active_pair_attempt"] = {
            "pair_id": pair_id,
            "attempt_id": attempt_id,
            "path": pair_root.relative_to(self.root).as_posix(),
            "slurm_job_id": "123",
            "allocation_node": "watgpu108",
            "started_at_utc": "2026-08-13T00:00:00Z",
        }
        campaign.write_matrix_exit_marker(pair_root, pair_id, "123", 2)
        (pair_root / "attempts").mkdir()
        (pair_root / "attempts" / "unbound-partial.json").write_text(
            "{}", encoding="utf-8"
        )
        with self.assertRaisesRegex(campaign.CampaignError, "neither an exact setup error"):
            campaign.archive_failed_attempt(
                self.root,
                self.benchmark,
                index,
                pair_id,
                "123",
                2,
                "matrix_error",
            )


if __name__ == "__main__":
    unittest.main()
