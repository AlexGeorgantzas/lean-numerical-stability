from __future__ import annotations

import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import aggregate_highambench_pair_shards as aggregate
import manage_highambench_pair_shard as campaign


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


def snapshot(paper_id: str) -> dict[str, object]:
    pairs = [
        canonical_pair(f"{paper_id}-T{tier}-rep-0{repetition}")
        for tier in range(1, 4)
        for repetition in range(1, 4)
    ]
    policy = json.loads(json.dumps(campaign.run_matrix.HARDWARE_MATCHING_POLICY))
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


def fresh_index(paper_id: str, pair_id: str) -> dict[str, object]:
    return campaign.bind_index_hash(
        {
            "schema_version": 1,
            "kind": campaign.INDEX_KIND,
            "paper_id": paper_id,
            "target_pair_id": pair_id,
            **snapshot(paper_id),
            "committed_pairs": {},
            "failed_pair_attempts": [],
            "active_pair_attempt": None,
            "created_at_utc": "2026-08-14T00:00:00Z",
            "updated_at_utc": "2026-08-14T00:00:00Z",
        }
    )


class PairShardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "shard"
        self.benchmark = Path(self.temporary.name) / "benchmark"
        self.benchmark.mkdir()
        campaign.configure_target("P05", "P05-T1-rep-01")

    def test_configure_target_rejects_unsupported_and_cross_paper_pair(self) -> None:
        with self.assertRaisesRegex(campaign.CampaignError, "paper ID must be"):
            campaign.configure_target("P01", "P01-T1-rep-01")
        with self.assertRaisesRegex(campaign.CampaignError, "not canonical"):
            campaign.configure_target("P05", "P11-T1-rep-01")

    def test_all_supported_papers_have_exact_nine_pair_ids(self) -> None:
        order = {
            "pairs": [
                {
                    "pair_id": f"{paper}-T{tier}-rep-0{rep}",
                    "task_id": f"{paper}-T{tier}",
                    "repetition_id": f"rep-0{rep}",
                    "condition_order": ["N", "L"],
                    "run_ids": [
                        f"{paper}-T{tier}-rep-0{rep}-N",
                        f"{paper}-T{tier}-rep-0{rep}-L",
                    ],
                    "sha256": "a" * 64,
                }
                for paper in campaign.SUPPORTED_PAPER_IDS
                for tier in range(1, 4)
                for rep in range(1, 4)
            ]
        }
        for paper in campaign.SUPPORTED_PAPER_IDS:
            with self.subTest(paper=paper):
                campaign.configure_target(paper, f"{paper}-T1-rep-01")
                pairs = campaign.canonical_pairs(order)
                self.assertEqual(len(pairs), 9)
                self.assertEqual(
                    [item["pair_id"] for item in pairs],
                    aggregate.canonical_pair_ids(paper),
                )

    @mock.patch.object(campaign, "metadata_snapshot")
    def test_initialize_exposes_only_target_as_next(self, metadata: mock.Mock) -> None:
        metadata.return_value = snapshot("P05")
        index = campaign.initialize(self.root, self.benchmark)
        status = campaign.status_payload(index)
        self.assertEqual(status["target_pair_id"], "P05-T1-rep-01")
        self.assertEqual(status["next_pair_id"], "P05-T1-rep-01")
        self.assertEqual(status["planned_pair_count"], 1)
        self.assertEqual(status["committed_pair_count"], 0)

    @mock.patch.object(campaign, "metadata_snapshot")
    def test_empty_index_round_trip_authenticates(self, metadata: mock.Mock) -> None:
        metadata.return_value = snapshot("P05")
        campaign.initialize(self.root, self.benchmark)
        loaded = campaign.load_and_verify_index(self.root, self.benchmark)
        self.assertEqual(loaded["target_pair_id"], "P05-T1-rep-01")

    @mock.patch.object(campaign, "metadata_snapshot")
    def test_index_rejects_commit_for_another_pair(self, metadata: mock.Mock) -> None:
        metadata.return_value = snapshot("P05")
        index = campaign.initialize(self.root, self.benchmark)
        index["committed_pairs"] = {
            "P05-T1-rep-02": {"pair_id": "P05-T1-rep-02"}
        }
        campaign.atomic_write_json(
            campaign.index_path(self.root), campaign.bind_index_hash(index)
        )
        with self.assertRaisesRegex(campaign.CampaignError, "exact target"):
            campaign.load_and_verify_index(self.root, self.benchmark)

    @mock.patch.object(campaign, "metadata_snapshot")
    def test_begin_rejects_other_pair_and_uses_permanent_target_path(
        self, metadata: mock.Mock
    ) -> None:
        metadata.return_value = snapshot("P05")
        index = campaign.initialize(self.root, self.benchmark)
        with self.assertRaisesRegex(campaign.CampaignError, "next canonical pair"):
            campaign.begin_attempt(
                self.root, index, "P05-T1-rep-02", "123", "watgpu108"
            )
        _, attempt = campaign.begin_attempt(
            self.root, index, "P05-T1-rep-01", "123", "watgpu108"
        )
        self.assertEqual(
            attempt.relative_to(self.root).as_posix(),
            "pair_attempts/P05-T1-rep-01/attempt-1-slurm-123",
        )

    def test_attempt_serial_counts_only_target_history(self) -> None:
        index = fresh_index("P05", "P05-T1-rep-01")
        index["failed_pair_attempts"] = [
            {
                "pair_id": "P05-T1-rep-01",
                "attempt_id": "attempt-1-slurm-123",
            }
        ]
        self.assertEqual(campaign.attempt_serial(index, "P05-T1-rep-01"), 2)

    def test_index_self_hash_detects_tampering(self) -> None:
        index = fresh_index("P05", "P05-T1-rep-01")
        campaign.verify_index_hash(index)
        index["target_pair_id"] = "P05-T1-rep-02"
        with self.assertRaisesRegex(campaign.CampaignError, "self-hash is stale"):
            campaign.verify_index_hash(index)

    def test_launcher_is_pair_scoped_and_never_promotes_canaries(self) -> None:
        launcher = (
            Path(__file__).resolve().parent
            / "run_highambench_pair_shard_actual_ultra.sh"
        ).read_text(encoding="utf-8")
        self.assertIn('readonly RESULT_ROOT="${SHARDS_ROOT}/${PAIR_ID}"', launcher)
        self.assertIn('exec 9>"${RESULT_ROOT}/.launcher.lock"', launcher)
        self.assertIn('--only-pair-id "$PAIR_ID"', launcher)
        self.assertIn('"${CAMPAIGN_ARGS[@]}"', launcher)
        self.assertIn("require both frozen canary descriptors already passed", launcher)
        self.assertNotIn("promote_live_canary.py", launcher)
        self.assertNotIn("--ultra-orchestration-attestation", launcher)
        self.assertNotIn("--token-control-attestation", launcher)

    def test_canary_bootstrap_is_serial_and_never_runs_a_pair(self) -> None:
        bootstrap = (
            Path(__file__).resolve().parent
            / "run_highambench_canary_bootstrap_actual_ultra.sh"
        ).read_text(encoding="utf-8")
        self.assertIn(".highambench-canary-bootstrap.lock", bootstrap)
        self.assertIn("/usr/bin/flock -n 8", bootstrap)
        self.assertIn("--ultra-orchestration-attestation", bootstrap)
        self.assertIn("--token-control-attestation", bootstrap)
        self.assertIn("--verify-only", bootstrap)
        self.assertNotIn("run_matrix.py", bootstrap)
        self.assertNotIn("--only-pair-id", bootstrap)
        self.assertNotIn("manage_highambench_pair_shard.py\"\n+  --", bootstrap)


class AggregateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "shards"
        self.root.mkdir()
        self.benchmark = Path(self.temporary.name) / "benchmark"
        self.benchmark.mkdir()
        self.pair_ids = aggregate.canonical_pair_ids("P05")
        manager_path = "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py"
        launcher_path = (
            "paper_bencmark/scratch_pad/"
            "run_highambench_pair_shard_actual_ultra.sh"
        )
        ledger_text = "\n".join(
            sorted(
                (
                    f"{'1' * 64}  paper_bencmark/highambench/metadata/manifest.json",
                    f"{'2' * 64}  paper_bencmark/highambench/metadata/run_order.json",
                    f"{'3' * 64}  {manager_path}",
                    f"{'4' * 64}  {launcher_path}",
                )
            )
        ) + "\n"
        for pair_id in self.pair_ids:
            root = self.root / pair_id
            attempt = root / "pair_attempts" / pair_id / "attempt-1-slurm-123"
            attempt.mkdir(parents=True)
            (root / ".campaign.lock").touch()
            (root / ".launcher.lock").touch()
            (attempt / "freeze_check.json").write_text("{}\n", encoding="utf-8")
            (root / "campaign_index.json").write_text("{}\n", encoding="utf-8")
            audit = root / "runbook_audit"
            audit.mkdir()
            ledger = audit / campaign.INITIAL_LEDGER_NAME
            ledger.write_text(ledger_text, encoding="utf-8")
            ledger.chmod(0o444)

    def fake_index(self, pair_id: str) -> dict[str, object]:
        descriptor = {
            "pair_id": pair_id,
            "attempt_id": "attempt-1-slurm-123",
            "path": f"pair_attempts/{pair_id}/attempt-1-slurm-123",
            "final_records": {
                condition: {
                    "run_id": f"{pair_id}-{condition}",
                    "path": f"records/{pair_id}-{condition}.json",
                }
                for condition in ("N", "L")
            },
        }
        return {
            "paper_id": "P05",
            "target_pair_id": pair_id,
            **snapshot("P05"),
            "active_pair_attempt": None,
            "committed_pairs": {pair_id: descriptor},
            "failed_pair_attempts": [],
            campaign.INDEX_HASH_FIELD: "e" * 64,
        }

    def test_aggregate_self_hash_detects_tampering(self) -> None:
        value = aggregate.bind_hash({"schema_version": 1, "kind": aggregate.KIND})
        aggregate.verify_hash(value)
        value["kind"] = "tampered"
        with self.assertRaisesRegex(aggregate.AggregateError, "self-hash is stale"):
            aggregate.verify_hash(value)

    def test_aggregate_rejects_missing_pair_root(self) -> None:
        missing = self.root / self.pair_ids[-1]
        for path in sorted(missing.rglob("*"), reverse=True):
            if path.is_file():
                path.chmod(0o600)
                path.unlink()
            else:
                path.rmdir()
        missing.rmdir()
        with self.assertRaisesRegex(aggregate.AggregateError, "missing or unsafe"):
            aggregate.validate_root_entries(self.root, self.pair_ids)

    @mock.patch.object(aggregate, "ledger_descriptor")
    @mock.patch.object(campaign.run_matrix, "verify_pair_policy_compatible_freeze_checks")
    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "load_and_verify_index")
    def test_build_authenticates_exact_nine_first_success_shards(
        self,
        load: mock.Mock,
        verify_commit: mock.Mock,
        verify_freeze: mock.Mock,
        ledger: mock.Mock,
    ) -> None:
        load.side_effect = lambda root, _benchmark: self.fake_index(root.name)
        ledger.return_value = {
            "path": f"runbook_audit/{campaign.INITIAL_LEDGER_NAME}",
            "sha256": "5" * 64,
            "line_count": 4,
            "manager_sha256": "3" * 64,
            "launcher_sha256": "4" * 64,
        }
        value = aggregate.build(
            self.root,
            self.benchmark,
            "P05",
            created_at_utc="2026-08-14T00:00:00Z",
        )
        self.assertEqual(value["pair_ids"], self.pair_ids)
        self.assertEqual(len(value["pair_shards"]), 9)
        self.assertEqual(verify_commit.call_count, 9)
        self.assertEqual(verify_freeze.call_count, 8)
        self.assertEqual(ledger.call_count, 9)
        aggregate.verify_hash(value)

    @mock.patch.object(campaign, "load_and_verify_index")
    def test_build_rejects_active_shard(self, load: mock.Mock) -> None:
        def side_effect(root: Path, _benchmark: Path) -> dict[str, object]:
            value = self.fake_index(root.name)
            if root.name == self.pair_ids[0]:
                value["active_pair_attempt"] = {"pair_id": root.name}
            return value

        load.side_effect = side_effect
        with self.assertRaisesRegex(aggregate.AggregateError, "remains active"):
            aggregate.build(self.root, self.benchmark, "P05")

    @mock.patch.object(campaign, "verify_committed_index_descriptor")
    @mock.patch.object(campaign, "load_and_verify_index")
    def test_build_rejects_stale_final_identity(
        self, load: mock.Mock, _verify_commit: mock.Mock
    ) -> None:
        def side_effect(root: Path, _benchmark: Path) -> dict[str, object]:
            value = self.fake_index(root.name)
            if root.name == self.pair_ids[0]:
                value["committed_pairs"][root.name]["final_records"]["N"][
                    "run_id"
                ] = "P05-T1-rep-01-L"
            return value

        load.side_effect = side_effect
        with self.assertRaisesRegex(aggregate.AggregateError, "identity is stale"):
            aggregate.build(self.root, self.benchmark, "P05")

    def test_atomic_aggregate_publication_is_sealed(self) -> None:
        path = self.root / aggregate.INDEX_NAME
        aggregate.atomic_write(path, aggregate.bind_hash({"kind": aggregate.KIND}))
        self.assertEqual(path.stat().st_mode & 0o777, 0o444)

    def test_shard_root_rejects_unindexed_top_level_artifact(self) -> None:
        shard_root = self.root / self.pair_ids[0]
        (shard_root / "foreign.txt").write_text("unexpected\n", encoding="utf-8")
        with self.assertRaisesRegex(aggregate.AggregateError, "top-level entries"):
            aggregate.validate_shard_root_entries(shard_root)

    @mock.patch.object(aggregate, "expected_ledger_paths")
    def test_ledger_descriptor_recomputes_claimed_hashes(
        self, expected_paths: mock.Mock
    ) -> None:
        project = Path(self.temporary.name) / "project"
        project.mkdir()
        source = project / "input.txt"
        source.write_text("bound bytes\n", encoding="utf-8")
        manager = project / "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py"
        launcher = project / "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh"
        manager.parent.mkdir(parents=True)
        manager.write_text("manager\n", encoding="utf-8")
        launcher.write_text("launcher\n", encoding="utf-8")
        expected = {
            "input.txt": campaign.file_sha256(source),
            manager.relative_to(project).as_posix(): campaign.file_sha256(manager),
            launcher.relative_to(project).as_posix(): campaign.file_sha256(launcher),
        }
        expected_paths.return_value = (project, set(expected))
        shard_root = self.root / self.pair_ids[0]
        ledger = shard_root / "runbook_audit" / campaign.INITIAL_LEDGER_NAME
        ledger.chmod(0o600)
        ledger.write_text(
            "".join(
                f"{digest}  {relative}\n"
                for relative, digest in sorted(expected.items())
            ),
            encoding="utf-8",
        )
        ledger.chmod(0o444)
        aggregate.ledger_descriptor(shard_root, self.benchmark, "P05")
        source.write_text("changed bytes\n", encoding="utf-8")
        with self.assertRaisesRegex(aggregate.AggregateError, "digest is stale"):
            aggregate.ledger_descriptor(shard_root, self.benchmark, "P05")


if __name__ == "__main__":
    unittest.main()
