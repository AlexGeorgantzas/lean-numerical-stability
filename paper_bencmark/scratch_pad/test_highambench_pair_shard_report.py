from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

SCRATCH_ROOT = Path(__file__).resolve().parent
if str(SCRATCH_ROOT) not in sys.path:
    sys.path.insert(0, str(SCRATCH_ROOT))

import aggregate_highambench_pair_shards as aggregate
import manage_highambench_pair_shard as shard
import report_highambench_pair_shards as report


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bind_record(value: dict[str, object], field: str) -> dict[str, object]:
    result = dict(value)
    result[field] = shard.canonical_sha256(result)
    return result


class Fixture:
    def __init__(self, base: Path, paper_id: str) -> None:
        self.paper_id = paper_id
        self.project = base / "project"
        self.benchmark = self.project / "paper_bencmark/highambench"
        self.scratch = self.project / "paper_bencmark/scratch_pad"
        self.shards = self.scratch / f"{paper_id.lower()}_shards"
        self.benchmark.mkdir(parents=True)
        self.shards.mkdir(parents=True)
        self.pair_specs: list[dict[str, object]] = []
        self.pair_shards: list[dict[str, object]] = []
        self.records: dict[str, Path] = {}
        for index, pair_id in enumerate(aggregate.canonical_pair_ids(paper_id)):
            tier = pair_id.split("-")[1]
            repetition = pair_id.rsplit("-", 1)[-1]
            order = ["N", "L"] if index % 2 == 0 else ["L", "N"]
            pair = {
                "pair_id": pair_id,
                "task_id": f"{paper_id}-{tier}",
                "repetition_id": f"rep-{repetition}",
                "condition_order": order,
                "run_ids": [f"{pair_id}-{condition}" for condition in order],
                "run_order_pair_sha256": f"{index + 1:064x}",
            }
            self.pair_specs.append(pair)
            self.pair_shards.append(self._make_pair(pair, index))
        policy = json.loads(json.dumps(shard.run_matrix.HARDWARE_MATCHING_POLICY))
        self.aggregate = aggregate.bind_hash(
            {
                "schema_version": aggregate.SCHEMA_VERSION,
                "kind": aggregate.KIND,
                "paper_id": paper_id,
                "benchmark_id": "benchmark-fixture",
                "manifest": {
                    "path": "metadata/manifest.json",
                    "sha256": "1" * 64,
                },
                "run_order": {
                    "path": "metadata/run_order.json",
                    "sha256": "2" * 64,
                },
                "environment": {
                    "path": "metadata/environment.json",
                    "environment_id": "environment-fixture",
                    "environment_bundle_sha256": "3" * 64,
                },
                "hardware_matching_policy": policy,
                "hardware_matching_policy_sha256": shard.canonical_sha256(policy),
                "canonical_pairs": self.pair_specs,
                "pair_ids": aggregate.canonical_pair_ids(paper_id),
                "pair_shards": self.pair_shards,
                "common_initial_task_ledger_sha256": "4" * 64,
                "manager_sha256": "5" * 64,
                "launcher_sha256": "6" * 64,
                "created_at_utc": "2026-08-14T00:00:00Z",
            }
        )
        write_json(self.shards / aggregate.INDEX_NAME, self.aggregate)

    def _make_pair(
        self, pair: dict[str, object], index: int
    ) -> dict[str, object]:
        pair_id = str(pair["pair_id"])
        job_id = str(1000 + index)
        node = ("watgpu108", "watgpu508", "watgpu808")[index % 3]
        pair_root = self.shards / pair_id
        attempt_relative = Path(
            f"pair_attempts/{pair_id}/attempt-1-slurm-{job_id}"
        )
        attempt = pair_root / attempt_relative
        records_dir = attempt / "records"
        records_dir.mkdir(parents=True)
        allocation_record = bind_record(
            {
                "schema_version": 2,
                "kind": "highambench-allocation-hardware-record",
                "job_id": job_id,
                "hostname": node,
                "host_class_sha256": f"{index + 20:064x}",
                "scheduler_sharing": {
                    "exclusive": False,
                    "sharing_policy": "partition_forced_oversubscription",
                },
            },
            "record_sha256",
        )
        allocation_path = attempt / f"allocation_hardware/slurm-{job_id}.json"
        write_json(allocation_path, allocation_record)
        allocation = {
            "path": f"allocation_hardware/slurm-{job_id}.json",
            "sha256": file_sha(allocation_path),
            "record_sha256": allocation_record["record_sha256"],
            "job_id": job_id,
        }
        final_records: dict[str, object] = {}
        order = list(pair["condition_order"])
        for condition in order:
            run_id = f"{pair_id}-{condition}"
            passed = not (
                (index == 0 and condition == "N")
                or (index == 1 and condition == "L")
            )
            scored_seconds = (
                1800
                if index == 1 and condition == "L"
                else (100 + index)
                if condition == "N"
                else (90 + index)
            )
            model_tokens = (1000 + index) if condition == "N" else (900 + index)
            failure_code = (
                None
                if passed
                else "TOKEN_LIMIT"
                if index == 1 and condition == "L"
                else "PROOF_ERROR"
            )
            library_use = (
                False if condition == "N" else True if passed else None
            )
            library_declarations = (
                ["NumStability.fixture"] if library_use is True else []
            )
            record = bind_record(
                {
                    "run_id": run_id,
                    "pair_id": pair_id,
                    "paper_id": self.paper_id,
                    "task_id": pair["task_id"],
                    "tier": str(pair["task_id"]).rsplit("-", 1)[-1],
                    "repetition_id": pair["repetition_id"],
                    "condition": condition,
                    "order_index": order.index(condition) + 1,
                    "pair_order": f"{order[0]}-first",
                    "scored": True,
                    "pass": passed,
                    "failure_code": failure_code,
                    "failure_note": "" if passed else "fixture proof failure",
                    "actual_stop_seconds": scored_seconds + 5,
                    "scored_elapsed_seconds": scored_seconds,
                    "first_valid_seconds": scored_seconds if passed else None,
                    "token_usage": {
                        "model_tokens": model_tokens,
                        "input_tokens": model_tokens - 10,
                        "cached_input_tokens": model_tokens - 20,
                        "output_tokens": 10,
                        "thread_count": 4,
                        "response_count": 12,
                        "appserver_response_count": 10,
                    },
                    "agent": {
                        "id": "codex-cli",
                        "version": "fixture",
                        "model": "gpt-fixture",
                        "reasoning_effort": "ultra",
                    },
                    "protocol": {"complete": True},
                    "library_use": library_use,
                    "library_declarations": library_declarations,
                    "allocation_hardware": allocation,
                    "started_at_utc": "2026-08-14T00:01:00+00:00",
                    "finished_at_utc": "2026-08-14T00:02:00+00:00",
                    "final_submission_sha256": "7" * 64 if passed else None,
                },
                "matrix_record_sha256",
            )
            path = records_dir / f"{run_id}.json"
            write_json(path, record)
            self.records[run_id] = path
            final_records[condition] = {
                "run_id": run_id,
                "path": f"records/{run_id}.json",
                "sha256": file_sha(path),
                "matrix_record_sha256": record["matrix_record_sha256"],
            }
        campaign_index_path = pair_root / "campaign_index.json"
        write_json(campaign_index_path, {"fixture": pair_id})
        failures: list[dict[str, object]] = []
        if index == 0:
            failures.append(
                {
                    "pair_id": pair_id,
                    "attempt_id": f"attempt-0-slurm-{job_id}0",
                    "path": f"pair_attempts/{pair_id}/attempt-0-slurm-{job_id}0",
                    "slurm_job_id": f"{job_id}0",
                    "allocation_node": node,
                    "started_at_utc": "2026-08-13T23:00:00Z",
                    "archived_at_utc": "2026-08-13T23:30:00Z",
                    "outcome": "matrix_error",
                    "matrix_exit_code": 2,
                    "final_record_count": 0,
                    "incidents": [
                        {
                            "path": f"incidents/{pair_id}-N.attempt-1.json",
                            "sha256": "8" * 64,
                            "matrix_incident_sha256": "9" * 64,
                        }
                    ],
                    "last_chunk_status": None,
                    "file_count": 4,
                    "total_bytes": 100,
                    "tree_sha256": "a" * 64,
                }
            )
        commit = {
            "pair_id": pair_id,
            "attempt_id": f"attempt-1-slurm-{job_id}",
            "path": attempt_relative.as_posix(),
            "slurm_job_id": job_id,
            "allocation_node": node,
            "started_at_utc": "2026-08-14T00:00:30Z",
            "committed_at_utc": "2026-08-14T00:03:00Z",
            "file_count": 6,
            "total_bytes": 1000,
            "tree_sha256": "b" * 64,
            "pair_commit": {
                "path": (attempt_relative / "pair_commit.json").as_posix(),
                "sha256": f"{index + 40:064x}",
                "pair_commit_sha256": f"{index + 50:064x}",
            },
            "final_records": final_records,
            "allocation_hardware": allocation,
            "freeze_check_sha256": "c" * 64,
            "hardware_matching_policy_sha256": "d" * 64,
        }
        return {
            "pair_id": pair_id,
            "shard_root": pair_id,
            "shard_index": {
                "path": f"{pair_id}/campaign_index.json",
                "sha256": file_sha(campaign_index_path),
                "campaign_index_sha256": f"{index + 60:064x}",
            },
            "committed_attempt": commit,
            "failed_pair_attempt_count": len(failures),
            "failed_pair_attempts": failures,
            "initial_task_ledger": {
                "path": "runbook_audit/fixture.sha256",
                "sha256": "e" * 64,
                "line_count": 1,
                "manager_sha256": "5" * 64,
                "launcher_sha256": "6" * 64,
            },
        }

    def refresh_final_descriptor(self, run_id: str) -> None:
        pair_id, condition = run_id.rsplit("-", 1)
        record = json.loads(self.records[run_id].read_text(encoding="utf-8"))
        descriptor = next(
            value for value in self.pair_shards if value["pair_id"] == pair_id
        )["committed_attempt"]["final_records"][condition]
        descriptor["sha256"] = file_sha(self.records[run_id])
        descriptor["matrix_record_sha256"] = record["matrix_record_sha256"]


class PairShardReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.fixture = Fixture(self.base, "P05")

    def collect(self) -> tuple[dict[str, object], dict[str, bytes]]:
        return report.collect_report(
            self.fixture.shards,
            self.fixture.benchmark,
            "P05",
            self.fixture.aggregate,
            created_at_utc="2026-08-14T01:00:00Z",
        )

    def test_exact_runs_pairs_deltas_failures_and_caveats(self) -> None:
        source_before = {
            path: file_sha(path)
            for path in self.fixture.shards.rglob("*")
            if path.is_file()
        }
        manifest, artifacts = self.collect()
        runs = json.loads(artifacts["runs.json"])["runs"]
        pairs = json.loads(artifacts["pairs.json"])["pairs"]
        failures = json.loads(artifacts["failed_attempts.json"])["failed_attempts"]
        summary = json.loads(artifacts["summary.json"])
        self.assertEqual(len(runs), 18)
        self.assertEqual(len(pairs), 9)
        self.assertEqual(pairs[0]["l_minus_n_scored_seconds"], -10)
        self.assertEqual(pairs[0]["l_minus_n_model_tokens"], -100)
        self.assertEqual(pairs[0]["l_minus_n_pass"], 1)
        self.assertTrue(all(pair["same_authenticated_allocation"] for pair in pairs))
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]["outcome"], "matrix_error")
        self.assertEqual(summary["analysis"]["run_count"], 18)
        token_failure = next(
            run for run in runs if run["run_id"] == "P05-T1-rep-02-L"
        )
        self.assertFalse(token_failure["pass"])
        self.assertEqual(token_failure["failure_code"], "TOKEN_LIMIT")
        self.assertIsNone(token_failure["library_use"])
        self.assertEqual(
            token_failure["library_use_status"], "not_audited_failed_l_run"
        )
        self.assertEqual(token_failure["library_declarations"], [])
        self.assertEqual(
            summary["analysis"]["library_use"][
                "failed_l_run_without_completed_audit_count"
            ],
            1,
        )
        self.assertIn("may differ across pairs", summary["caveats"]["cross_pair_hardware"])
        self.assertIn(b"pooled absolute times are descriptive only", artifacts["report.md"])
        report.verify_bound_hash(summary, report.SUMMARY_HASH_FIELD, "summary")
        report.verify_bound_hash(manifest, report.MANIFEST_HASH_FIELD, "manifest")
        source_after = {
            path: file_sha(path)
            for path in self.fixture.shards.rglob("*")
            if path.is_file()
        }
        self.assertEqual(source_before, source_after)

    def test_stale_final_file_digest_fails_closed(self) -> None:
        path = self.fixture.records["P05-T1-rep-01-N"]
        path.write_text(path.read_text(encoding="utf-8") + " ", encoding="utf-8")
        with self.assertRaisesRegex(report.ReportError, "file SHA-256 is stale"):
            self.collect()

    def test_scored_l_token_failure_preserves_unaudited_library_state(self) -> None:
        _manifest, artifacts = self.collect()
        runs = json.loads(artifacts["runs.json"])["runs"]
        token_failure = next(
            run for run in runs if run["run_id"] == "P05-T1-rep-02-L"
        )
        self.assertTrue(token_failure["scored"])
        self.assertFalse(token_failure["pass"])
        self.assertEqual(token_failure["failure_code"], "TOKEN_LIMIT")
        self.assertIsNone(token_failure["library_use"])
        self.assertEqual(token_failure["library_declarations"], [])
        self.assertEqual(
            token_failure["library_use_status"], "not_audited_failed_l_run"
        )

    def test_passing_l_record_cannot_claim_unaudited_library_state(self) -> None:
        run_id = "P05-T1-rep-01-L"
        path = self.fixture.records[run_id]
        record = json.loads(path.read_text(encoding="utf-8"))
        record["library_use"] = None
        record["library_declarations"] = []
        record.pop("matrix_record_sha256")
        record = bind_record(record, "matrix_record_sha256")
        write_json(path, record)
        self.fixture.refresh_final_descriptor(run_id)
        with self.assertRaisesRegex(
            report.ReportError, "passing L record lacks a library-use classification"
        ):
            self.collect()

    def test_mismatched_committed_allocation_fails_closed(self) -> None:
        run_id = "P05-T1-rep-01-L"
        path = self.fixture.records[run_id]
        record = json.loads(path.read_text(encoding="utf-8"))
        record["allocation_hardware"] = dict(record["allocation_hardware"])
        record["allocation_hardware"]["job_id"] = "999999"
        record.pop("matrix_record_sha256")
        record = bind_record(record, "matrix_record_sha256")
        write_json(path, record)
        self.fixture.refresh_final_descriptor(run_id)
        with self.assertRaisesRegex(report.ReportError, "committed pair allocation"):
            self.collect()

    @mock.patch.object(aggregate, "verify_existing")
    def test_publish_verify_and_tamper_detection(self, verify: mock.Mock) -> None:
        verify.return_value = self.fixture.aggregate
        manifest, artifacts = self.collect()
        output = self.fixture.scratch / "authenticated_report"
        report.publish(output, manifest, artifacts)
        self.assertEqual(output.stat().st_mode & 0o777, 0o555)
        self.assertTrue(
            all(path.stat().st_mode & 0o777 == 0o444 for path in output.iterdir())
        )
        verified = report.verify_existing_report(
            output, self.fixture.shards, self.fixture.benchmark, "P05"
        )
        self.assertEqual(
            verified[report.MANIFEST_HASH_FIELD], manifest[report.MANIFEST_HASH_FIELD]
        )
        output.chmod(0o755)
        markdown = output / "report.md"
        markdown.chmod(0o644)
        markdown.write_text("tampered\n", encoding="utf-8")
        markdown.chmod(0o444)
        output.chmod(0o555)
        with self.assertRaisesRegex(report.ReportError, "digest is stale"):
            report.verify_existing_report(
                output, self.fixture.shards, self.fixture.benchmark, "P05"
            )

    def test_cli_output_is_scratch_only_and_disjoint(self) -> None:
        output = self.fixture.scratch / "safe_report"
        resolved, scratch = report.validate_output_path(
            output, self.fixture.benchmark, self.fixture.shards
        )
        self.assertEqual(resolved, output)
        self.assertEqual(scratch, self.fixture.scratch.resolve())
        with self.assertRaisesRegex(report.ReportError, "direct, safely named child"):
            report.validate_output_path(
                self.fixture.project / "outside", self.fixture.benchmark, self.fixture.shards
            )
        with self.assertRaisesRegex(report.ReportError, "direct, safely named child"):
            report.validate_output_path(
                self.fixture.shards / "inside", self.fixture.benchmark, self.fixture.shards
            )

    def test_all_supported_papers_project_exact_nine_pairs(self) -> None:
        for paper_id in shard.SUPPORTED_PAPER_IDS:
            with self.subTest(paper_id=paper_id):
                paper_base = self.base / paper_id
                fixture = Fixture(paper_base, paper_id)
                _manifest, artifacts = report.collect_report(
                    fixture.shards,
                    fixture.benchmark,
                    paper_id,
                    fixture.aggregate,
                    created_at_utc="2026-08-14T01:00:00Z",
                )
                self.assertEqual(
                    json.loads(artifacts["pairs.json"])["pair_count"], 9
                )
                self.assertEqual(
                    json.loads(artifacts["runs.json"])["run_count"], 18
                )


if __name__ == "__main__":
    unittest.main()
