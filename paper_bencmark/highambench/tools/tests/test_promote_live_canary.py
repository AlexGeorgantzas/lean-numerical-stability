from __future__ import annotations

from pathlib import Path
import tempfile
import unittest
from unittest import mock

from paper_bencmark.highambench.tools.common import (
    BenchmarkToolError,
    read_json,
    write_json,
)
from paper_bencmark.highambench.tools import promote_live_canary as promote


class PromoteLiveCanaryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.project = Path(self.temporary.name)
        self.root = self.project / "paper_bencmark" / "highambench"
        (self.root / "metadata" / "evidence").mkdir(parents=True)
        self.config = {
            "benchmark_id": "fixture-benchmark",
            "limits": {"total_model_tokens": 100_000},
            "frozen_environment": {
                "agent_id": "codex-cli",
                "agent_version": "fixture",
                "agent_binary_sha256": "a" * 64,
                "model_version": "gpt-5.6-sol",
                "model_reasoning_effort": "ultra",
                "ultra_orchestration": {"enabled": True},
                "prompt_protocol": {"version": "fixture-production-prompt-v1"},
            },
        }
        self.execution_components = {
            field: format(index, "064x")
            for index, field in enumerate(
                promote.run_matrix.EXECUTION_COMPONENT_FIELDS, start=1
            )
        }
        self.environment = {
            "agent": {
                "prompt_protocol": {"version": "fixture-production-prompt-v1"}
            },
            "isolation": dict(self.execution_components),
        }
        write_json(self.root / "metadata/config.json", self.config)
        write_json(self.root / "metadata/environment.json", self.environment)
        write_json(
            self.root / "metadata/manifest.json",
            {"papers": [{"paper_id": "P01"}]},
        )
        write_json(self.root / "metadata/release_files.json", {"old": True})
        write_json(
            self.root / promote.TOKEN_EVIDENCE_RELATIVE,
            {"status": "replacement_required"},
        )
        write_json(
            self.root / promote.ULTRA_EVIDENCE_RELATIVE,
            {"status": "replacement_required"},
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    @staticmethod
    def fake_sync(
        root: Path,
        config: dict,
        environment: dict,
        manifest: dict,
        *,
        corpus_slug: str,
    ) -> tuple[str, str, int]:
        environment["environment_id"] = f"highambench-{corpus_slug}-fixture"
        environment["release_manifest_sha256"] = "b" * 64
        write_json(root / "metadata/config.json", config)
        write_json(root / "metadata/environment.json", environment)
        write_json(root / "metadata/release_files.json", {"promoted": True})
        return "b" * 64, "c" * 64, 3

    def test_requires_an_explicit_attestation(self) -> None:
        with self.assertRaisesRegex(BenchmarkToolError, "at least one explicit"):
            promote.promote(self.root, self.project)

    def test_both_named_candidates_are_validated_and_promoted(self) -> None:
        token_source = self.project / "results" / "token.json"
        ultra_source = self.project / "results" / "ultra.json"
        write_json(token_source, {"kind": "token-candidate"})
        write_json(ultra_source, {"kind": "ultra-candidate"})
        with mock.patch.object(
            promote.token_canary,
            "validate_attestation_document",
            return_value={"status": "passed", "kind": "token"},
        ) as token_validate, mock.patch.object(
            promote.ultra_canary,
            "verify_evidence_document",
            return_value={"status": "passed", "kind": "ultra"},
        ) as ultra_validate, mock.patch.object(
            promote.refresh_snapshot,
            "_sync_release_and_environment",
            side_effect=self.fake_sync,
        ):
            result = promote.promote(
                self.root,
                self.project,
                token_control_attestation=token_source,
                ultra_orchestration_attestation=ultra_source,
            )
        token_validate.assert_called_once()
        ultra_validate.assert_called_once()
        self.assertEqual(
            ultra_validate.call_args.kwargs["expected_prompt_protocol"],
            {"version": "fixture-production-prompt-v1"},
        )
        self.assertEqual(
            ultra_validate.call_args.kwargs["expected_execution_components"],
            self.execution_components,
        )
        self.assertEqual(
            read_json(self.root / promote.TOKEN_EVIDENCE_RELATIVE)["kind"],
            "token-candidate",
        )
        self.assertEqual(
            read_json(self.root / promote.ULTRA_EVIDENCE_RELATIVE)["kind"],
            "ultra-candidate",
        )
        config = read_json(self.root / "metadata/config.json")
        environment = read_json(self.root / "metadata/environment.json")
        for key in ("token_control_canary", "ultra_orchestration_canary"):
            self.assertEqual(config["frozen_environment"][key]["status"], "passed")
            self.assertEqual(environment[key], config["frozen_environment"][key])
        self.assertFalse(result["benchmark_task_files_modified"])

    def test_validation_failure_makes_no_metadata_change(self) -> None:
        source = self.project / "results" / "ultra-invalid.json"
        write_json(source, {"kind": "invalid"})
        before = {
            path: path.read_bytes()
            for path in (
                self.root / "metadata/config.json",
                self.root / "metadata/environment.json",
                self.root / "metadata/release_files.json",
                self.root / promote.ULTRA_EVIDENCE_RELATIVE,
            )
        }
        with mock.patch.object(
            promote.ultra_canary,
            "verify_evidence_document",
            side_effect=BenchmarkToolError("invalid evidence"),
        ):
            with self.assertRaisesRegex(BenchmarkToolError, "invalid evidence"):
                promote.promote(
                    self.root,
                    self.project,
                    ultra_orchestration_attestation=source,
                )
        for path, payload in before.items():
            self.assertEqual(path.read_bytes(), payload)

    def test_refresh_failure_rolls_back_promoted_ultra_bytes(self) -> None:
        source = self.project / "results" / "ultra-valid.json"
        write_json(source, {"kind": "ultra-candidate"})
        touched = (
            self.root / "metadata/config.json",
            self.root / "metadata/environment.json",
            self.root / "metadata/release_files.json",
            self.root / promote.ULTRA_EVIDENCE_RELATIVE,
        )
        before = {path: path.read_bytes() for path in touched}

        def failing_sync(
            root: Path,
            config: dict,
            environment: dict,
            manifest: dict,
            *,
            corpus_slug: str,
        ) -> None:
            del manifest, corpus_slug
            write_json(root / "metadata/config.json", {"partially": "updated"})
            write_json(root / "metadata/environment.json", environment)
            write_json(root / "metadata/release_files.json", {"partially": "updated"})
            raise BenchmarkToolError("refresh failed after candidate replacement")

        with mock.patch.object(
            promote.ultra_canary,
            "verify_evidence_document",
            return_value={"status": "passed"},
        ), mock.patch.object(
            promote.refresh_snapshot,
            "_sync_release_and_environment",
            side_effect=failing_sync,
        ):
            with self.assertRaisesRegex(BenchmarkToolError, "refresh failed"):
                promote.promote(
                    self.root,
                    self.project,
                    ultra_orchestration_attestation=source,
                )
        for path, payload in before.items():
            self.assertEqual(path.read_bytes(), payload)


if __name__ == "__main__":
    unittest.main()
