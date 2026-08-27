from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, sha256_file, write_json  # noqa: E402
from paper_registry import (  # noqa: E402
    BUNDLE_KIND,
    BUNDLE_SCHEMA,
    CONSTRUCTION_EVIDENCE_KIND,
    CONSTRUCTION_EVIDENCE_SCHEMA,
    REVIEW_EVIDENCE_KIND,
    REVIEW_EVIDENCE_SCHEMA,
    compose_registration_catalog,
    discover_paper_registrations,
    finalize_paper,
    plan_paper_registration,
)
from check_construction import publish_paper_construction_evidence  # noqa: E402


class PaperRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / "benchmark"
        (self.root / "metadata" / "controlled").mkdir(parents=True)
        (self.root / "shared" / "HighamBench").mkdir(parents=True)
        (self.root / "tasks").mkdir(parents=True)
        (self.root / "agent_prompt.md").write_text(
            "Fill the designated proof.\n", encoding="utf-8"
        )
        self.global_sentinels = {
            "metadata/manifest.json": b'{"global":"manifest"}\n',
            "metadata/config.json": b'{"global":"config"}\n',
            "metadata/environment.json": b'{"global":"environment"}\n',
            "metadata/run_order.json": b'{"global":"run-order"}\n',
            "metadata/release_files.json": b'{"global":"release"}\n',
            "metadata/controlled/legacy.json": b'{"global":"controlled"}\n',
            "shared/HighamBench/Core.lean": b"-- global Core sentinel\n",
            "shared/HighamBench/SemanticCore.lean": (
                b"-- global SemanticCore sentinel\n"
            ),
        }
        for relative, payload in self.global_sentinels.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
        self._add_paper("P02")
        self._add_paper("P01")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _add_paper(self, paper_id: str, *, tier: str = "T1") -> None:
        definitions = (
            self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        )
        definitions.write_text(
            "import Mathlib.Data.Real.Basic\n\n"
            "namespace HighamBench\n"
            f"def {paper_id.lower()}Value : ℝ := 1\n"
            "end HighamBench\n",
            encoding="utf-8",
        )
        paper_root = self.root / "tasks" / paper_id
        task_root = paper_root / tier
        task_root.mkdir(parents=True)
        task_id = f"{paper_id}-{tier}"
        (task_root / "Target.lean").write_text(
            f"import HighamBench.{paper_id}Definitions\n\n"
            "namespace HighamBench\n"
            f"theorem {paper_id.lower()}_{tier.lower()} : True := by sorry\n"
            "end HighamBench\n",
            encoding="utf-8",
        )
        (task_root / "context.md").write_text(
            f"Context for {task_id}.\n", encoding="utf-8"
        )
        task_record = {
            "schema_version": "highambench-task-0.4" if tier == "T4" else "highambench-task-0.3",
            "task_id": task_id,
            "paper_id": paper_id,
            "tier": tier,
            "context_file": (
                f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/context.md"
            ),
            "source_tags": ["EQN"],
            "author_label": None,
            "classification_frozen_before_runs": False,
            "source_locations": [{"anchor": "equation (1.1)"}],
        }
        if tier == "T4":
            task_record["declarations"] = []
        write_json(
            task_root / "task.json",
            task_record,
        )
        write_json(
            paper_root / "paper.json",
            {
                "schema_version": "highambench-paper-0.2",
                "paper_id": paper_id,
                "classification_frozen_before_runs": False,
                "included_tasks": [task_id],
                "source": {"sha256": paper_id[-1] * 64},
            },
        )

    def _sentinel_hashes(self) -> dict[str, str]:
        return {
            relative: sha256_file(self.root / relative)
            for relative in self.global_sentinels
        }

    @staticmethod
    def _canonical_digest(value: object) -> str:
        payload = json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()

    def _write_bundle(
        self,
        paper_id: str,
        *,
        definition_sha256: str | None = None,
        olean_paths: list[str] | None = None,
    ) -> Path:
        definitions = (
            self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        )
        definition_source = {
            "path": f"shared/HighamBench/{paper_id}Definitions.lean",
            "sha256": definition_sha256 or sha256_file(definitions),
            "bytes": definitions.stat().st_size,
        }
        paths = olean_paths or [f"HighamBench/{paper_id}Definitions.olean"]
        olean_files = [
            {"path": path, "sha256": str(index + 1) * 64, "bytes": 100 + index}
            for index, path in enumerate(paths)
        ]
        basis = {
            "paper_id": paper_id,
            "definition_source": definition_source,
            "olean_files": olean_files,
        }
        destination = (
            self.root / "metadata" / "papers" / paper_id / "bundle.json"
        )
        write_json(
            destination,
            {
                "schema_version": BUNDLE_SCHEMA,
                "kind": BUNDLE_KIND,
                "paper_id": paper_id,
                "pass": True,
                **basis,
                "bundle_sha256": self._canonical_digest(basis),
            },
        )
        return destination

    def _set_measurement_ready(self, paper_id: str) -> None:
        paper_path = self.root / "tasks" / paper_id / "paper.json"
        paper = json.loads(paper_path.read_text(encoding="utf-8"))
        paper["classification_frozen_before_runs"] = True
        write_json(paper_path, paper)
        for task_path in sorted((self.root / "tasks" / paper_id).glob("T*/task.json")):
            task = json.loads(task_path.read_text(encoding="utf-8"))
            task["classification_frozen_before_runs"] = True
            write_json(task_path, task)

    def _write_evidence(
        self,
        paper_id: str,
        *,
        name: str,
        schema: str,
        kind: str,
        controlled_manifest_sha256: dict[str, str],
    ) -> Path:
        paper_path = self.root / "tasks" / paper_id / "paper.json"
        task_paths = sorted((self.root / "tasks" / paper_id).glob("T*/task.json"))
        destination = self.root / "metadata" / "papers" / paper_id / f"{name}.json"
        task_ids = list(controlled_manifest_sha256)
        paper_record_sha256 = sha256_file(paper_path)
        evidence = {
            "schema_version": schema,
            "kind": kind,
            "paper_id": paper_id,
            "pass": True,
            "task_ids": task_ids,
            "definition_source_sha256": sha256_file(
                self.root
                / "shared"
                / "HighamBench"
                / f"{paper_id}Definitions.lean"
            ),
            "paper_record_sha256": paper_record_sha256,
            "task_record_sha256": {
                f"{paper_id}-{path.parent.name}": sha256_file(path)
                for path in task_paths
                if f"{paper_id}-{path.parent.name}" in task_ids
            },
            "controlled_manifest_sha256": controlled_manifest_sha256,
        }
        if name == "construction":
            certificate = {
                "schema_version": 4,
                "kind": "highambench-private-construction-check",
                "pass": True,
                "record_status": "paper_current_final",
                "scope": {
                    "scope_kind": "paper-local",
                    "paper_id": paper_id,
                    "paper_record_sha256": paper_record_sha256,
                    "task_ids": task_ids,
                    "complete_paper_scope": True,
                },
            }
            evidence["certificate"] = certificate
            evidence["certificate_sha256"] = self._canonical_digest(certificate)
            evidence["validation"] = {
                "paper_record_sha256": paper_record_sha256,
                "controlled_manifest_sha256": controlled_manifest_sha256,
            }
        write_json(destination, evidence)
        return destination

    def test_two_papers_finalize_concurrently_without_global_writes(self) -> None:
        before = self._sentinel_hashes()
        with ThreadPoolExecutor(max_workers=2) as executor:
            futures = [
                executor.submit(finalize_paper, self.root, paper_id)
                for paper_id in ("P01", "P02")
            ]
            results = [future.result() for future in futures]

        self.assertEqual({result["paper_id"] for result in results}, {"P01", "P02"})
        self.assertEqual(before, self._sentinel_hashes())
        for paper_id in ("P01", "P02"):
            self.assertTrue(
                (self.root / "metadata" / "papers" / paper_id / "registration.json").is_file()
            )
            self.assertTrue(
                (
                    self.root
                    / "metadata"
                    / "papers"
                    / paper_id
                    / "controlled"
                    / "T1.json"
                ).is_file()
            )
            checked = finalize_paper(self.root, paper_id, mode="check")
            self.assertEqual(checked["written"], [])

    def test_two_construction_receipts_publish_concurrently_without_global_writes(
        self,
    ) -> None:
        for paper_id in ("P01", "P02"):
            finalize_paper(self.root, paper_id)
        before = self._sentinel_hashes()

        def environment(paper_id: str) -> SimpleNamespace:
            spec = SimpleNamespace(task_id=f"{paper_id}-T1")
            return SimpleNamespace(
                paper_local=True,
                selected_paper_ids=(paper_id,),
                benchmark_root=self.root,
                specs=(spec, spec),
            )

        def validate_paper(
            current: SimpleNamespace, _evidence: object
        ) -> dict[str, object]:
            paper_id = current.selected_paper_ids[0]
            registration = plan_paper_registration(self.root, paper_id).registration
            controlled = {
                str(task["task_id"]): str(task["controlled_manifest"]["sha256"])
                for task in registration["tasks"]
            }
            return {
                "paper_record_sha256": registration["paper_record"]["sha256"],
                "controlled_manifest_sha256": controlled,
            }

        def certificate(paper_id: str) -> dict[str, object]:
            registration = plan_paper_registration(self.root, paper_id).registration
            return {
                "schema_version": 4,
                "kind": "highambench-private-construction-check",
                "pass": True,
                "record_status": "paper_current_final",
                "scope": {
                    "scope_kind": "paper-local",
                    "paper_id": paper_id,
                    "paper_record_sha256": registration["paper_record"]["sha256"],
                    "task_ids": list(registration["task_ids"]),
                    "complete_paper_scope": True,
                },
            }

        with ThreadPoolExecutor(max_workers=2) as executor:
            futures = [
                executor.submit(
                    publish_paper_construction_evidence,
                    environment(paper_id),
                    certificate(paper_id),
                    evidence_validator=validate_paper,
                )
                for paper_id in ("P01", "P02")
            ]
            results = [future.result() for future in futures]

        self.assertEqual({item["paper_id"] for item in results}, {"P01", "P02"})
        self.assertEqual(before, self._sentinel_hashes())
        for paper_id in ("P01", "P02"):
            receipt = self.root / "metadata" / "papers" / paper_id / "construction.json"
            self.assertTrue(receipt.is_file())
            registration = plan_paper_registration(self.root, paper_id).registration
            self.assertEqual(
                registration["readiness_artifacts"]["construction"]["status"],
                "authenticated",
            )
            self.assertEqual(
                registration["readiness_artifacts"]["review"]["status"],
                "not-applicable",
            )

    def test_dry_run_reports_exact_write_set_and_writes_nothing(self) -> None:
        result = finalize_paper(self.root, "P01", mode="dry-run")
        self.assertEqual(
            [item["path"] for item in result["write_set"]],
            [
                "metadata/papers/P01/controlled/T1.json",
                "metadata/papers/P01/registration.json",
            ],
        )
        self.assertTrue(all(item["state"] == "missing" for item in result["write_set"]))
        self.assertFalse((self.root / "metadata" / "papers").exists())
        self.assertFalse(
            (
                self.root
                / "metadata"
                / "papers"
                / "P01"
                / "controlled"
                / "T1.json"
            ).exists()
        )

    def test_discovery_and_composition_are_deterministic(self) -> None:
        finalize_paper(self.root, "P02")
        finalize_paper(self.root, "P01")
        first = compose_registration_catalog(self.root)
        second = compose_registration_catalog(self.root)
        self.assertEqual(first, second)
        self.assertEqual(first["paper_ids"], ["P01", "P02"])
        self.assertEqual(first["task_ids"], ["P01-T1", "P02-T1"])
        self.assertEqual(
            [value["paper_id"] for value in discover_paper_registrations(self.root)],
            ["P01", "P02"],
        )
        original_registration = (
            self.root / "metadata" / "papers" / "P01" / "registration.json"
        ).read_bytes()
        finalize_paper(self.root, "P01")
        self.assertEqual(
            original_registration,
            (
                self.root
                / "metadata"
                / "papers"
                / "P01"
                / "registration.json"
            ).read_bytes(),
        )
        self.assertEqual(first, compose_registration_catalog(self.root))

    def test_rejects_core_semantic_core_and_cross_paper_imports(self) -> None:
        definitions = (
            self.root / "shared" / "HighamBench" / "P01Definitions.lean"
        )
        for forbidden in (
            "HighamBench.Core",
            "HighamBench.SemanticCore",
            "HighamBench.P02Definitions",
        ):
            with self.subTest(forbidden=forbidden):
                definitions.write_text(f"import {forbidden}\n", encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkToolError, "forbidden import"):
                    finalize_paper(self.root, "P01", mode="dry-run")

        definitions.write_text("import Mathlib.Data.Real.Basic\n", encoding="utf-8")
        target = self.root / "tasks" / "P01" / "T1" / "Target.lean"
        target.write_text("import HighamBench.P02Definitions\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "must import exactly"):
            finalize_paper(self.root, "P01", mode="dry-run")

    def test_check_rejects_stale_registration(self) -> None:
        finalize_paper(self.root, "P01")
        context = self.root / "tasks" / "P01" / "T1" / "context.md"
        context.write_text("revised context\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "missing or stale"):
            finalize_paper(self.root, "P01", mode="check")

    def test_registration_has_no_time_or_global_manifest_dependency(self) -> None:
        finalize_paper(self.root, "P01")
        path = self.root / "metadata" / "papers" / "P01" / "registration.json"
        document = json.loads(path.read_text(encoding="utf-8"))
        self.assertNotIn("generated_at", document)
        serialized = path.read_text(encoding="utf-8")
        self.assertNotIn("metadata/manifest.json", serialized)
        self.assertEqual(
            document["ownership"]["custom_import_closure"],
            ["HighamBench.P01Definitions"],
        )

    def test_construction_registration_reports_pending_or_authenticated_receipts(
        self,
    ) -> None:
        finalize_paper(self.root, "P01")
        registration_path = (
            self.root / "metadata" / "papers" / "P01" / "registration.json"
        )
        registration = json.loads(registration_path.read_text(encoding="utf-8"))
        self.assertEqual(
            {
                name: artifact["status"]
                for name, artifact in registration["readiness_artifacts"].items()
            },
            {"bundle": "pending", "construction": "pending", "review": "not-applicable"},
        )
        self.assertEqual(
            registration["readiness_policy"]["required_artifacts"],
            ["bundle", "construction"],
        )

        bundle_path = self._write_bundle("P01")
        finalize_paper(self.root, "P01")
        registration = json.loads(registration_path.read_text(encoding="utf-8"))
        bundle = registration["readiness_artifacts"]["bundle"]
        self.assertEqual(bundle["status"], "authenticated")
        self.assertEqual(
            bundle["receipt"]["path"], "metadata/papers/P01/bundle.json"
        )
        self.assertEqual(bundle["receipt"]["sha256"], sha256_file(bundle_path))
        self.assertEqual(
            registration["readiness_artifacts"]["construction"]["status"],
            "pending",
        )

    def test_rejects_tampered_embedded_construction_certificate(self) -> None:
        preflight = finalize_paper(self.root, "P01", mode="dry-run")
        controlled = {
            "P01-T1": next(
                str(item["sha256"])
                for item in preflight["write_set"]
                if item["path"] == "metadata/papers/P01/controlled/T1.json"
            )
        }
        path = self._write_evidence(
            "P01",
            name="construction",
            schema=CONSTRUCTION_EVIDENCE_SCHEMA,
            kind=CONSTRUCTION_EVIDENCE_KIND,
            controlled_manifest_sha256=controlled,
        )
        evidence = json.loads(path.read_text(encoding="utf-8"))
        evidence["certificate"]["pass"] = False
        write_json(path, evidence)
        with self.assertRaisesRegex(BenchmarkToolError, "certificate digest"):
            finalize_paper(self.root, "P01", mode="dry-run")

    def test_rejects_stale_or_nonminimal_bundle_receipt(self) -> None:
        self._write_bundle("P01", definition_sha256="f" * 64)
        with self.assertRaisesRegex(BenchmarkToolError, "definition source"):
            finalize_paper(self.root, "P01", mode="dry-run")

        self._write_bundle(
            "P01",
            olean_paths=[
                "HighamBench/P01Definitions.olean",
                "HighamBench/Core.olean",
            ],
        )
        with self.assertRaisesRegex(BenchmarkToolError, "must contain only"):
            finalize_paper(self.root, "P01", mode="dry-run")

        self._write_bundle("P01", olean_paths=["HighamBench/SemanticCore.olean"])
        with self.assertRaisesRegex(BenchmarkToolError, "must contain only"):
            finalize_paper(self.root, "P01", mode="dry-run")

    def test_measurement_ready_requires_all_authenticated_local_artifacts(self) -> None:
        self._set_measurement_ready("P01")
        with self.assertRaisesRegex(
            BenchmarkToolError, "lacks authenticated paper-local artifacts"
        ):
            finalize_paper(self.root, "P01", mode="dry-run")

    def test_measurement_ready_accepts_current_bundle_and_evidence(self) -> None:
        preflight = finalize_paper(self.root, "P01", mode="dry-run")
        controlled = {
            f"P01-{Path(str(item['path'])).stem}": str(item["sha256"])
            for item in preflight["write_set"]
            if str(item["path"]).startswith("metadata/papers/P01/controlled/")
        }
        self._set_measurement_ready("P01")
        self._write_bundle("P01")
        self._write_evidence(
            "P01",
            name="construction",
            schema=CONSTRUCTION_EVIDENCE_SCHEMA,
            kind=CONSTRUCTION_EVIDENCE_KIND,
            controlled_manifest_sha256=controlled,
        )

        finalize_paper(self.root, "P01")
        registration = json.loads(
            (
                self.root
                / "metadata"
                / "papers"
                / "P01"
                / "registration.json"
            ).read_text(encoding="utf-8")
        )
        self.assertEqual(registration["phase"], "measurement-ready")
        self.assertEqual(
            {
                name: artifact["status"]
                for name, artifact in registration["readiness_artifacts"].items()
            },
            {
                "bundle": "authenticated",
                "construction": "authenticated",
                "review": "not-applicable",
            },
        )

        task_path = self.root / "tasks" / "P01" / "T1" / "task.json"
        task = json.loads(task_path.read_text(encoding="utf-8"))
        task["source_locations"] = [{"anchor": "equation (revised)"}]
        write_json(task_path, task)
        with self.assertRaisesRegex(BenchmarkToolError, "task records are stale"):
            finalize_paper(self.root, "P01", mode="dry-run")

    @patch("paper_registry.validate_t4_file_bindings", return_value=None)
    @patch("paper_registry.validate_task_source_tags", return_value={})
    def test_t4_measurement_ready_requires_t4_scoped_review_evidence(
        self, _validate_tags: object, _validate_files: object
    ) -> None:
        self._add_paper("P03", tier="T4")
        preflight = finalize_paper(self.root, "P03", mode="dry-run")
        controlled = {
            "P03-T4": next(
                str(item["sha256"])
                for item in preflight["write_set"]
                if item["path"] == "metadata/papers/P03/controlled/T4.json"
            )
        }
        self._set_measurement_ready("P03")
        self._write_bundle("P03")
        self._write_evidence(
            "P03",
            name="construction",
            schema=CONSTRUCTION_EVIDENCE_SCHEMA,
            kind=CONSTRUCTION_EVIDENCE_KIND,
            controlled_manifest_sha256=controlled,
        )
        with self.assertRaisesRegex(BenchmarkToolError, "review"):
            finalize_paper(self.root, "P03", mode="dry-run")

        self._write_evidence(
            "P03",
            name="review",
            schema=REVIEW_EVIDENCE_SCHEMA,
            kind=REVIEW_EVIDENCE_KIND,
            controlled_manifest_sha256=controlled,
        )
        finalize_paper(self.root, "P03")
        registration = json.loads(
            (
                self.root
                / "metadata"
                / "papers"
                / "P03"
                / "registration.json"
            ).read_text(encoding="utf-8")
        )
        self.assertEqual(
            registration["readiness_policy"],
            {
                "required_artifacts": ["bundle", "construction", "review"],
                "review_required_for_tiers": ["T4"],
                "review_task_ids": ["P03-T4"],
            },
        )
        self.assertEqual(
            registration["readiness_artifacts"]["review"]["status"],
            "authenticated",
        )


if __name__ == "__main__":
    unittest.main()
