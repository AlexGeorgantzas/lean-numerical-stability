from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, sha256_file, write_json  # noqa: E402
from finalize_paper import finalize_paper  # noqa: E402


class FinalizePaperTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.project = Path(self.temporary.name) / "project"
        self.root = self.project / "paper_bencmark" / "highambench"
        (self.root / "shared" / "HighamBench").mkdir(parents=True)
        (self.root / "tasks").mkdir()
        (self.root / "metadata").mkdir()
        (self.root / "agent_prompt.md").write_text(
            "Fill only the designated proof placeholder.\n", encoding="utf-8"
        )
        (self.project / "lakefile.toml").write_text(
            'name = "fixture"\n', encoding="utf-8"
        )
        (self.project / "lean-toolchain").write_text(
            "leanprover/lean4:v4.29.0-rc3\n", encoding="utf-8"
        )
        (self.project / "lake-manifest.json").write_text(
            '{"version":"1.1.0","packages":[]}\n', encoding="utf-8"
        )
        self.global_sentinels = {
            "metadata/manifest.json": b'{"global":"manifest"}\n',
            "metadata/environment.json": b'{"global":"environment"}\n',
            "metadata/run_order.json": b'{"global":"run-order"}\n',
            "shared/HighamBench/Core.lean": b"-- global Core\n",
            "shared/HighamBench/SemanticCore.lean": b"-- global SemanticCore\n",
        }
        for relative, payload in self.global_sentinels.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
        self._add_paper("P01")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _add_paper(self, paper_id: str) -> None:
        definitions = (
            self.root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        )
        definitions.write_text(
            "import Mathlib.Data.Real.Basic\n\n"
            f"namespace HighamBench.{paper_id}\n"
            "def value : ℝ := 1\n"
            f"end HighamBench.{paper_id}\n",
            encoding="utf-8",
        )
        task_root = self.root / "tasks" / paper_id / "T1"
        task_root.mkdir(parents=True)
        task_id = f"{paper_id}-T1"
        (task_root / "Target.lean").write_text(
            f"import HighamBench.{paper_id}Definitions\n\n"
            f"namespace HighamBench.{paper_id}\n"
            "theorem task : True := by sorry\n"
            f"end HighamBench.{paper_id}\n",
            encoding="utf-8",
        )
        (task_root / "context.md").write_text(
            f"Context for {task_id}.\n", encoding="utf-8"
        )
        write_json(
            task_root / "task.json",
            {
                "schema_version": "highambench-task-0.3",
                "task_id": task_id,
                "paper_id": paper_id,
                "tier": "T1",
                "context_file": (
                    f"paper_bencmark/highambench/tasks/{paper_id}/T1/context.md"
                ),
                "source_tags": ["EQN"],
                "author_label": None,
                "classification_frozen_before_runs": False,
                "source_locations": [{"anchor": "equation (1.1)"}],
            },
        )
        write_json(
            task_root.parent / "paper.json",
            {
                "schema_version": "highambench-paper-0.2",
                "paper_id": paper_id,
                "classification_frozen_before_runs": False,
                "included_tasks": [task_id],
                "source": {"sha256": paper_id[-1] * 64},
            },
        )

    @staticmethod
    def _fake_compiler(
        command: list[str] | tuple[str, ...],
        cwd: Path,
        env: dict[str, str] | object,
    ) -> subprocess.CompletedProcess[str]:
        del cwd, env
        output = Path(command[command.index("-o") + 1])
        source = Path(command[-1])
        payload = b"fake-olean-v1\0" + hashlib.sha256(source.read_bytes()).digest()
        output.write_bytes(payload)
        return subprocess.CompletedProcess(command, 0, "")

    def _sentinel_hashes(self) -> dict[str, str]:
        return {
            relative: sha256_file(self.root / relative)
            for relative in self.global_sentinels
        }

    def _bundle_root(self, paper_id: str) -> Path:
        return (
            self.project
            / "paper_bencmark"
            / "scratch_pad"
            / "highambench_environment"
            / "shared_olean"
            / paper_id
        )

    def test_write_builds_exact_bundle_receipt_and_registration(self) -> None:
        before = self._sentinel_hashes()
        result = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            compiler_runner=self._fake_compiler,
        )
        self.assertTrue(result["ok"])
        bundle_root = self._bundle_root("P01")
        files = [
            path.relative_to(bundle_root).as_posix()
            for path in bundle_root.rglob("*")
            if path.is_file()
        ]
        self.assertEqual(files, ["HighamBench/P01Definitions.olean"])

        receipt_path = self.root / "metadata" / "papers" / "P01" / "bundle.json"
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        self.assertEqual(receipt["schema_version"], "highambench-paper-bundle-0.1")
        self.assertEqual(
            receipt["olean_files"][0]["sha256"],
            sha256_file(bundle_root / "HighamBench" / "P01Definitions.olean"),
        )
        basis = {
            "paper_id": "P01",
            "definition_source": receipt["definition_source"],
            "olean_files": receipt["olean_files"],
        }
        expected_digest = hashlib.sha256(
            json.dumps(basis, sort_keys=True, separators=(",", ":")).encode("utf-8")
        ).hexdigest()
        self.assertEqual(receipt["bundle_sha256"], expected_digest)
        self.assertTrue(
            (self.root / "metadata" / "papers" / "P01" / "registration.json").is_file()
        )
        self.assertEqual(before, self._sentinel_hashes())

        checked = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            mode="check",
            compiler_runner=self._fake_compiler,
        )
        self.assertEqual(checked["written"], [])

    def test_does_not_read_legacy_global_controlled_manifests(self) -> None:
        legacy = self.root / "metadata" / "controlled"
        legacy.mkdir(parents=True)
        (legacy / "P01-T1.json").symlink_to(legacy / "missing-global-view.json")

        result = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            compiler_runner=self._fake_compiler,
        )

        self.assertTrue(result["ok"])
        self.assertTrue((legacy / "P01-T1.json").is_symlink())
        self.assertTrue(
            (
                self.root
                / "metadata"
                / "papers"
                / "P01"
                / "controlled"
                / "T1.json"
            ).is_file()
        )

    def test_replaces_and_archives_legacy_bundle_by_content_hash(self) -> None:
        old_root = self._bundle_root("P01")
        (old_root / "HighamBench").mkdir(parents=True)
        (old_root / "HighamBench" / "Core.olean").write_bytes(b"old core")
        (old_root / "HighamBench" / "P01Definitions.olean").write_bytes(b"old defs")

        result = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            compiler_runner=self._fake_compiler,
        )
        retired = [path for path in result["written"] if "retired_shared_olean" in path]
        self.assertEqual(len(retired), 1)
        retired_root = self.project / retired[0]
        self.assertEqual(
            (retired_root / "HighamBench" / "Core.olean").read_bytes(), b"old core"
        )
        current_files = sorted(
            path.relative_to(old_root).as_posix()
            for path in old_root.rglob("*")
            if path.is_file()
        )
        self.assertEqual(current_files, ["HighamBench/P01Definitions.olean"])

        second = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            compiler_runner=self._fake_compiler,
        )
        self.assertEqual(second["written"], [])

    def test_dry_run_compiles_and_validates_without_repository_writes(self) -> None:
        before = self._sentinel_hashes()
        result = finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            mode="dry-run",
            compiler_runner=self._fake_compiler,
        )
        self.assertEqual(result["written"], [])
        self.assertFalse(self._bundle_root("P01").exists())
        self.assertFalse((self.root / "metadata" / "papers").exists())
        self.assertEqual(before, self._sentinel_hashes())

    def test_two_papers_finalize_concurrently_with_disjoint_writes(self) -> None:
        self._add_paper("P02")
        before = self._sentinel_hashes()
        with ThreadPoolExecutor(max_workers=2) as executor:
            futures = [
                executor.submit(
                    finalize_paper,
                    self.root,
                    paper_id,
                    phase="construction",
                    project_root=self.project,
                    compiler_runner=self._fake_compiler,
                )
                for paper_id in ("P01", "P02")
            ]
            results = [future.result() for future in futures]
        self.assertEqual({item["paper_id"] for item in results}, {"P01", "P02"})
        self.assertEqual(before, self._sentinel_hashes())
        for paper_id in ("P01", "P02"):
            bundle = self._bundle_root(paper_id)
            self.assertEqual(
                [
                    path.relative_to(bundle).as_posix()
                    for path in bundle.rglob("*")
                    if path.is_file()
                ],
                [f"HighamBench/{paper_id}Definitions.olean"],
            )

    def test_forbidden_highambench_import_fails_without_writes(self) -> None:
        definitions = self.root / "shared" / "HighamBench" / "P01Definitions.lean"
        definitions.write_text("import HighamBench.Core\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "forbidden import"):
            finalize_paper(
                self.root,
                "P01",
                phase="construction",
                project_root=self.project,
                mode="dry-run",
                compiler_runner=self._fake_compiler,
            )
        self.assertFalse(self._bundle_root("P01").exists())

    def test_check_rejects_stale_bundle_without_mutating_it(self) -> None:
        finalize_paper(
            self.root,
            "P01",
            phase="construction",
            project_root=self.project,
            compiler_runner=self._fake_compiler,
        )
        olean = self._bundle_root("P01") / "HighamBench" / "P01Definitions.olean"
        olean.write_bytes(b"tampered")
        before = olean.read_bytes()
        with self.assertRaisesRegex(BenchmarkToolError, "bundle is missing or stale"):
            finalize_paper(
                self.root,
                "P01",
                phase="construction",
                project_root=self.project,
                mode="check",
                compiler_runner=self._fake_compiler,
            )
        self.assertEqual(olean.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
