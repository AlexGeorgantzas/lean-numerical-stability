from __future__ import annotations

import copy
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, sha256_file  # noqa: E402
from t4_workspace import descriptor_digest, manage_workspace  # noqa: E402


class T4WorkspaceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.benchmark = self.root / "highambench"
        self.references = self.root / "reference_papers"
        self.scratch = self.root / "scratch_pad"
        (self.benchmark / "shared" / "HighamBench").mkdir(parents=True)
        (self.benchmark / "tasks").mkdir()
        self.references.mkdir()
        self.contract_files = {
            "task_schema": (
                self.benchmark / "schemas" / "highambench-t4-task-0.4.schema.json"
            ),
            "source_inventory_schema": (
                self.benchmark
                / "schemas"
                / "highambench-t4-source-inventory-0.3.schema.json"
            ),
            "task_template": (
                self.benchmark / "templates" / "T4" / "task.pending.template.json"
            ),
            "source_inventory_template": (
                self.benchmark
                / "templates"
                / "T4"
                / "source_inventory.pending.template.json"
            ),
        }
        for name, path in self.contract_files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"contract": name}) + "\n", encoding="utf-8")
        self._add_paper("P06", pages=6)
        self._add_paper("P07", pages=7)

        self.sentinels = {
            self.benchmark / "metadata" / "manifest.json": b'{"global":true}\n',
            self.benchmark / "shared" / "HighamBench" / "Core.lean": b"-- core\n",
            self.benchmark
            / "shared"
            / "HighamBench"
            / "SemanticCore.lean": b"-- semantic core\n",
            self.benchmark
            / "shared"
            / "HighamBench"
            / "P01Definitions.lean": b"import Mathlib\n",
            self.benchmark
            / "tasks"
            / "P01"
            / "T4"
            / "Target.lean": b"-- immutable P01 target\n",
            self.scratch
            / "t4_source_faithfulness"
            / "P01"
            / "workspace.json": b'{"historical":"P01"}\n',
        }
        for path, payload in self.sentinels.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _add_paper(self, paper_id: str, *, pages: int) -> None:
        definitions = (
            self.benchmark
            / "shared"
            / "HighamBench"
            / f"{paper_id}Definitions.lean"
        )
        definitions.write_text(
            "import Mathlib.Data.Real.Basic\n\n"
            f"namespace HighamBench.{paper_id}\n"
            "def value : ℝ := 1\n"
            f"end HighamBench.{paper_id}\n",
            encoding="utf-8",
        )
        pdf = self.references / f"{paper_id}_paper title.pdf"
        pdf.write_bytes(
            b"%PDF-1.7\n"
            + f"1 0 obj << /Type /Pages /Count {pages} >> endobj\n".encode()
            + b"%%EOF\n"
        )

    def _sentinel_hashes(self) -> dict[Path, str]:
        return {path: sha256_file(path) for path in self.sentinels}

    def test_parallel_initialization_has_disjoint_write_sets(self) -> None:
        before = self._sentinel_hashes()

        def initialize(paper_id: str) -> dict[str, object]:
            return manage_workspace(
                self.benchmark,
                self.references,
                paper_id,
                scratch_root=self.scratch,
            )

        with ThreadPoolExecutor(max_workers=2) as executor:
            results = list(executor.map(initialize, ("P06", "P07")))

        write_sets = [
            {(item["root"], item["path"]) for item in result["write_set"]}
            for result in results
        ]
        self.assertTrue(write_sets[0].isdisjoint(write_sets[1]))
        contract_bindings: list[dict[str, object]] = []
        for paper_id, write_set in zip(("P06", "P07"), write_sets, strict=True):
            self.assertEqual(
                write_set,
                {
                    ("benchmark", f"shared/HighamBench/{paper_id}Definitions.lean"),
                    ("benchmark", f"tasks/{paper_id}/paper.json"),
                    ("benchmark", f"tasks/{paper_id}/T4"),
                    ("scratch", f"private_gold/{paper_id}"),
                    (
                        "scratch",
                        f"t4_source_faithfulness/{paper_id}",
                    ),
                },
            )
            contract_paths = {
                ("benchmark", path.relative_to(self.benchmark).as_posix())
                for path in self.contract_files.values()
            }
            self.assertTrue(write_set.isdisjoint(contract_paths))
        self.assertEqual(before, self._sentinel_hashes())

        for paper_id, pages, result in zip(("P06", "P07"), (6, 7), results):
            workspace = (
                self.scratch
                / "t4_source_faithfulness"
                / paper_id
                / "workspace.json"
            )
            self.assertEqual(result["written"], [str(workspace)])
            descriptor = json.loads(workspace.read_text(encoding="utf-8"))
            contract_bindings.append(descriptor["generic_contract_files"])
            self.assertEqual(descriptor["paper_id"], paper_id)
            self.assertEqual(descriptor["source_pdf"]["page_count"], pages)
            self.assertEqual(
                descriptor["source_pdf"]["sha256"],
                sha256_file(self.references / f"{paper_id}_paper title.pdf"),
            )
            self.assertEqual(
                descriptor["controlled_files"]["target"]["path"],
                f"tasks/{paper_id}/T4/Target.lean",
            )
            self.assertEqual(
                descriptor["artifacts"]["campaign_root"]["path"],
                f"t4_source_faithfulness/{paper_id}/review_campaigns",
            )
            self.assertEqual(
                descriptor["descriptor_sha256"], descriptor_digest(descriptor)
            )
            self.assertEqual(
                set(descriptor["generic_contract_files"]), set(self.contract_files)
            )
            for name, path in self.contract_files.items():
                binding = descriptor["generic_contract_files"][name]
                self.assertEqual(binding["root"], "benchmark")
                self.assertEqual(
                    binding["path"], path.relative_to(self.benchmark).as_posix()
                )
                self.assertEqual(binding["kind"], "file")
                self.assertEqual(binding["sha256"], sha256_file(path))
                self.assertEqual(binding["bytes"], path.stat().st_size)
            checked = manage_workspace(
                self.benchmark,
                self.references,
                paper_id,
                scratch_root=self.scratch,
                mode="check",
            )
            self.assertEqual(checked["written"], [])

        self.assertEqual(contract_bindings[0], contract_bindings[1])

        leftovers = list(self.scratch.rglob(".workspace.json.tmp-*"))
        self.assertEqual(leftovers, [])

    def test_write_set_mode_does_not_create_workspace(self) -> None:
        result = manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
            mode="write-set",
        )
        self.assertEqual(result["written"], [])
        self.assertFalse(
            (self.scratch / "t4_source_faithfulness" / "P06").exists()
        )

    def test_init_upgrades_only_an_authentic_pre_contract_descriptor(self) -> None:
        manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
        )
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P06" / "workspace.json"
        )
        legacy = json.loads(workspace.read_text(encoding="utf-8"))
        legacy.pop("generic_contract_files")
        legacy["ownership"]["write_set"] = [
            reference
            for reference in legacy["ownership"]["write_set"]
            if reference["path"] != "tasks/P06/paper.json"
        ]
        legacy["descriptor_sha256"] = descriptor_digest(legacy)
        workspace.write_text(
            json.dumps(legacy, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        with self.assertRaisesRegex(BenchmarkToolError, "generic_contract_files"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="check",
            )
        result = manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
            mode="init",
        )
        self.assertEqual(result["written"], [str(workspace)])
        upgraded = json.loads(workspace.read_text(encoding="utf-8"))
        self.assertEqual(
            set(upgraded["generic_contract_files"]), set(self.contract_files)
        )
        self.assertEqual(upgraded["descriptor_sha256"], descriptor_digest(upgraded))

    def test_init_rejects_authenticated_but_modified_legacy_descriptors(self) -> None:
        manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
        )
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P06" / "workspace.json"
        )
        legacy = json.loads(workspace.read_text(encoding="utf-8"))
        legacy.pop("generic_contract_files")
        legacy["ownership"]["write_set"] = [
            reference
            for reference in legacy["ownership"]["write_set"]
            if reference["path"] != "tasks/P06/paper.json"
        ]
        changes = {
            "other paper": lambda value: value.__setitem__("paper_id", "P07"),
            "root drift": lambda value: value["roots"].__setitem__(
                "scratch", str(self.root / "other-scratch")
            ),
            "writer drift": lambda value: value["ownership"].__setitem__(
                "single_writer", "P07"
            ),
            "workspace drift": lambda value: value["artifacts"].__setitem__(
                "workspace_file",
                {
                    "root": "scratch",
                    "path": "t4_source_faithfulness/P07/workspace.json",
                    "kind": "file",
                },
            ),
            "artifact tamper": lambda value: value["artifacts"][
                "packet_root"
            ].__setitem__("path", "t4_source_faithfulness/P06/other-packets"),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                modified = copy.deepcopy(legacy)
                change(modified)
                modified["descriptor_sha256"] = descriptor_digest(modified)
                payload = json.dumps(modified, indent=2, sort_keys=True) + "\n"
                workspace.write_text(payload, encoding="utf-8")
                with self.assertRaises(BenchmarkToolError):
                    manage_workspace(
                        self.benchmark,
                        self.references,
                        "P06",
                        scratch_root=self.scratch,
                        mode="init",
                    )
                self.assertEqual(workspace.read_text(encoding="utf-8"), payload)

    def test_rejects_shared_and_foreign_imports_before_writing(self) -> None:
        definitions = (
            self.benchmark / "shared" / "HighamBench" / "P06Definitions.lean"
        )
        for module in ("HighamBench.Core", "HighamBench.SemanticCore"):
            with self.subTest(module=module):
                definitions.write_text(f"import {module}\n", encoding="utf-8")
                with self.assertRaisesRegex(BenchmarkToolError, "forbidden shared import"):
                    manage_workspace(
                        self.benchmark,
                        self.references,
                        "P06",
                        scratch_root=self.scratch,
                    )

        definitions.write_text("import Mathlib.Data.Real.Basic\n", encoding="utf-8")
        target = self.benchmark / "tasks" / "P06" / "T4" / "Target.lean"
        target.parent.mkdir(parents=True)
        target.write_text("import HighamBench.P07Definitions\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "foreign HighamBench import"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
            )
        self.assertFalse(
            (self.scratch / "t4_source_faithfulness" / "P06").exists()
        )

    def test_rejects_tampered_out_of_scope_binding(self) -> None:
        manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
        )
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P06" / "workspace.json"
        )
        descriptor = json.loads(workspace.read_text(encoding="utf-8"))
        descriptor["artifacts"]["packet_root"]["path"] = "../P01/packets"
        descriptor["descriptor_sha256"] = descriptor_digest(descriptor)
        workspace.write_text(
            json.dumps(descriptor, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(BenchmarkToolError, "unsafe|outside|escapes"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="check",
            )

    def test_requires_exactly_one_matching_pdf(self) -> None:
        (self.references / "P06_second.pdf").write_bytes(b"%PDF-1.4\n%%EOF\n")
        with self.assertRaisesRegex(BenchmarkToolError, "exactly one"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="write-set",
            )

    def test_requires_regular_non_symlink_generic_contract_files(self) -> None:
        missing = self.contract_files["task_schema"]
        missing.unlink()
        with self.assertRaisesRegex(BenchmarkToolError, "generic T4 contract"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="write-set",
            )

        missing.write_text('{"contract":"task_schema"}\n', encoding="utf-8")
        linked = self.contract_files["task_template"]
        target = linked.with_name("task.real.json")
        linked.rename(target)
        linked.symlink_to(target.name)
        with self.assertRaisesRegex(
            BenchmarkToolError, "symlink|generic T4 contract"
        ):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="write-set",
            )

    def test_check_detects_generic_contract_hash_change(self) -> None:
        manage_workspace(
            self.benchmark,
            self.references,
            "P06",
            scratch_root=self.scratch,
        )
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P06" / "workspace.json"
        )
        before = workspace.read_bytes()
        self.contract_files["source_inventory_template"].write_text(
            '{"contract":"tampered"}\n', encoding="utf-8"
        )
        with self.assertRaisesRegex(BenchmarkToolError, "expected binding"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="check",
            )
        self.assertEqual(workspace.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
