from __future__ import annotations

import copy
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
import uuid


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, sha256_file  # noqa: E402
from t4_workspace import (  # noqa: E402
    BASE_GENERIC_CONTRACT_FILES,
    GENERIC_CONTRACT_FILES,
    descriptor_digest,
    manage_workspace,
)
from t4_writer_lease import manage_lease, write_lease_credentials  # noqa: E402


class T4WorkspaceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.benchmark = self.root / "highambench"
        self.references = self.root / "reference_papers"
        self.scratch = self.root / "scratch_pad"
        self.leases: dict[str, tuple[str, str]] = {}
        (self.benchmark / "shared" / "HighamBench").mkdir(parents=True)
        (self.benchmark / "tasks").mkdir()
        self.references.mkdir()
        self.contract_files = {
            name: self.benchmark / relative
            for name, relative in GENERIC_CONTRACT_FILES
        }
        for name, path in self.contract_files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            if name == "task_template":
                payload = {
                    "schema_version": "highambench-task-0.4",
                    "limits": {
                        "total_model_tokens": 5000000,
                        "wall_clock_seconds": 1800,
                    },
                }
            elif name == "source_inventory_template":
                payload = {
                    "schema_version": "highambench-t4-source-inventory-0.3"
                }
            else:
                payload = {"contract": name}
            path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        self._add_paper("P06", pages=6)
        self._add_paper("P07", pages=7)
        self._add_source_only("P08", pages=8)

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

    def _add_source_only(self, paper_id: str, *, pages: int) -> None:
        pdf = self.references / f"{paper_id}_paper title.pdf"
        pdf.write_bytes(
            b"%PDF-1.7\n"
            + f"1 0 obj << /Type /Pages /Count {pages} >> endobj\n".encode()
            + b"%%EOF\n"
        )

    def _sentinel_hashes(self) -> dict[Path, str]:
        return {path: sha256_file(path) for path in self.sentinels}

    def _claim(self, paper_id: str) -> tuple[str, str]:
        existing = self.leases.get(paper_id)
        if existing is not None:
            return existing
        invocation_id = str(uuid.uuid4())
        token = "test-token-" + uuid.uuid4().hex
        manage_lease(
            self.scratch,
            paper_id,
            "claim",
            invocation_id=invocation_id,
            token=token,
        )
        self.leases[paper_id] = (invocation_id, token)
        return invocation_id, token

    def _init(self, paper_id: str) -> dict[str, object]:
        invocation_id, token = self._claim(paper_id)
        return manage_workspace(
            self.benchmark,
            self.references,
            paper_id,
            scratch_root=self.scratch,
            mode="init",
            lease_invocation_id=invocation_id,
            lease_token=token,
        )

    def test_parallel_initialization_has_disjoint_write_sets(self) -> None:
        before = self._sentinel_hashes()
        for paper_id in ("P06", "P07"):
            self._claim(paper_id)

        def initialize(paper_id: str) -> dict[str, object]:
            return self._init(paper_id)

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
        self._init("P06")
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

        with self.assertRaisesRegex(
            BenchmarkToolError, "authentic prior contract.*lease-guarded init"
        ):
            manage_workspace(
                self.benchmark,
                self.references,
                "P06",
                scratch_root=self.scratch,
                mode="check",
            )
        result = self._init("P06")
        self.assertEqual(result["written"], [str(workspace)])
        upgraded = json.loads(workspace.read_text(encoding="utf-8"))
        self.assertEqual(
            set(upgraded["generic_contract_files"]), set(self.contract_files)
        )
        self.assertEqual(upgraded["descriptor_sha256"], descriptor_digest(upgraded))

    def test_init_requires_matching_active_writer_lease_even_when_noop(self) -> None:
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P08" / "workspace.json"
        )
        with self.assertRaisesRegex(BenchmarkToolError, "T4 init requires"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="init",
            )
        self.assertFalse(workspace.exists())

        invocation_id, token = self._claim("P08")
        with self.assertRaisesRegex(BenchmarkToolError, "credentials"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="init",
                lease_invocation_id=invocation_id,
                lease_token="wrong-token-" + "x" * 32,
            )
        self.assertFalse(workspace.exists())

        result = self._init("P08")
        self.assertEqual(result["written"], [str(workspace)])
        before = workspace.read_bytes()
        with self.assertRaisesRegex(BenchmarkToolError, "T4 init requires"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="init",
            )
        self.assertEqual(workspace.read_bytes(), before)
        self.assertEqual(
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="init",
                lease_invocation_id=invocation_id,
                lease_token=token,
            )["written"],
            [],
        )

    def test_owner_only_credential_file_drives_init(self) -> None:
        invocation_id, token = self._claim("P08")
        credential_directory = self.root / "credential"
        credential_directory.mkdir(mode=0o700)
        credential_file = credential_directory / "P08.json"
        write_lease_credentials(
            credential_file,
            self.scratch,
            "P08",
            invocation_id,
            token,
        )
        result = manage_workspace(
            self.benchmark,
            self.references,
            "P08",
            scratch_root=self.scratch,
            mode="init",
            lease_credential_file=credential_file,
        )
        self.assertEqual(len(result["written"]), 1)
        self.assertNotIn(token, json.dumps(result))
        with self.assertRaisesRegex(BenchmarkToolError, "cannot be combined"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="init",
                lease_invocation_id=invocation_id,
                lease_credential_file=credential_file,
            )

    def test_init_rejects_authenticated_but_modified_legacy_descriptors(self) -> None:
        self._init("P06")
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
                    self._init("P06")
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
        self._init("P06")
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
        self._init("P06")
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


    def test_scaffold_creates_only_explicitly_incomplete_owned_files(self) -> None:
        invocation_id, token = self._claim("P08")
        self._init("P08")
        result = manage_workspace(
            self.benchmark,
            self.references,
            "P08",
            scratch_root=self.scratch,
            mode="scaffold",
            lease_invocation_id=invocation_id,
            lease_token=token,
        )
        expected = {
            self.benchmark / "shared" / "HighamBench" / "P08Definitions.lean",
            self.benchmark / "tasks" / "P08" / "T4" / "Target.lean",
            self.benchmark / "tasks" / "P08" / "T4" / "context.md",
            self.benchmark / "tasks" / "P08" / "T4" / "source_inventory.json",
            self.benchmark / "tasks" / "P08" / "T4" / "task.json",
            self.scratch / "private_gold" / "P08" / "T4_N.lean",
            self.scratch / "private_gold" / "P08" / "T4_L.lean",
        }
        self.assertEqual(set(map(Path, result["written"])), expected)

        definitions = (
            self.benchmark / "shared" / "HighamBench" / "P08Definitions.lean"
        )
        target = self.benchmark / "tasks" / "P08" / "T4" / "Target.lean"
        inventory_path = (
            self.benchmark / "tasks" / "P08" / "T4" / "source_inventory.json"
        )
        task_path = self.benchmark / "tasks" / "P08" / "T4" / "task.json"
        self.assertEqual(
            definitions.read_text(encoding="utf-8").splitlines()[0],
            "import Mathlib.Data.Real.Basic",
        )
        target_text = target.read_text(encoding="utf-8")
        self.assertEqual(
            target_text.splitlines()[0], "import HighamBench.P08Definitions"
        )
        self.assertIn("NON-BENCHMARK STARTER", target_text)
        self.assertNotIn("PROOF_START", target_text)
        self.assertNotIn("sorry", target_text)
        context = (
            self.benchmark / "tasks" / "P08" / "T4" / "context.md"
        ).read_text(encoding="utf-8")
        self.assertIn("durable-artifact-policy.v1.md", context)
        self.assertIn("Hidden reasoning", context)

        inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
        task = json.loads(task_path.read_text(encoding="utf-8"))
        self.assertEqual(inventory["items"], [])
        self.assertEqual(task["source_inventory"], [])
        self.assertEqual(task["declarations"], [])
        self.assertEqual(task["review_units"], [])
        self.assertEqual(task["faithfulness_reviews"], [])
        self.assertFalse(task["classification_frozen_before_runs"])
        self.assertEqual(
            task["construction_inputs"]["paper_definitions_sha256"],
            sha256_file(definitions),
        )
        self.assertEqual(
            task["construction_inputs"]["target_sha256"], sha256_file(target)
        )
        self.assertEqual(
            task["construction_inputs"]["source_inventory_sha256"],
            sha256_file(inventory_path),
        )
        self.assertNotIn("__", inventory_path.read_text(encoding="utf-8"))
        self.assertNotIn("__", task_path.read_text(encoding="utf-8"))
        for condition in ("N", "L"):
            private = (
                self.scratch / "private_gold" / "P08" / f"T4_{condition}.lean"
            ).read_text(encoding="utf-8")
            self.assertIn("intentionally not a", private)
            self.assertIn("proof-complete", private)
            self.assertNotIn("sorry", private)

        before = {path: sha256_file(path) for path in expected}
        with self.assertRaisesRegex(BenchmarkToolError, "existing destination"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P08",
                scratch_root=self.scratch,
                mode="scaffold",
                lease_invocation_id=invocation_id,
                lease_token=token,
            )
        self.assertEqual(before, {path: sha256_file(path) for path in expected})

    def test_scaffold_preflight_refuses_one_existing_destination_without_writes(
        self,
    ) -> None:
        self._add_source_only("P09", pages=9)
        invocation_id, token = self._claim("P09")
        self._init("P09")
        context = self.benchmark / "tasks" / "P09" / "T4" / "context.md"
        context.parent.mkdir(parents=True)
        context.write_text("user-owned context\n", encoding="utf-8")
        with self.assertRaisesRegex(BenchmarkToolError, "existing destination"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P09",
                scratch_root=self.scratch,
                mode="scaffold",
                lease_invocation_id=invocation_id,
                lease_token=token,
            )
        self.assertEqual(context.read_text(encoding="utf-8"), "user-owned context\n")
        self.assertFalse(
            (
                self.benchmark
                / "shared"
                / "HighamBench"
                / "P09Definitions.lean"
            ).exists()
        )
        self.assertFalse(
            (self.benchmark / "tasks" / "P09" / "T4" / "Target.lean").exists()
        )
        self.assertFalse((self.scratch / "private_gold" / "P09").exists())

    def test_scaffold_requires_matching_active_writer_lease(self) -> None:
        self._add_source_only("P10", pages=10)
        self._init("P10")
        with self.assertRaisesRegex(BenchmarkToolError, "active lease"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P10",
                scratch_root=self.scratch,
                mode="scaffold",
            )
        invocation_id, _ = self._claim("P10")
        with self.assertRaisesRegex(BenchmarkToolError, "credentials"):
            manage_workspace(
                self.benchmark,
                self.references,
                "P10",
                scratch_root=self.scratch,
                mode="scaffold",
                lease_invocation_id=invocation_id,
                lease_token="wrong-token-" + "x" * 32,
            )
        self.assertFalse(
            (
                self.benchmark
                / "shared"
                / "HighamBench"
                / "P10Definitions.lean"
            ).exists()
        )

    def test_init_upgrades_exact_prior_four_contract_descriptor(self) -> None:
        self._init("P06")
        workspace = (
            self.scratch / "t4_source_faithfulness" / "P06" / "workspace.json"
        )
        legacy = json.loads(workspace.read_text(encoding="utf-8"))
        base_names = {name for name, _ in BASE_GENERIC_CONTRACT_FILES}
        legacy["generic_contract_files"] = {
            name: value
            for name, value in legacy["generic_contract_files"].items()
            if name in base_names
        }
        legacy["descriptor_sha256"] = descriptor_digest(legacy)
        workspace.write_text(
            json.dumps(legacy, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        result = self._init("P06")
        self.assertEqual(result["written"], [str(workspace)])
        upgraded = json.loads(workspace.read_text(encoding="utf-8"))
        self.assertEqual(
            set(upgraded["generic_contract_files"]), set(self.contract_files)
        )

if __name__ == "__main__":
    unittest.main()
