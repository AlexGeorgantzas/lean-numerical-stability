from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import write_json  # noqa: E402
from hashes import create_manifest  # noqa: E402
from validator import (  # noqa: E402
    ValidationConfig,
    classify_lean_failure,
    compare_required_surfaces,
    compare_target_signature,
    extract_imports,
    forbidden_source_findings,
    parse_dependency_audit,
    validate,
)


SIGNATURE = "theorem target (n : Nat) : n = n := by\n  rfl\n"


class ValidatorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        self.task = self.workspace / "task"
        self.task.mkdir()
        (self.task / "Canonical.lean").write_text(SIGNATURE, encoding="utf-8")
        self.manifest_path = self.root / "manifest.json"
        write_json(self.manifest_path, create_manifest(self.task))
        self.compiler = self.root / "fake_compile.py"
        self.compiler.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "text = Path(sys.argv[1]).read_text()\n"
            "if 'BAD_SYNTAX' in text:\n"
            "    print('error: unknown identifier BAD_SYNTAX')\n"
            "    raise SystemExit(1)\n"
            "if 'BAD_PROOF' in text:\n"
            "    print('error: unsolved goals')\n"
            "    raise SystemExit(1)\n"
            "Path(sys.argv[2]).write_bytes(b'test olean')\n"
            "print('axioms: []')\n",
            encoding="utf-8",
        )
        self.default_audit = self.root / "fake_audit.py"
        self.default_audit.write_text(
            "import sys\n"
            "candidate, expected = sys.argv[1:]\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tHighamBenchChecked')\n"
            "print('visited\\t1')\n"
            "print('summary\\t0\\t0')\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def config(self, *, condition: str = "N", audit: Path | None = None) -> ValidationConfig:
        return ValidationConfig(
            workspace=self.workspace,
            submission_relative="Submission.lean",
            canonical_relative="task/Canonical.lean",
            target_theorem="target",
            compile_command=[
                sys.executable,
                str(self.compiler),
                "{checked_submission}",
                "{checked_olean}",
            ],
            condition=condition,
            controlled_manifest=self.manifest_path,
            controlled_root_relative="task",
            audit_command=[
                sys.executable,
                str(audit or self.default_audit),
                "{target_theorem}",
                "{expected_theorem}",
            ],
            submission_module="Submission",
        )

    def write_submission(self, value: str = SIGNATURE) -> None:
        (self.workspace / "Submission.lean").write_text(value, encoding="utf-8")

    def audit_reporting_local_modules(self, *modules: str) -> Path:
        audit = self.root / "fake_local_module_audit.py"
        module_rows = "".join(
            f"print('localmodule\\t{module}')\n" for module in modules
        )
        audit.write_text(
            "import sys\n"
            "candidate, expected = sys.argv[1:]\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tHighamBenchChecked')\n"
            + module_rows
            + "print('visited\\t1')\n"
            "print('summary\\t0\\t0')\n",
            encoding="utf-8",
        )
        return audit

    def real_audit_config(self, *, condition: str = "N") -> ValidationConfig:
        elan = shutil.which("elan")
        if elan is not None:
            lean = subprocess.check_output(
                [elan, "which", "lean"], text=True
            ).strip()
        else:
            lean = shutil.which("lean")
        assert lean
        driver = self.root / "trusted_audit_driver.py"
        audit_helper = TOOLS / "dependency_audit.lean"
        driver.write_text(
            "import os, subprocess, sys\n"
            "lean, audit, workspace, module, target, expected_module, expected, local_modules = sys.argv[1:]\n"
            "environment = os.environ.copy()\n"
            "environment['LEAN_PATH'] = workspace + '/task:' + workspace\n"
            "environment['PATH'] = os.path.dirname(lean) + ':/usr/bin:/bin'\n"
            "result = subprocess.run(\n"
            "  [lean, '--run', audit, module, target, expected_module, expected, local_modules],\n"
            "  cwd=workspace, text=True, stdout=subprocess.PIPE, "
            "stderr=subprocess.STDOUT, env=environment)\n"
            "print(result.stdout, end='')\n"
            "raise SystemExit(result.returncode)\n",
            encoding="utf-8",
        )
        return replace(
            self.config(condition=condition),
            compile_command=[
                shutil.which("env") or "/usr/bin/env",
                "LEAN_PATH={workspace}",
                lean,
                "-o",
                "{checked_olean}",
                "{checked_submission}",
            ],
            audit_command=[
                sys.executable,
                str(driver),
                lean,
                str(audit_helper),
                "{workspace}",
                "{submission_module}",
                "{target_theorem}",
                "{expected_module}",
                "{expected_theorem}",
                "{local_modules_file}",
            ],
        )

    def test_accepts_exact_statement_in_hidden_copy(self) -> None:
        self.write_submission()
        result = validate(self.config())
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["controlled_before"]["ok"])
        self.assertTrue(result["controlled_hidden"]["ok"])
        self.assertTrue(result["controlled_after_compile"]["ok"])
        self.assertTrue(result["controlled_after_expected_compile"]["ok"])
        self.assertTrue(result["controlled_after_audit"]["ok"])
        self.assertTrue(result["semantic_statement_check"]["equal"])
        self.assertTrue(
            result["local_modules_side_channel"]["created_after_candidate_compilation"]
        )
        self.assertFalse(
            result["local_modules_side_channel"]["candidate_recompiled_during_audit"]
        )
        self.assertTrue(result["local_modules_side_channel"]["unchanged_after_audit"])
        self.assertIn("HighamBenchChecked_", result["compile"]["command"][-1])

    def test_changed_statement_is_a_rule_violation(self) -> None:
        self.write_submission("theorem target (n : Nat) : n + 0 = n := by\n  rfl\n")
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertFalse(result["statement_check"]["ok"])

    def test_forbidden_constructs_and_condition_n_import(self) -> None:
        self.write_submission("import NumStability\n" + SIGNATURE.replace("rfl", "sorry"))
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        kinds = {finding["kind"] for finding in result["static_findings"]}
        self.assertEqual(kinds, {"forbidden import", "sorry"})

    def test_axiom_hidden_in_candidate_helper_is_rejected(self) -> None:
        (self.workspace / "Helper.lean").write_text(
            "private axiom hidden_helper_fact : True\n", encoding="utf-8"
        )
        self.write_submission("import Helper\n" + SIGNATURE)
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertIn("Helper.lean", result["candidate_inventory"]["scanned_sources"])
        self.assertIn(
            "axiom declaration",
            {finding["kind"] for finding in result["static_findings"]},
        )

    def test_forbidden_import_hidden_in_candidate_helper_is_rejected(self) -> None:
        (self.workspace / "Helper.lean").write_text(
            "import NumStability\ntheorem harmless : True := by trivial\n",
            encoding="utf-8",
        )
        self.write_submission("import Helper\n" + SIGNATURE)
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        helper_findings = [
            finding
            for finding in result["static_findings"]
            if str(finding["path"]).endswith("Helper.lean")
        ]
        self.assertEqual(helper_findings[0]["kind"], "forbidden import")
        self.assertEqual(helper_findings[0]["import"], "NumStability")

    def test_authenticated_submit_rejects_generated_helper_import(self) -> None:
        (self.workspace / "Helper.lean").write_text(
            "theorem helper (n : Nat) : n = n := by rfl\n", encoding="utf-8"
        )
        self.write_submission("import Helper\n" + SIGNATURE)
        result = validate(
            replace(
                self.config(),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        local_imports = [
            finding
            for finding in result["static_findings"]
            if finding["kind"] == "workspace-local module import"
        ]
        self.assertEqual(
            local_imports,
            [
                {
                    "path": str(self.workspace / "Submission.lean"),
                    "kind": "workspace-local module import",
                    "import": "Helper",
                    "candidate_sources": ["Helper.lean"],
                    "resolution": "candidate",
                    "detail": (
                        "authenticated submissions may not import a "
                        "candidate-created module"
                    ),
                }
            ],
        )

    def test_authenticated_submit_accepts_same_file_helper(self) -> None:
        self.write_submission(
            "lemma sameFileHelper (n : Nat) : n = n := by rfl\n\n"
            "theorem target (n : Nat) : n = n := by\n"
            "  exact sameFileHelper n\n"
        )
        result = validate(
            replace(
                self.config(),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["reject_workspace_local_module_imports"])

    def test_authenticated_submit_accepts_controlled_shared_import(self) -> None:
        controlled = self.task / "shared" / "HighamBench" / "Core.lean"
        controlled.parent.mkdir(parents=True)
        controlled.write_text(
            "namespace HighamBench\n"
            "theorem controlledHelper : True := by trivial\n"
            "end HighamBench\n",
            encoding="utf-8",
        )
        write_json(self.manifest_path, create_manifest(self.task))
        self.write_submission("import HighamBench.Core\n" + SIGNATURE)
        result = validate(
            replace(
                self.config(),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertTrue(result["pass"], result)
        self.assertFalse(
            any(
                finding["kind"] == "workspace-local module import"
                for finding in result["static_findings"]
            )
        )

    def test_authenticated_submit_does_not_misclassify_numstability(self) -> None:
        self.write_submission("import NumStability\n" + SIGNATURE)
        result = validate(
            replace(
                self.config(condition="L"),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertTrue(result["pass"], result)
        self.assertFalse(
            any(
                finding["kind"] == "workspace-local module import"
                for finding in result["static_findings"]
            )
        )

    def test_authenticated_submit_accepts_mathlib_and_lean_imports(self) -> None:
        self.write_submission("import Mathlib\nimport Lean\n" + SIGNATURE)
        result = validate(
            replace(
                self.config(),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertTrue(result["pass"], result)
        self.assertFalse(
            any(
                finding["kind"] == "workspace-local module import"
                for finding in result["static_findings"]
            )
        )

    def test_legacy_submit_allows_generated_helper_import_by_default(self) -> None:
        (self.workspace / "Helper.lean").write_text(
            "theorem helper (n : Nat) : n = n := by rfl\n", encoding="utf-8"
        )
        self.write_submission("import Helper\n" + SIGNATURE)
        result = validate(
            self.config(audit=self.audit_reporting_local_modules("Helper"))
        )
        self.assertTrue(result["pass"], result)
        self.assertFalse(result["reject_workspace_local_module_imports"])

    def test_authenticated_submit_fails_closed_on_ambiguous_local_import(self) -> None:
        for directory in ("left", "right"):
            source = self.workspace / directory / "Helper.lean"
            source.parent.mkdir()
            source.write_text(
                "theorem helper (n : Nat) : n = n := by rfl\n",
                encoding="utf-8",
            )
        self.write_submission("import Helper\n" + SIGNATURE)
        result = validate(
            replace(
                self.config(),
                reject_workspace_local_module_imports=True,
            )
        )
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        local_import = next(
            finding
            for finding in result["static_findings"]
            if finding["kind"] == "workspace-local module import"
        )
        self.assertEqual(local_import["resolution"], "ambiguous")
        self.assertEqual(
            local_import["candidate_sources"],
            ["left/Helper.lean", "right/Helper.lean"],
        )

    def test_candidate_olean_without_scanned_source_is_rejected(self) -> None:
        (self.workspace / "HiddenHelper.olean").write_bytes(b"not a trusted module")
        self.write_submission()
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertIn(
            "candidate olean without scanned source",
            {finding["kind"] for finding in result["static_findings"]},
        )

    def test_lake_build_oleans_are_discarded_before_hidden_rebuild(self) -> None:
        generated = (
            self.workspace
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "HighamBench"
            / "Core.olean"
        )
        generated.parent.mkdir(parents=True)
        generated.write_bytes(b"ephemeral lake build output")
        self.write_submission()
        result = validate(self.config())
        self.assertTrue(result["pass"], result)
        self.assertEqual(result["candidate_inventory"]["candidate_oleans"], [])
        self.assertEqual(result["candidate_inventory"]["ignored_build_roots"], [".lake"])

    def test_hidden_validation_copy_does_not_contain_lake_cache(self) -> None:
        generated = self.workspace / ".lake" / "build" / "Hidden.olean"
        generated.parent.mkdir(parents=True)
        generated.write_bytes(b"untrusted cache bytes")
        compiler = self.root / "reject_lake_compile.py"
        compiler.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "if (Path.cwd() / '.lake').exists():\n"
            "    print('hidden copy retained .lake')\n"
            "    raise SystemExit(1)\n"
            "Path(sys.argv[2]).write_bytes(b'test olean')\n"
            "print('axioms: []')\n",
            encoding="utf-8",
        )
        self.write_submission()
        config = replace(
            self.config(),
            compile_command=[
                sys.executable,
                str(compiler),
                "{checked_submission}",
                "{checked_olean}",
            ],
        )
        result = validate(config)
        self.assertTrue(result["pass"], result)

    def test_lake_name_exception_is_exact(self) -> None:
        forged = self.workspace / ".lake-evil" / "HiddenHelper.olean"
        forged.parent.mkdir(parents=True)
        forged.write_bytes(b"untrusted candidate module")
        self.write_submission()
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        self.assertIn(
            "candidate olean without scanned source",
            {finding["kind"] for finding in result["static_findings"]},
        )

    def test_candidate_cannot_shadow_controlled_shared_module(self) -> None:
        controlled = self.task / "shared" / "HighamBench" / "Core.lean"
        controlled.parent.mkdir(parents=True)
        controlled.write_text(
            "namespace HighamBench\ndef protectedValue : Nat := 1\nend HighamBench\n",
            encoding="utf-8",
        )
        write_json(self.manifest_path, create_manifest(self.task))
        forged = self.workspace / "HighamBench" / "Core.lean"
        forged.parent.mkdir()
        forged.write_text(
            "namespace HighamBench\ndef protectedValue : Nat := 0\nend HighamBench\n",
            encoding="utf-8",
        )
        self.write_submission("import HighamBench.Core\n" + SIGNATURE)
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        collisions = [
            finding
            for finding in result["static_findings"]
            if finding["kind"] == "protected module collision"
        ]
        self.assertEqual(
            [finding["module"] for finding in collisions],
            ["HighamBench.Core"],
        )

    def test_condition_l_cannot_forge_numstability_module_ownership(self) -> None:
        forged = self.workspace / "NumStability" / "Candidate.lean"
        forged.parent.mkdir()
        forged.write_text(
            "namespace NumStability\ntheorem candidate : True := by trivial\nend NumStability\n",
            encoding="utf-8",
        )
        self.write_submission("import NumStability.Candidate\n" + SIGNATURE)
        result = validate(self.config(condition="L"))
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        reserved = [
            finding
            for finding in result["static_findings"]
            if finding["kind"] == "reserved library module"
        ]
        self.assertEqual(
            [finding["module"] for finding in reserved],
            ["NumStability.Candidate"],
        )

    def test_olean_cannot_claim_a_shorter_numstability_module_path(self) -> None:
        source = self.workspace / "foo" / "NumStability" / "Candidate.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace NumStability\ntheorem candidate : True := by trivial\nend NumStability\n",
            encoding="utf-8",
        )
        forged_olean = self.workspace / "NumStability" / "Candidate.olean"
        forged_olean.parent.mkdir()
        forged_olean.write_bytes(b"candidate-controlled compiled module")
        self.write_submission("import NumStability.Candidate\n" + SIGNATURE)
        result = validate(self.config(condition="L"))
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        self.assertIn(
            "candidate olean without scanned source",
            {finding["kind"] for finding in result["static_findings"]},
        )

    @unittest.skipUnless(shutil.which("lean"), "Lean executable is unavailable")
    def test_dependency_audit_follows_candidate_helper_module(self) -> None:
        elan = shutil.which("elan")
        lean = (
            subprocess.check_output([elan, "which", "lean"], text=True).strip()
            if elan is not None
            else shutil.which("lean")
        )
        assert lean
        helper = self.workspace / "Helper.lean"
        helper.write_text(
            "namespace Helper\naxiom hidden (n : Nat) : n = n\nend Helper\n",
            encoding="utf-8",
        )
        compiled = subprocess.run(
            [lean, "-o", str(self.workspace / "Helper.olean"), str(helper)],
            cwd=self.workspace,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        self.assertEqual(compiled.returncode, 0, compiled.stdout)
        # Replace the source with an innocent theorem while retaining the stale
        # candidate-created olean. Static scanning now passes, so the dependency
        # audit must still identify the helper-owned axiom used by the target.
        helper.write_text(
            "namespace Helper\n"
            "theorem hidden (n : Nat) : n = n := by rfl\n"
            "end Helper\n",
            encoding="utf-8",
        )
        self.write_submission(
            "import Helper\n"
            "theorem target (n : Nat) : n = n := by\n"
            "  exact Helper.hidden n\n"
        )
        config = self.real_audit_config(condition="L")
        result = validate(config)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        parsed = result["dependency_audit"]["parsed"]
        self.assertIn("Helper", parsed["local_modules"])
        self.assertIn("Helper", parsed["expected_helper_modules"])
        self.assertEqual(
            parsed["forbidden_dependencies"],
            [{"name": "Helper.hidden", "kind": "task-local axiom"}],
        )

    def test_classifies_elaboration_and_proof_failures(self) -> None:
        self.write_submission(SIGNATURE.replace("rfl", "BAD_SYNTAX"))
        self.assertEqual(validate(self.config())["failure_code"], "SYNTAX_OR_ELAB")
        self.write_submission(SIGNATURE.replace("rfl", "BAD_PROOF"))
        self.assertEqual(validate(self.config())["failure_code"], "PROOF_ERROR")
        self.assertEqual(classify_lean_failure("error: unsolved goals"), "PROOF_ERROR")
        for diagnostic in (
            "error: expected token",
            "unexpected identifier; expected command",
            "error: invalid syntax",
            "application type mismatch: function expected at f",
            "an unfamiliar compiler rejection",
        ):
            with self.subTest(diagnostic=diagnostic):
                self.assertEqual(
                    classify_lean_failure(diagnostic), "SYNTAX_OR_ELAB"
                )

    def test_condition_l_records_transitive_library_use(self) -> None:
        audit = self.root / "fake_audit.py"
        audit.write_text(
            "import sys\n"
            "candidate, expected = sys.argv[1:]\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tSubmission')\n"
            "print('library\\tNumStability.foo\\tNumStability.Basic\\t2')\n"
            "print('visited\\t4')\n"
            "print('summary\\t1\\t0')\n",
            encoding="utf-8",
        )
        self.write_submission()
        result = validate(self.config(condition="L", audit=audit))
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["library_audit_complete"])
        self.assertTrue(result["library_use"])
        self.assertEqual(result["library_declarations"][0]["distance"], 2)

    @unittest.skipUnless(shutil.which("lean"), "Lean executable is unavailable")
    def test_semantic_type_check_rejects_macro_changed_identical_signature(self) -> None:
        self.write_submission(
            'local macro "Nat" : term => `(Bool)\n' + SIGNATURE
        )
        result = validate(self.real_audit_config())
        self.assertTrue(result["statement_check"]["ok"], result)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        self.assertEqual(
            result["note"], "target theorem text elaborated to a different Lean type"
        )
        self.assertFalse(result["semantic_statement_check"]["equal"])

    @unittest.skipUnless(shutil.which("lean"), "Lean executable is unavailable")
    def test_candidate_compile_output_cannot_inject_dependency_audit_rows(self) -> None:
        self.write_submission(
            "import Lean.Elab.Command\n"
            "run_cmd do\n"
            '  IO.println "format\\t2"\n'
            '  IO.println "target\\ttarget\\tSubmission"\n'
            '  IO.println "localmodule\\tForged.Helper"\n'
            '  IO.println "library\\tNumStability.fake\\tNumStability.Fake\\t1"\n'
            + SIGNATURE
        )
        result = validate(self.real_audit_config())
        self.assertTrue(result["pass"], result)
        self.assertFalse(result["library_use"])
        parsed = result["dependency_audit"]["parsed"]
        self.assertNotIn("Forged.Helper", parsed["local_modules"])
        self.assertEqual(parsed["library_declarations"], [])
        self.assertEqual(parsed["malformed_lines"], [])
        self.assertIn("NumStability.fake", result["compile"]["output"])

    def test_controlled_files_are_rechecked_after_candidate_compile(self) -> None:
        mutator = self.root / "mutating_compile.py"
        mutator.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "source, output = map(Path, sys.argv[1:])\n"
            "(source.parent / 'task' / 'Canonical.lean').write_text('changed\\n')\n"
            "output.write_bytes(b'candidate olean')\n",
            encoding="utf-8",
        )
        self.write_submission()
        config = replace(
            self.config(),
            compile_command=[
                sys.executable,
                str(mutator),
                "{checked_submission}",
                "{checked_olean}",
            ],
        )
        result = validate(config)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        self.assertFalse(result["controlled_after_compile"]["ok"])

    def test_controlled_files_are_rechecked_after_dependency_audit(self) -> None:
        mutator = self.root / "mutating_audit.py"
        mutator.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "candidate, expected = sys.argv[1:]\n"
            "(Path.cwd() / 'task' / 'Canonical.lean').write_text('changed\\n')\n"
            "print('format\\t2')\n"
            "print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "print(f'target\\t{candidate}\\tChecked')\n"
            "print('visited\\t1')\n"
            "print('summary\\t0\\t0')\n",
            encoding="utf-8",
        )
        self.write_submission()
        result = validate(self.config(audit=mutator))
        self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)
        self.assertFalse(result["controlled_after_audit"]["ok"])

    def test_source_parser_ignores_comments_and_strings(self) -> None:
        source = self.root / "Parser.lean"
        source.write_text(
            '-- sorry\n/- axiom hidden : False -/\ndef text := "unsafe sorry"\nimport Mathlib\n',
            encoding="utf-8",
        )
        self.assertEqual(forbidden_source_findings(source, ("NumStability",)), [])
        self.assertEqual(extract_imports(source.read_text()), ["Mathlib"])

    def test_dependency_output_must_be_well_formed(self) -> None:
        parsed = parse_dependency_audit("format\t1\ntarget\tx\tM\nnoise\n")
        self.assertFalse(parsed["ok"])
        self.assertEqual(parsed["malformed_lines"], ["noise"])

    def test_signature_comparison_ignores_only_formatting(self) -> None:
        submitted = self.root / "submitted.lean"
        canonical = self.root / "canonical.lean"
        submitted.write_text("theorem target\n (n : Nat) : n = n := by rfl\n")
        canonical.write_text(SIGNATURE)
        self.assertTrue(compare_target_signature(submitted, canonical, "target")["ok"])

    def test_t4_authenticates_qualified_controlled_definition_name(self) -> None:
        shared = (
            "namespace HighamBench\n"
            "def Scope.FeasibleResult (n : Nat) : Prop := n = n\n"
            "end HighamBench\n"
        )
        checks = compare_required_surfaces(
            "import HighamBench.Shared\n",
            "theorem placeholder : True := by sorry\n",
            ("HighamBench.Scope.FeasibleResult",),
            (),
            ("HighamBench/Shared.lean",),
            (2,),
            {"HighamBench/Shared.lean": shared},
            "Canonical.lean",
        )
        self.assertEqual(len(checks), 1)
        self.assertTrue(checks[0]["ok"], checks[0])
        self.assertEqual(checks[0]["kind"], "controlled_imported_declaration")


    def _t4_config_and_sources(self) -> tuple[ValidationConfig, str, str]:
        shared = (
            "namespace HighamBench\n"
            "def fixed : Nat := 1\n"
            "end HighamBench\n"
        )
        shared_path = self.task / "HighamBench" / "Shared.lean"
        shared_path.parent.mkdir(parents=True, exist_ok=True)
        shared_path.write_text(shared, encoding="utf-8")
        canonical = (
            "import HighamBench.Shared\n"
            "\n"
            "namespace HighamBench\n"
            "theorem first : True := by\n"
            "  -- PROOF_START H001\n"
            "  sorry\n"
            "theorem second (n : Nat) : n + fixed = n + 1 := by\n"
            "  -- PROOF_START H002\n"
            "  sorry\n"
            "end HighamBench\n"
        )
        submission = (
            "import HighamBench.Shared\n"
            "\n"
            "namespace HighamBench\n"
            "theorem first : True := by\n"
            "  -- PROOF_START H001\n"
            "  trivial\n"
            "theorem second (n : Nat) : n + fixed = n + 1 := by\n"
            "  -- PROOF_START H002\n"
            "  rfl\n"
            "theorem provedLocalHelper : True := by trivial\n"
            "end HighamBench\n"
        )
        (self.task / "Canonical.lean").write_text(canonical, encoding="utf-8")
        write_json(self.manifest_path, create_manifest(self.task))

        def hole(order: int, placeholder_id: str, lean_name: str) -> dict:
            marker = f"-- PROOF_START {placeholder_id}"
            offset = canonical.index(marker)
            previous_newline = canonical.rfind("\n", 0, offset)
            return {
                "placeholder_order": order,
                "placeholder_id": placeholder_id,
                "declaration_id": f"D{order:03d}",
                "lean_name": lean_name,
                "marker": marker,
                "line": canonical.count("\n", 0, offset) + 1,
                "column": offset - previous_newline,
            }

        holes = [
            hole(1, "H001", "HighamBench.first"),
            hole(2, "H002", "HighamBench.second"),
        ]
        plural_audit = self.root / "fake_plural_audit.py"
        plural_audit.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "for row in Path(sys.argv[1]).read_text().splitlines():\n"
            "    kind, candidate, expected = row.split('\\t')\n"
            "    if kind != 'proof':\n"
            "        continue\n"
            "    print('format\\t2')\n"
            "    print(f'typeeq\\t{candidate}\\t{expected}\\ttrue')\n"
            "    print(f'target\\t{candidate}\\tHighamBenchChecked')\n"
            "    print('visited\\t1')\n"
            "    print('summary\\t0\\t0')\n",
            encoding="utf-8",
        )
        config = replace(
            self.config(),
            target_theorem="HighamBench.first",
            required_declarations=(
                "HighamBench.first",
                "HighamBench.fixed",
                "HighamBench.second",
            ),
            required_declaration_sources=(
                "Canonical.lean",
                "HighamBench/Shared.lean",
                "Canonical.lean",
            ),
            required_declaration_source_lines=(4, 2, 7),
            controlled_sorries=holes,
            audit_command=[sys.executable, str(plural_audit), "{audit_pairs_file}"],
        )
        return config, canonical, submission

    def test_t4_checks_every_declaration_hole_and_audit(self) -> None:
        config, _, submission = self._t4_config_and_sources()
        self.write_submission(submission)
        result = validate(config)
        self.assertTrue(result["pass"], result)
        self.assertEqual(
            [check["lean_name"] for check in result["statement_checks"]],
            list(config.required_declarations),
        )
        self.assertTrue(all(check["ok"] for check in result["statement_checks"]))
        self.assertEqual(len(result["proof_hole_check"]["holes"]), 2)
        self.assertEqual(len(result["dependency_audits"]), 2)
        self.assertEqual(
            [check["candidate"] for check in result["semantic_statement_checks"]],
            ["HighamBench.first", "HighamBench.second"],
        )
        self.assertTrue(result["audit_pairs_side_channel"]["unchanged_after_audit"])
        self.assertEqual(result["audit_pairs_side_channel"]["pair_count"], 2)
        self.assertEqual(result["audit_pairs_side_channel"]["mapping_count"], 2)
        self.assertEqual(
            result["audit_pairs_side_channel"]["controlled_source_binding_count"],
            3,
        )
        shared_check = result["statement_checks"][1]
        self.assertEqual(shared_check["kind"], "controlled_imported_declaration")
        self.assertEqual(
            shared_check["controlled_source_file"], "HighamBench/Shared.lean"
        )
        self.assertIsNone(shared_check["submitted"])

    def test_t4_real_lean_audits_every_proof_declaration(self) -> None:
        elan = shutil.which("elan")
        if elan is not None:
            lean = subprocess.check_output([elan, "which", "lean"], text=True).strip()
        else:
            lean = shutil.which("lean")
        if not lean:
            self.skipTest("Lean is unavailable")
        config, _, submission = self._t4_config_and_sources()
        shared_source = self.task / "HighamBench" / "Shared.lean"
        shared_olean = shared_source.with_suffix(".olean")
        subprocess.run(
            [lean, "-o", str(shared_olean), str(shared_source)],
            check=True,
            cwd=self.workspace,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        write_json(self.manifest_path, create_manifest(self.task))
        self.write_submission(submission)
        driver = self.root / "trusted_plural_audit_driver.py"
        driver.write_text(
            "import os, subprocess, sys\n"
            "lean, audit, workspace, module, pairs, expected_module, local_modules = sys.argv[1:]\n"
            "environment = os.environ.copy()\n"
            "environment['LEAN_PATH'] = workspace + '/task:' + workspace\n"
            "environment['PATH'] = os.path.dirname(lean) + ':/usr/bin:/bin'\n"
            "result = subprocess.run(\n"
            "  [lean, '--run', audit, module, '--pairs-file', pairs, expected_module, local_modules],\n"
            "  cwd=workspace, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=environment)\n"
            "print(result.stdout, end='')\n"
            "raise SystemExit(result.returncode)\n",
            encoding="utf-8",
        )
        config = replace(
            config,
            compile_command=[
                shutil.which("env") or "/usr/bin/env",
                "LEAN_PATH={workspace}/task:{workspace}",
                lean,
                "-o",
                "{checked_olean}",
                "{checked_submission}",
            ],
            audit_command=[
                sys.executable,
                str(driver),
                lean,
                str(TOOLS / "dependency_audit.lean"),
                "{workspace}",
                "{submission_module}",
                "{audit_pairs_file}",
                "{expected_module}",
                "{local_modules_file}",
            ],
        )
        result = validate(config)
        self.assertTrue(result["pass"], result)
        self.assertEqual(len(result["dependency_audits"]), 2)

    def test_t4_rejects_changed_later_surface_and_bad_hole_ledgers(self) -> None:
        config, _, submission = self._t4_config_and_sources()
        cases = {
            "later signature": submission.replace(
                "theorem second (n : Nat) : n + fixed = n + 1 := by",
                "theorem second (n : Nat) : n + fixed + 0 = n + 1 := by",
            ),
            "fixed definition": submission.replace(
                "namespace HighamBench\n",
                "namespace HighamBench\ndef fixed : Nat := 2\n",
                1,
            ),
            "missing marker": submission.replace("  -- PROOF_START H002\n", ""),
            "extra marker": submission.replace(
                "theorem provedLocalHelper",
                "-- PROOF_START EXTRA\ntheorem provedLocalHelper",
            ),
        }
        for label, candidate in cases.items():
            with self.subTest(label=label):
                self.write_submission(candidate)
                result = validate(config)
                self.assertEqual(result["failure_code"], "RULE_VIOLATION", result)

        self.write_submission(submission.replace("  rfl\n", "  sorry\n", 1))
        retained = validate(config)
        self.assertEqual(retained["failure_code"], "RULE_VIOLATION", retained)
        self.assertIn(
            "sorry", {finding["kind"] for finding in retained["static_findings"]}
        )


if __name__ == "__main__":
    unittest.main()
