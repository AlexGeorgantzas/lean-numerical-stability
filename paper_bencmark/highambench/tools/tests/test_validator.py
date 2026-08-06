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
            "environment['LEAN_PATH'] = workspace\n"
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

    def test_candidate_olean_without_scanned_source_is_rejected(self) -> None:
        (self.workspace / "HiddenHelper.olean").write_bytes(b"not a trusted module")
        self.write_submission()
        result = validate(self.config())
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
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


if __name__ == "__main__":
    unittest.main()
