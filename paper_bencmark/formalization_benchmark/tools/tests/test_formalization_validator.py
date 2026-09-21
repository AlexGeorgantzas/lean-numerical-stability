from __future__ import annotations

import os
from pathlib import Path
import sys
import tempfile
import time
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from formalization_validator import (  # noqa: E402
    COMMAND_CGROUP_VARIABLE,
    inspect_candidate_source,
    run_bounded_command,
    validate_candidate,
)


GOOD_SOURCE = """\
namespace HighamBenchCandidate

def reflected (n : Nat) : Nat := n

theorem target : ∀ n : Nat, reflected n = n := by
  intro n
  rfl

end HighamBenchCandidate
"""


class FormalizationValidatorTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.candidate = self.root / "Candidate.lean"
        self.compiler = self.root / "fake_compiler.py"
        self.compiler.write_text(
            "from pathlib import Path\n"
            "import sys\n"
            "candidate, olean = map(Path, sys.argv[1:3])\n"
            "source = candidate.read_text(encoding='utf-8')\n"
            "print(candidate.parent)\n"
            "if '#check _root_.HighamBenchCandidate.target' not in source:\n"
            "    print('missing trusted target probe')\n"
            "    raise SystemExit(3)\n"
            "if 'COMPILE_ERROR' in source:\n"
            "    print('error: unknown identifier COMPILE_ERROR')\n"
            "    raise SystemExit(1)\n"
            "olean.write_bytes(b'fake Candidate olean')\n",
            encoding="utf-8",
        )
        self.command = (
            sys.executable,
            str(self.compiler),
            "{candidate}",
            "{olean}",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_candidate(self, source: str = GOOD_SOURCE) -> None:
        self.candidate.write_text(source, encoding="utf-8")

    def test_accepts_contract_and_compiles_only_a_fresh_copy(self) -> None:
        self.write_candidate()
        result = validate_candidate(self.candidate, compiler_command=self.command)
        self.assertTrue(result["pass"], result)
        self.assertTrue(result["source_check"]["pass"])
        self.assertTrue(result["compile"]["fresh_workspace"])
        compiled_parent = Path(result["compile"]["output"].strip())
        self.assertNotEqual(compiled_parent, self.candidate.parent)
        self.assertFalse(compiled_parent.exists())
        self.assertEqual(self.candidate.read_text(encoding="utf-8"), GOOD_SOURCE)

    def test_comments_and_strings_do_not_trigger_keyword_checks(self) -> None:
        source = """\
namespace HighamBenchCandidate
-- axiom hidden : False := sorry
/- unsafe opaque constant admit -/
def words : String := "axiom unsafe opaque constant admit sorry"
theorem target : words.length > 0 := by decide
end HighamBenchCandidate
"""
        inspection = inspect_candidate_source(source)
        self.assertTrue(inspection["pass"], inspection)

    def test_rejects_every_integrity_escape(self) -> None:
        declarations = {
            "sorry": "def helper : True := by sorry",
            "admit": "def helper : True := by admit",
            "axiom": "axiom helper : True",
            "constant": "constant helper : Nat",
            "opaque": "opaque helper : Nat := 0",
            "unsafe": "unsafe def helper : Nat := 0",
            "sorryAx": "def helper : True := sorryAx True true",
            "partial": "partial def helper : Nat → Nat := fun n => helper n",
            "extern": "@[extern \"helper\"] def helper : Nat := 0",
            "implemented_by": "@[implemented_by helper] def helper2 : Nat := 0",
            "elab": "elab \"makeHelper\" : command => pure ()",
            "run_cmd": "run_cmd pure ()",
            "syntax": "syntax \"helperSyntax\" : term",
            "command_directive": "#eval (1 + 1 : Nat)",
        }
        for keyword, declaration in declarations.items():
            with self.subTest(keyword=keyword):
                source = (
                    "namespace HighamBenchCandidate\n"
                    + declaration
                    + "\ntheorem target : True := by trivial\n"
                    "end HighamBenchCandidate\n"
                )
                result = inspect_candidate_source(source)
                self.assertFalse(result["pass"])
                self.assertIn(
                    "forbidden-construct", {item["code"] for item in result["issues"]}
                )

    def test_rejects_any_hole_without_running_compiler(self) -> None:
        self.write_candidate(GOOD_SOURCE.replace("def reflected (n : Nat) : Nat := n", "def reflected (n : Nat) : Nat := by sorry"))
        result = validate_candidate(self.candidate, compiler_command=self.command)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertIsNone(result["compile"])
        self.assertEqual(result["source_check"]["sorry_count"], 1)

    def test_requires_final_root_and_complete_proof(self) -> None:
        variants = [
            GOOD_SOURCE.replace("intro n\n  rfl", "intro n\n  sorry"),
            GOOD_SOURCE.replace(
                "\nend HighamBenchCandidate",
                "\ndef afterTarget : Nat := 0\nend HighamBenchCandidate",
            ),
            GOOD_SOURCE.replace("namespace HighamBenchCandidate\n", ""),
        ]
        for source in variants:
            with self.subTest(source=source):
                self.assertFalse(inspect_candidate_source(source)["pass"])

    def test_statement_only_mode_requires_one_hole_exactly_at_final_target(self) -> None:
        source = GOOD_SOURCE.replace("intro n\n  rfl", "sorry")
        self.write_candidate(source)
        result = validate_candidate(
            self.candidate,
            compiler_command=self.command,
            allow_single_target_sorry=True,
        )
        self.assertTrue(result["pass"], result)
        self.assertEqual(result["source_check"]["sorry_count"], 1)
        self.assertEqual(
            result["source_check"]["source_contract"],
            "statement-only-single-target-sorry",
        )

        bad_variants = [
            source.replace("def reflected (n : Nat) : Nat := n", "def reflected (n : Nat) : Nat := by sorry"),
            source.replace("theorem target : ∀ n : Nat, reflected n = n := by\n  sorry", "theorem target : ∀ n : Nat, reflected n = n := by\n  trivial\n  sorry"),
            GOOD_SOURCE,
        ]
        for bad in bad_variants:
            with self.subTest(source=bad):
                self.assertFalse(
                    inspect_candidate_source(
                        bad, allow_single_target_sorry=True
                    )["pass"]
                )

    def test_rejects_lemma_as_the_audited_root(self) -> None:
        source = GOOD_SOURCE.replace("theorem target", "lemma target")
        inspection = inspect_candidate_source(source)
        self.assertFalse(inspection["pass"])
        self.assertIn(
            "root-declaration-kind",
            {item["code"] for item in inspection["issues"]},
        )

    def test_reports_candidate_compilation_failure(self) -> None:
        self.write_candidate(GOOD_SOURCE.replace("∀ n : Nat", "COMPILE_ERROR → ∀ n : Nat"))
        result = validate_candidate(self.candidate, compiler_command=self.command)
        self.assertFalse(result["pass"])
        self.assertEqual(result["failure_code"], "COMPILATION_FAILURE")
        self.assertIn("unknown identifier", result["compile"]["output"])

    def test_requires_exact_candidate_basename(self) -> None:
        wrong = self.root / "Other.lean"
        wrong.write_text(GOOD_SOURCE, encoding="utf-8")
        result = validate_candidate(wrong, compiler_command=self.command)
        self.assertEqual(result["failure_code"], "RULE_VIOLATION")
        self.assertEqual(result["source_check"]["issues"][0]["code"], "candidate-file")


class BoundedCommandTests(unittest.TestCase):
    def test_output_is_capped_and_process_is_stopped(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            environment = os.environ.copy()
            environment.pop(COMMAND_CGROUP_VARIABLE, None)
            result = run_bounded_command(
                [sys.executable, "-c", "import sys; sys.stdout.write('x' * 4096)"],
                cwd=Path(temporary),
                environment=environment,
                timeout_seconds=5,
                maximum_output_bytes=128,
            )
        self.assertTrue(result["output_limit_exceeded"])
        self.assertGreater(result["output_bytes_observed"], 128)
        self.assertEqual(len(result["output"].encode("utf-8")), 128)

    def test_command_joins_configured_cgroup_and_reads_stable_counters(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cgroup = root / "commands"
            cgroup.mkdir()
            endpoint = cgroup / "cgroup.procs"
            endpoint.write_text("", encoding="ascii")
            (cgroup / "memory.events").write_text(
                "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n", encoding="ascii"
            )
            (cgroup / "pids.events").write_text("max 0\n", encoding="ascii")
            environment = os.environ.copy()
            environment[COMMAND_CGROUP_VARIABLE] = str(endpoint)
            result = run_bounded_command(
                [sys.executable, "-c", "print('joined')"],
                cwd=root,
                environment=environment,
                timeout_seconds=5,
                maximum_output_bytes=1024,
            )
            self.assertEqual(endpoint.read_text(encoding="ascii"), "0")
        self.assertEqual(result["returncode"], 0, result)
        self.assertEqual(result["output"].strip(), "joined")
        self.assertFalse(result["resource_cgroup_join_failed"])
        self.assertFalse(result["resource_limit_exceeded"])

    def test_timeout_kills_descendant_after_process_group_leader_exits(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "descendant-survived"
            child = (
                "import pathlib,time; time.sleep(0.4); "
                f"pathlib.Path({str(marker)!r}).write_text('alive')"
            )
            parent = (
                "import subprocess,sys; "
                f"subprocess.Popen([sys.executable, '-c', {child!r}]); "
                "print('leader-exiting', flush=True)"
            )
            environment = os.environ.copy()
            environment.pop(COMMAND_CGROUP_VARIABLE, None)
            result = run_bounded_command(
                [sys.executable, "-c", parent],
                cwd=root,
                environment=environment,
                timeout_seconds=0.1,
                maximum_output_bytes=1024,
            )
            time.sleep(0.5)
            self.assertFalse(marker.exists())
        self.assertTrue(result["timed_out"])


if __name__ == "__main__":
    unittest.main()
