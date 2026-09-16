from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from prepare_candidate_audit import (  # noqa: E402
    CandidateAuditError,
    build_blind_dossier,
    parse_lean_report,
    prepare_candidate_audit,
)


REPORT = """\
format\t2
target\tHighamBenchCandidate.target
target-readable\t∀ x : LocalThing, round x = x
target-explicit\t(x : @HighamBenchCandidate.LocalThing) → @NumStability.Model.round x = x
environment-module\tCandidate
environment-module\tNumStability.Model
dependency\tlocal\tHighamBenchCandidate.LocalThing\tCandidate\t1\tinductive\tType\tType\t\t
dependency\tlocal\tNumStability.Model.round\tNumStability.Model\t1\tdef\tLocalThing → LocalThing\t@HighamBenchCandidate.LocalThing → @HighamBenchCandidate.LocalThing\tfun x => x\tfun (x : @HighamBenchCandidate.LocalThing) => x
dependency\texternal-frontier\tEq\tInit.Prelude\t1\tinductive\tα → α → Prop\t{α : Sort u} → α → α → Prop\t\t
edge\tHighamBenchCandidate.target\tHighamBenchCandidate.LocalThing\ttype
edge\tHighamBenchCandidate.target\tNumStability.Model.round\ttype
edge\tNumStability.Model.round\tHighamBenchCandidate.LocalThing\ttype
summary\t3\t3
"""


GOOD_SOURCE = """\
namespace HighamBenchCandidate
def LocalThing := Nat
theorem target : ∀ x : LocalThing, x = x := by sorry
end HighamBenchCandidate
"""


class CandidateDossierTests(unittest.TestCase):
    def test_parser_is_strict_and_assigns_stable_ids(self) -> None:
        parsed = parse_lean_report(REPORT)
        self.assertEqual(
            [item["id"] for item in parsed["dependencies"]],
            ["D001", "D002", "D003"],
        )
        broken = REPORT.replace("summary\t3\t3", "summary\t2\t3")
        with self.assertRaises(CandidateAuditError):
            parse_lean_report(broken)

    def test_blind_dossier_removes_names_and_module_provenance(self) -> None:
        parsed = parse_lean_report(REPORT)
        blind, private_map = build_blind_dossier(parsed)
        rendered = json.dumps(blind, sort_keys=True)
        for forbidden in (
            "HighamBenchCandidate",
            "NumStability",
            "Candidate",
            "LocalThing",
        ):
            self.assertNotIn(forbidden, rendered)
        self.assertRegex(blind["semantic_sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(blind["target"]["name"], "TARGET")
        self.assertEqual(blind["dependencies"][0]["name"], "LocalDef001")
        self.assertEqual(
            {item["owner_module"] for item in blind["dependencies"] if item["role"] == "local"},
            {"LOCAL"},
        )
        self.assertIn("HighamBenchCandidate.LocalThing", private_map["declarations"])

    def test_semantic_hash_is_stable_and_changes_with_target(self) -> None:
        parsed = parse_lean_report(REPORT)
        first, _ = build_blind_dossier(parsed)
        second, _ = build_blind_dossier(parse_lean_report(REPORT))
        self.assertEqual(first["semantic_sha256"], second["semantic_sha256"])
        changed = copy.deepcopy(parsed)
        changed["target_type_explicit"] += " → False"
        third, _ = build_blind_dossier(changed)
        self.assertNotEqual(first["semantic_sha256"], third["semantic_sha256"])

    def test_fake_compiler_and_extractor_prepare_separate_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candidate = root / "Candidate.lean"
            candidate.write_text(GOOD_SOURCE, encoding="utf-8")
            compiler = root / "fake_compiler.py"
            compiler.write_text(
                "from pathlib import Path\n"
                "import sys\n"
                "candidate, olean = map(Path, sys.argv[1:3])\n"
                "assert '#check _root_.HighamBenchCandidate.target' in candidate.read_text()\n"
                "olean.write_bytes(b'fake olean')\n",
                encoding="utf-8",
            )
            extractor = root / "fake_extractor.py"
            extractor.write_text(f"print({REPORT!r}, end='')\n", encoding="utf-8")
            blind, private = prepare_candidate_audit(
                candidate,
                compiler_command=(
                    sys.executable,
                    str(compiler),
                    "{candidate}",
                    "{olean}",
                ),
                extractor_command=(sys.executable, str(extractor)),
            )
            self.assertEqual(
                private["blind_semantic_sha256"], blind["semantic_sha256"]
            )
            self.assertEqual(
                private["candidate"]["sha256"],
                hashlib.sha256(GOOD_SOURCE.encode("utf-8")).hexdigest(),
            )
            self.assertIn("raw_semantic_report", private)
            self.assertNotIn("NumStability", json.dumps(blind, sort_keys=True))

    @unittest.skipUnless(shutil.which("lean"), "Lean executable is unavailable")
    def test_real_lean_extractor_follows_candidate_definition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            candidate = Path(temporary) / "Candidate.lean"
            candidate.write_text(
                "namespace HighamBenchCandidate\n"
                "def reflected (n : Nat) : Nat := n\n"
                "theorem target : ∀ n : Nat, reflected n = n := by sorry\n"
                "end HighamBenchCandidate\n",
                encoding="utf-8",
            )
            blind, private = prepare_candidate_audit(candidate)
            raw_local = [
                item
                for item in private["raw_semantic_report"]["dependencies"]
                if item["role"] == "local"
            ]
            self.assertIn(
                "HighamBenchCandidate.reflected",
                {item["name"] for item in raw_local},
            )
            self.assertNotIn("HighamBenchCandidate", json.dumps(blind))

    @unittest.skipUnless(shutil.which("lean"), "Lean executable is unavailable")
    def test_real_lean_extractor_blinds_private_helpers(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            candidate = Path(temporary) / "Candidate.lean"
            candidate.write_text(
                "namespace HighamBenchCandidate\n"
                "private def firstIndex (n : Nat) : Nat := n\n"
                "private def tailIndex (n : Nat) : Nat := firstIndex n + 1\n"
                "def pairwiseSum (n : Nat) : Nat := firstIndex n\n"
                "def recursiveSum (n : Nat) : Nat := tailIndex n\n"
                "theorem target : ∀ n : Nat, pairwiseSum n = recursiveSum n := by sorry\n"
                "end HighamBenchCandidate\n",
                encoding="utf-8",
            )
            blind, private = prepare_candidate_audit(candidate)
            raw = private["raw_semantic_report"]
            self.assertTrue(
                any(
                    item["role"] == "local" and "firstIndex" in item["name"]
                    for item in raw["dependencies"]
                )
            )
            self.assertTrue(
                any(
                    item["role"] == "local" and "tailIndex" in item["name"]
                    for item in raw["dependencies"]
                )
            )
            for forbidden in ("HighamBenchCandidate", "_private", "firstIndex", "tailIndex", "✝"):
                self.assertNotIn(forbidden, json.dumps(blind, sort_keys=True))


if __name__ == "__main__":
    unittest.main()
