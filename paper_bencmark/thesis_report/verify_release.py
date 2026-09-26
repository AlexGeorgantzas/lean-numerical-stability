#!/usr/bin/env python3
"""Verify the published analysis inputs and compact evidence bundles.

This does not replace the original controller's complete hash-chain audit on
Titan: the compact publication bundles intentionally omit binary caches and
private state. It verifies every primary published source and the 4+11 sealed
pair identities used by the fifteen-task composite.
"""

from __future__ import annotations

import hashlib
import json
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EXPECTED = {
    ROOT / "paper_bencmark/pilot35/RESULTS_15.json": "3faeb35af66f5c3c9d16e0800a4c88bd5cef09e1a35f0bc10e6c387f40d9c050",
    HERE / "evidence/warm-root.json": "3401426d25ee278cbf33e48da80f665d5bcc4ad8bcab721a4fa69cae0095ee39",
    HERE / "evidence/library-snapshot.json": "c82dc7ec24af3a49569b94e28bb6e4942f45e2f910cbec59628836d76345b84a",
    HERE / "evidence/library-build-record.json": "6f4581380982e51fd52a342cc380db5c8bae5d427d32be9c8f2aa9d136de8058",
    HERE / "evidence/runtime-snapshot.json": "9fac78511309a5919d31424eb0adc5964a26f0e334542639fdd9f81fd3979fc6",
    HERE / "evidence/warm-scout/turn.json": "520f7efaa34ba72ad89b2d7e7826721244ac58c94b4b158cd190b4480b20fbc2",
    HERE / "evidence/pilot34-high-overlap-20260924-a-thesis-evidence.tar.gz": "7f9b3774458a8e9ca1cc871ec6e1718933911cb2c2843b604a55bffe2a5cc3fc",
    HERE / "evidence/pilot35-audit-recovery-20260925-a-thesis-evidence.tar.gz": "c4c5b8fac97cc2172d811e13a3e81acbf5eb10d76482867d5681e62283b7f438",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FAIL: " + message)


def main() -> None:
    for path, wanted in EXPECTED.items():
        check(path.exists(), f"missing {path}")
        check(sha(path.read_bytes()) == wanted, f"SHA-256 mismatch: {path}")
    result = json.loads((ROOT / "paper_bencmark/pilot35/RESULTS_15.json").read_text())
    corpus = json.loads((ROOT / "paper_bencmark/formalization_benchmark/design33/CORPUS_15.json").read_text())
    recovery = json.loads((ROOT / "paper_bencmark/pilot35/RECOVERY_11.json").read_text())
    tasks = result["tasks"]
    check([t["task_id"] for t in tasks] == corpus["scheduled_order"], "task order")
    check(len(tasks) == 15, "task count")
    check(sum(t["source_pilot"] == "Pilot 34" for t in tasks) == 4, "Pilot 34 count")
    check(sum(t["source_pilot"] == "Pilot 35" for t in tasks) == 11, "Pilot 35 count")
    check(all(t["paired_proof_eligible"] for t in tasks), "proof eligibility")
    for pilot, count in ((34, 312), (35, 712)):
        archive = next(HERE.glob(f"evidence/pilot{pilot}-*thesis-evidence.tar.gz"))
        with tarfile.open(archive, "r:gz") as tar:
            members = tar.getmembers()
            check(len(members) == count, f"Pilot {pilot} archive count")
            for m in members:
                p = Path(m.name)
                check(not p.is_absolute() and ".." not in p.parts,
                      f"unsafe archive path: {m.name}")
            if pilot == 34:
                for task, wanted in recovery["preserved_pair_report_sha256"].items():
                    m = tar.getmember(f"./{task}/pair-report.json")
                    stream = tar.extractfile(m)
                    check(stream is not None and sha(stream.read()) == wanted,
                          f"preserved pair SHA-256: {task}")
    sums = result["summary"]["phase_comparisons"]
    for key, field in (("formalization_seconds_inclusive", "formalization_seconds_inclusive"),
                       ("proof_seconds_inclusive", "proof_seconds_inclusive"),
                       ("total_seconds_inclusive", "total_seconds_inclusive"),
                       ("proof_code_lines", "proof_code_lines")):
        for condition in ("N", "L"):
            actual = sum(t[condition][field] for t in tasks)
            claimed = sums[key][f"{condition}_sum"]
            check(abs(actual - claimed) < 1e-5, f"aggregate {key} {condition}")
    print("PASS: primary sources, 4+11 pair identities, archive safety, and key sums")


if __name__ == "__main__":
    main()
