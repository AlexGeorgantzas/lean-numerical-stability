"""R02 gate battery. Exit codes come from subprocess.run, never from PowerShell.

The predecessor wave's PowerShell harness reported `exit=0` with an empty log for a
checker that was failing with five errors, because `& $block *> file` did not carry the
native exit code back. Every gate here records `returncode` directly with its output
captured beside it, so a pass can never be inferred from silence.

The caller holds Local\\lean-reorganization-2026-08 for the whole run; this script does not
acquire it, so the entire battery is one acquisition.
"""
from __future__ import annotations

import json, os, subprocess, sys, time

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
LOGS = os.path.join(OUT, "logs")
os.makedirs(LOGS, exist_ok=True)
STATUS = os.path.join(LOGS, "gates.status")


def note(m):
    with open(STATUS, "a", encoding="utf-8") as fh:
        fh.write(f"{time.strftime('%H:%M:%S')} {m}\n")


def mods(fn):
    p = os.path.join(OUT, fn)
    return [l.strip() for l in open(p, encoding="utf-8") if l.strip()] if os.path.exists(p) else []


PY = sys.executable
STEPS = [
    ("lake_lib",        ["lake", "build", "NumStability"]),
    ("lake_libtest",    ["lake", "build", "NumStability", "NumStabilityTest"]),
    ("tests_canonical", ["lake", "build"] + mods("tests-canonical_only.txt")),
    ("tests_old",       ["lake", "build"] + mods("tests-old_only.txt")),
    ("tests_focused",   ["lake", "build"] + mods("tests-focused.txt")),
    ("tests_consumer",  ["lake", "build"] + mods("tests-protected_consumer.txt")),
    ("lake_test",       ["lake", "test"]),
    ("check_layout",       [PY, "-B", "tools/architecture/check_layout.py"]),
    ("check_compatibility", [PY, "-B", "tools/architecture/check_compatibility.py"]),
    ("check_provenance",   [PY, "-B", "tools/architecture/check_provenance.py"]),
    ("strict_source",   [PY, "-B", "tools/architecture/generate_baseline.py",
                         "--output-dir", "benchmark-results/R02-strict-source",
                         "--name", "source", "--strict-source", "--no-build"]),
    ("candidate",       [PY, "-B", "tools/architecture/generate_baseline.py",
                         "--output-dir", "benchmark-results", "--name", "R02-candidate",
                         "--no-build", "--keep-dependency-tsv",
                         "benchmark-results/R02-candidate.tsv"]),
]

results = {}
open(STATUS, "w", encoding="utf-8").close()
note(f"battery start; {len(STEPS)} steps")
for name, cmd in STEPS:
    if cmd[0] == "lake" and cmd[1] == "build" and len(cmd) == 2:   # empty module list
        note(f"{name} SKIPPED (no modules listed)")
        continue
    t0 = time.time()
    p = subprocess.run(cmd, cwd=WT, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    txt = (p.stdout or "") + (p.stderr or "")
    open(os.path.join(LOGS, f"gate-{name}.log"), "w", encoding="utf-8").write(txt)
    errs = [l for l in txt.splitlines() if l.startswith("error:")]
    mins = int((time.time() - t0) / 60)
    jobs = txt.count("Built ") + txt.count("Replayed ")
    results[name] = {"exit": p.returncode, "errors": len(errs), "minutes": mins,
                     "jobs": jobs, "argv": len(cmd)}
    note(f"{name} exit={p.returncode} errors={len(errs)} {mins}m jobs={jobs}")
    for e in errs[:6]:
        note("   " + e[:160])
    json.dump(results, open(os.path.join(LOGS, "gates.json"), "w", encoding="utf-8"), indent=1)

# projection replay last, only if the candidate exists
cand = os.path.join(WT, "benchmark-results", "R02-candidate.tsv")
if results.get("candidate", {}).get("exit") == 0 and os.path.exists(cand):
    t0 = time.time()
    p = subprocess.run([PY, "-B", os.path.join(OUT, "projection.py")],
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    txt = (p.stdout or "") + (p.stderr or "")
    open(os.path.join(LOGS, "gate-replay.log"), "w", encoding="utf-8").write(txt)
    results["replay"] = {"exit": p.returncode, "errors": 0,
                         "minutes": int((time.time() - t0) / 60), "jobs": 0, "argv": 2}
    note(f"replay exit={p.returncode}")
    for l in txt.splitlines():
        if any(k in l for k in ("passed", "declarations:", "edges:", "sha256")):
            note("   " + l.strip()[:150])
else:
    note("replay SKIPPED (no candidate)")

json.dump(results, open(os.path.join(LOGS, "gates.json"), "w", encoding="utf-8"), indent=1)
bad = {k: v["exit"] for k, v in results.items() if v["exit"] != 0}
note(f"ALL DONE failures={len(bad)} {bad}")
note("DONE exit=" + str(0 if not bad else 1))
