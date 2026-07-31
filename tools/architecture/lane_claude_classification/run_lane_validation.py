#!/usr/bin/env python3
"""Run this lane's gates and record machine-readable validation evidence.

Every command is recorded with its exact argument vector, exit code, duration,
and captured tail, together with the repository identity, the tracked input and
output hashes, and row counts.  Nothing is inferred: a gate that did not run
appears with ``"status": "not-run"`` and a stated reason, and a gate that failed
keeps its real exit code.

Large Lean gates are wrapped in the packet's shared build lock, because other
subscriptions share this physical computer.  Pass ``--stage python`` to run only
the static gates, ``--stage lean`` for the Lean gates, or ``--stage all``.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PROPOSAL = ROOT / "docs/architecture/lane-proposals/claude-classification"
LANE_TOOLS = "tools/architecture/lane_claude_classification"
BASE_SHA = "6487fc33088523b8f27ecde9ad613515b78f9977"
BRANCH = "codex/org-classification-prep"

TRACKED_ARTIFACTS = (
    "classification/input-modules.tsv",
    "classification/modules.tsv",
    "classification/summary.json",
    "classification/README.md",
    "ch09/routes.tsv",
    "ch09/ownership.tsv",
    "ch09/owner-dag.tsv",
    "ch09/direct-imports.tsv",
    "ch09/private-rewrites.tsv",
    "ch09/downstream-consumers.tsv",
    "ch09/acceptance.json",
    "ch09/README.md",
    "ch11/routes.tsv",
    "ch11/ownership.tsv",
    "ch11/owner-dag.tsv",
    "ch11/direct-imports.tsv",
    "ch11/private-rewrites.tsv",
    "ch11/downstream-consumers.tsv",
    "ch11/acceptance.json",
    "ch11/README.md",
    "REFRESH-APPENDIX.md",
)

CH09_FOCUSED = [
    "NumStability.Algorithms.HighamChapter9",
    "NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure",
    "NumStability.Algorithms.HighamChapter9ComplexClosure",
    "NumStability.Algorithms.HighamChapter9ComputedCorrection",
    "NumStability.Algorithms.HighamChapter9DoolittleClosure",
    "NumStability.Algorithms.HighamChapter9Theorem914Actual",
    "NumStability.Algorithms.HighamChapter9Theorem914DiagDominant",
    "NumStability.Algorithms.HighamChapter9Theorem914Primitive",
    "NumStability.Algorithms.HighamChapter9Theorem97Classification",
    "NumStability.Algorithms.HighamChapter9Theorem99Closure",
    "NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure",
]

WORKER_TESTS = ROOT / "NumStabilityTest/Worker/ClassificationAudit"


def smoke_modules() -> list[str]:
    """Every isolated worker module, chapter smoke tests first."""

    ordered = [
        "Chapter09Historical.lean",
        "Chapter11Historical.lean",
        "Chapter11CanonicalExisting.lean",
        "AxiomProbe.lean",
    ]
    paths = [WORKER_TESTS / name for name in ordered if (WORKER_TESTS / name).is_file()]
    paths.extend(sorted((WORKER_TESTS / "ProposedFamilies").glob("*.lean")))
    return [path.relative_to(ROOT).as_posix() for path in paths]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def tsv_rows(path: Path) -> int | None:
    if path.suffix != ".tsv":
        return None
    return max(0, len(path.read_text(encoding="utf-8").splitlines()) - 1)


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(argv: list[str], *, lock: Path | None = None, label: str = "") -> dict:
    # The packet ships the shared build lock without the executable bit, so it
    # must be invoked through bash rather than executed directly.
    command = (["bash", str(lock)] if lock else []) + argv
    started = now()
    clock = dt.datetime.now(dt.timezone.utc)
    completed = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, errors="replace"
    )
    duration = (dt.datetime.now(dt.timezone.utc) - clock).total_seconds()
    output = (completed.stdout or "") + (completed.stderr or "")
    tail = [line for line in output.strip().splitlines() if line][-6:]
    record = {
        "label": label or " ".join(argv[:3]),
        "command": command,
        "exit_code": completed.returncode,
        "status": "pass" if completed.returncode == 0 else "fail",
        "started_utc": started,
        "duration_seconds": round(duration, 1),
        "output_tail": tail,
    }
    print(f"[{record['status']}] ({completed.returncode}) {' '.join(argv)}")
    return record


def pristine_baseline(directory: Path) -> dict:
    """Record the external frozen source/.ilean/.olean hash manifest.

    This lane moves no declaration, so the manifest is a baseline record for the
    integrator's post-migration comparison rather than a before/after pair.
    """

    manifest = directory / "SOURCE-HASHES.json"
    if not manifest.is_file():
        return {"present": False, "directory": str(directory)}
    data = json.loads(manifest.read_text(encoding="utf-8"))
    return {
        "present": True,
        "directory": str(directory),
        "external_to_repository": not str(directory.resolve()).startswith(str(ROOT.resolve())),
        "candidate_modules": data.get("files"),
        "modules_with_ilean": data.get("with_ilean"),
        "manifest": manifest.name,
        "manifest_sha256": sha256(manifest),
    }


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args], capture_output=True, text=True, check=True
    ).stdout.strip()


def python_gates(baseline: Path) -> list[dict]:
    tool = lambda name: [sys.executable, f"{LANE_TOOLS}/{name}"]
    records = [
        run(tool("check_read_only_inventory.py"), label="lane inventory checker"),
        run(tool("check_classification_proposal.py") + ["--self-test"],
            label="proposal checker self-test"),
        run(tool("check_classification_proposal.py") + ["--check"],
            label="proposal checker"),
        run(tool("apply_tier_proposal.py") + ["--self-test"],
            label="apply-tool self-test"),
        run(tool("check_ch09_contract.py") + ["--self-test"],
            label="Chapter 9 checker self-test"),
        run(tool("check_ch09_contract.py") + ["--mode", "pre", "--baseline-zip", str(baseline)],
            label="Chapter 9 pre gate"),
        run(tool("check_ch11_contract.py") + ["--self-test"],
            label="Chapter 11 checker self-test"),
        run(tool("check_ch11_contract.py") + ["--mode", "pre", "--baseline-zip", str(baseline)],
            label="Chapter 11 pre gate"),
        run([sys.executable, "tools/architecture/check_compatibility.py"],
            label="repository compatibility gate"),
        run([sys.executable, "tools/architecture/check_layout.py"],
            label="repository layout gate"),
        run([sys.executable, "tools/architecture/check_provenance.py"],
            label="repository provenance gate"),
        run(["git", "diff", "--check"], label="git diff --check"),
    ]
    return records


def lean_gates(lock: Path) -> list[dict]:
    records = [
        run(["lake", "build", "NumStability", "NumStabilityTest"], lock=lock,
            label="lake build NumStability NumStabilityTest"),
        run(["lake", "build", *CH09_FOCUSED], lock=lock,
            label="focused Chapter 9 historical builds"),
        run(["lake", "build", "NumStability.Algorithms.HighamChapter11",
             "NumStability.Source.Higham.Chapter11",
             "NumStability.Source.Higham.Chapter11.Theorem07"], lock=lock,
            label="focused Chapter 11 historical and canonical builds"),
    ]
    for module in smoke_modules():
        records.append(run(["lake", "env", "lean", module], lock=lock,
                           label=f"isolated smoke module {Path(module).stem}"))
    records.append(run(["lake", "test"], lock=lock, label="lake test"))
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("python", "lean", "all"), default="all")
    parser.add_argument("--baseline-zip", type=Path,
                        default=ROOT.parent.parent / "baseline/parallel-base-declarations-v2.zip")
    parser.add_argument("--lock", type=Path,
                        default=ROOT.parent.parent / "scripts/with_lean_lock.sh")
    parser.add_argument("--pristine", type=Path,
                        default=ROOT.parent.parent / "runtime/pristine-baseline",
                        help="external directory holding the frozen source/.ilean manifest")
    parser.add_argument("--merge", type=Path,
                        help="merge previously recorded gate records from this VALIDATION.json")
    args = parser.parse_args()

    records: list[dict] = []
    if args.merge and args.merge.is_file():
        records.extend(json.loads(args.merge.read_text(encoding="utf-8")).get("gates", []))
    if args.stage in {"python", "all"}:
        records = [r for r in records if not r["command"][0].endswith("python3")] + \
            python_gates(args.baseline_zip)
    if args.stage in {"lean", "all"}:
        if shutil.which("lake") is None:
            records.append({
                "label": "lean gates", "command": ["lake"], "exit_code": None,
                "status": "not-run", "started_utc": now(), "duration_seconds": 0.0,
                "output_tail": ["lake is not on PATH in this environment"],
            })
        else:
            records = [r for r in records if "lake" not in r["command"][0]
                       and not any("lake" == part for part in r["command"])] + \
                lean_gates(args.lock)

    artifacts = {}
    for relative in TRACKED_ARTIFACTS:
        path = PROPOSAL / relative
        if not path.is_file():
            artifacts[relative] = {"present": False}
            continue
        entry = {"present": True, "bytes": path.stat().st_size, "sha256": sha256(path)}
        rows = tsv_rows(path)
        if rows is not None:
            entry["rows"] = rows
        artifacts[relative] = entry

    summary = json.loads((PROPOSAL / "classification/summary.json").read_text(encoding="utf-8"))
    ch09 = json.loads((PROPOSAL / "ch09/acceptance.json").read_text(encoding="utf-8"))
    ch11 = json.loads((PROPOSAL / "ch11/acceptance.json").read_text(encoding="utf-8"))

    evidence = {
        "schema_version": 1,
        "generated_utc": now(),
        "lane": "classification-ch09-ch11",
        "engine": "Claude",
        "subscription": "4",
        "identity": {
            "frozen_base_sha": BASE_SHA,
            "branch": git("branch", "--show-current"),
            "head": git("rev-parse", "HEAD"),
            "base_is_ancestor_of_head": subprocess.run(
                ["git", "-C", str(ROOT), "merge-base", "--is-ancestor", BASE_SHA, "HEAD"]
            ).returncode == 0,
            "status_porcelain_lines": len(git("status", "--porcelain=v1").splitlines()),
            "commits_since_base": len(git("rev-list", f"{BASE_SHA}..HEAD").splitlines()),
            "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        },
        "inputs": {
            "packet_read_only_modules_sha256":
                "C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54",
            "baseline_stream_zip": str(args.baseline_zip),
            "baseline_stream_zip_sha256":
                sha256(args.baseline_zip) if args.baseline_zip.is_file() else None,
        },
        "counts": {
            "classification_rows": summary["rows"],
            "classification_tiers": summary["tier_counts"],
            "classification_deferred_rows": len(summary["deferred_reusable_rows"]),
            "classification_split_queue": summary["split_queue_size"],
            "ch09_destinations": ch09["destination_count"],
            "ch09_ownership_rows": ch09["counts"]["ownership_rows"],
            "ch09_private_rewrites": ch09["counts"]["private_declarations"],
            "ch11_destinations": ch11["destination_count"],
            "ch11_ownership_rows": ch11["counts"]["ownership_rows"],
            "ch11_private_rewrites": ch11["counts"]["private_declarations"],
        },
        "normalized_hashes": {"ch09": ch09["normalized_hashes"], "ch11": ch11["normalized_hashes"]},
        "artifacts": artifacts,
        "pristine_baseline": pristine_baseline(args.pristine),
        "gates": records,
        "gate_totals": {
            "pass": sum(1 for r in records if r["status"] == "pass"),
            "fail": sum(1 for r in records if r["status"] == "fail"),
            "not_run": sum(1 for r in records if r["status"] == "not-run"),
        },
    }
    (PROPOSAL / "VALIDATION.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (PROPOSAL / "VALIDATION.md").write_text(render_markdown(evidence), encoding="utf-8")
    print(f"Wrote {(PROPOSAL / 'VALIDATION.json').relative_to(ROOT)} and VALIDATION.md: "
          f"{evidence['gate_totals']}")
    return 0


def render_markdown(evidence: dict) -> str:
    identity = evidence["identity"]
    counts = evidence["counts"]
    totals = evidence["gate_totals"]
    lines = [
        "# Lane validation evidence",
        "",
        "Generated by "
        "`tools/architecture/lane_claude_classification/run_lane_validation.py`; the "
        "machine-readable record is `VALIDATION.json` and this file is rendered from it, "
        "so the two cannot disagree.",
        "",
        "## Identity",
        "",
        f"- Generated (UTC): `{evidence['generated_utc']}`",
        f"- Lane: `{evidence['lane']}` ({evidence['engine']} subscription "
        f"{evidence['subscription']})",
        f"- Frozen base SHA: `{identity['frozen_base_sha']}`",
        f"- Branch: `{identity['branch']}`",
        f"- HEAD: `{identity['head']}`",
        f"- Base is an ancestor of HEAD: `{identity['base_is_ancestor_of_head']}`",
        f"- Commits since base: {identity['commits_since_base']}",
        f"- Uncommitted lines in `git status --porcelain`: "
        f"{identity['status_porcelain_lines']}",
        f"- Toolchain: `{identity['toolchain']}`",
        "",
        "## Inputs",
        "",
        f"- Frozen packet inventory SHA-256: "
        f"`{evidence['inputs']['packet_read_only_modules_sha256']}`",
        f"- Baseline format-2 stream: `{evidence['inputs']['baseline_stream_zip']}`",
        f"- Baseline stream SHA-256: `{evidence['inputs']['baseline_stream_zip_sha256']}`",
        "",
        "## Counts",
        "",
        f"- Classification rows: {counts['classification_rows']} "
        f"({', '.join(f'{k}={v}' for k, v in sorted(counts['classification_tiers'].items()))})",
        f"- Deferred reusable rows: {counts['classification_deferred_rows']}; "
        f"split queue: {counts['classification_split_queue']}",
        f"- Chapter 9: {counts['ch09_destinations']} destinations, "
        f"{counts['ch09_ownership_rows']} ownership rows, "
        f"{counts['ch09_private_rewrites']} private rewrites",
        f"- Chapter 11: {counts['ch11_destinations']} destinations, "
        f"{counts['ch11_ownership_rows']} ownership rows, "
        f"{counts['ch11_private_rewrites']} private rewrites",
        "",
        "## Normalized format-2 hashes",
        "",
        "| Chapter | Stream | Rows | SHA-256 |",
        "| --- | --- | --- | --- |",
    ]
    for chapter, groups in sorted(evidence["normalized_hashes"].items()):
        for stream, value in sorted(groups.items()):
            lines.append(
                f"| {chapter} | {stream} | {value['rows']} | `{value['sha256']}` |"
            )
    lines += [
        "",
        "## Gates",
        "",
        f"**{totals['pass']} passed, {totals['fail']} failed, "
        f"{totals['not_run']} not run.** A failing gate keeps its real exit code; "
        "nothing here is claimed that did not run.",
        "",
        "| Result | Exit | Seconds | Command |",
        "| --- | --- | --- | --- |",
    ]
    for record in evidence["gates"]:
        command = " ".join(record["command"]).replace("|", r"\|")
        exit_code = "-" if record["exit_code"] is None else record["exit_code"]
        lines.append(
            f"| {record['status']} | {exit_code} | {record['duration_seconds']} | "
            f"`{command}` |"
        )
    failures = [record for record in evidence["gates"] if record["status"] != "pass"]
    if failures:
        lines += ["", "### Gates that did not pass", ""]
        for record in failures:
            lines.append(f"- **{record['label']}** (exit `{record['exit_code']}`):")
            for tail in record["output_tail"]:
                lines.append(f"  - `{tail[:300]}`")
    pristine = evidence.get("pristine_baseline", {})
    if pristine.get("present"):
        lines += [
            "",
            "## Pristine baseline",
            "",
            f"- Directory: `{pristine['directory']}`",
            f"- External to the repository: `{pristine['external_to_repository']}`",
            f"- Candidate modules: {pristine['candidate_modules']}; with compiled "
            f".ilean: {pristine['modules_with_ilean']}",
            f"- Manifest `{pristine['manifest']}` SHA-256: "
            f"`{pristine['manifest_sha256']}`",
            "",
            "This lane moves no declaration, so the manifest is a baseline record for the "
            "integrator's post-migration comparison rather than a before/after pair.",
        ]
    lines += [
        "",
        "## Tracked artifact hashes",
        "",
        "| Path | Bytes | Rows | SHA-256 |",
        "| --- | --- | --- | --- |",
    ]
    for relative, entry in sorted(evidence["artifacts"].items()):
        if not entry.get("present"):
            lines.append(f"| `{relative}` | missing | - | - |")
            continue
        lines.append(
            f"| `{relative}` | {entry['bytes']} | {entry.get('rows', '-')} | "
            f"`{entry['sha256']}` |"
        )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
