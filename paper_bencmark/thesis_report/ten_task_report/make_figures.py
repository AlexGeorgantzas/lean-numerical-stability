#!/usr/bin/env python3
"""Rebuild a ten-task, full-scope report from sealed N/L pairs.

The ten IDs come from the dated, post-outcome selection manifest. This script
does not rerun contestants, alter candidate files, or change audit verdicts.
"""

from __future__ import annotations

import csv
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(PARENT))
import make_figures as shared  # noqa: E402 - intentionally reuse primary plotting code

SOURCE = ROOT / "paper_bencmark/pilot35/RESULTS_15.json"
SELECTION = PARENT / "posthoc_10/generated/summary.json"
WARM = PARENT / "generated/summary.json"
REUSE = PARENT / "generated/realized_reuse.json"
ADMISSION = ROOT / "paper_bencmark/formalization_benchmark/design33/ADMISSION_15.json"
FIG = HERE / "figures"
GEN = HERE / "generated"
BLUE, ORANGE, RED, GRAY = "#24547a", "#d27834", "#b94b55", "#59636e"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name: str) -> None:
    plt.savefig(FIG / (name + ".pdf"), bbox_inches="tight", pad_inches=.12)
    plt.close()


def score_line(tasks: list[dict], scores: dict[str, int]) -> str:
    counts = Counter(scores[t["task_id"]] for t in tasks)
    return "Reuse scores: " + ", ".join(f"{s}/3 x {counts[s]}" for s in (1, 2, 3))


def plot_pairbars(tasks: list[dict], key: str, title: str, xlabel: str,
                  name: str, warm_add: float = 0, scale: float = 1) -> None:
    labels = [shared.short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, ax = plt.subplots(figsize=(9.1, 6.5))
    ax.barh(y-.19, [t["N"][key]/scale for t in tasks], .37,
            color=BLUE, label="N: Mathlib")
    ax.barh(y+.19, [t["L"][key]/scale+warm_add for t in tasks], .37,
            color=ORANGE, label="L: NumStability")
    ax.set_yticks(y, labels, fontsize=8.5)
    ax.invert_yaxis()
    ax.set_xlabel(xlabel)
    ax.set_title(title, loc="left", fontweight="bold")
    ax.grid(axis="x", alpha=.2)
    ax.set_axisbelow(True)
    fig.legend(loc="upper center", bbox_to_anchor=(.72, .985), ncol=2,
               frameon=False, fontsize=8)
    shared.add_task_score_key(fig)
    fig.tight_layout(rect=(0, .04, 1, .91))
    save(name)


def plot_averages(tasks: list[dict], seconds: float, tokens: int,
                  scores: dict[str, int]) -> None:
    n = len(tasks)
    groups = [
        [("Formalization", "formalization_seconds_inclusive", 1, 0),
         ("Proof", "proof_seconds_inclusive", 1, 0),
         ("Total", "total_seconds_inclusive", 1, 0),
         ("Total + warm", "total_seconds_inclusive", 1, seconds/n)],
        [("Formalization", "formalization_tokens_net_new", 1000, 0),
         ("Proof", "proof_tokens_net_new", 1000, 0),
         ("Total", "total_tokens_net_new", 1000, 0),
         ("Total + warm", "total_tokens_net_new", 1000, tokens/(1000*n))],
        [("Statement", "statement_code_lines", 1, 0),
         ("Proof", "proof_code_lines", 1, 0)],
    ]
    fig, axes = plt.subplots(1, 3, figsize=(12.1, 5))
    for ax, group, title, unit in zip(axes, groups,
                                      ("Time", "Net-new tokens", "Code"),
                                      ("Seconds/task", "Thousands/task", "Lines/task")):
        y = np.arange(len(group))
        nv = [np.mean([t["N"][key]/scale for t in tasks]) for _, key, scale, _ in group]
        lv = [np.mean([t["L"][key]/scale for t in tasks])+warm
              for _, key, scale, warm in group]
        ax.barh(y-.18, nv, height=.35, color=BLUE, label="N")
        ax.barh(y+.18, lv, height=.35, color=ORANGE, label="L")
        ax.set_yticks(y, [row[0] for row in group], fontsize=8)
        ax.invert_yaxis()
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel(unit)
        ax.grid(axis="x", alpha=.2)
        ax.set_axisbelow(True)
    axes[0].legend(frameon=False)
    fig.text(.5, .015, score_line(tasks, scores), ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("07_averages")


def plot_code(tasks: list[dict]) -> None:
    labels = [shared.short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.7, 6.2), sharey=True)
    for ax, metric, title in zip(axes, ("statement_code_lines", "proof_code_lines"),
                                  ("Audited statement", "Kernel-accepted proof")):
        ax.barh(y-.19, [t["N"][metric] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][metric] for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels, fontsize=8)
        ax.invert_yaxis()
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Nonblank, noncomment Lean lines")
        ax.grid(axis="x", alpha=.2)
    axes[1].legend(frameon=False)
    shared.add_task_score_key(fig)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("08_code_lines")


def plot_direct_count(rows: list[dict], scores: dict[str, int]) -> dict:
    x = np.array([r["proof_count"] for r in rows])
    panels = (("time_gain_pct", "Total-time gain (%)"),
              ("token_gain_pct", "Net-new-token gain (%)"),
              ("proof_line_gain_pct", "Proof-line gain (%)"),
              ("formal_gain_pct", "Formalization-time gain (%)"))
    fig, axes = plt.subplots(2, 2, figsize=(9.7, 7.1))
    stats = {}
    for ax, (key, title) in zip(axes.flat, panels):
        y = np.array([r[key] for r in rows])
        for i, r in enumerate(rows):
            color = ORANGE if r["retained"] else BLUE
            marker = "o" if r["retained"] else "D"
            ax.scatter(x[i], y[i], s=100, color=color, marker=marker,
                       edgecolor="white", linewidth=.6, zorder=3)
            ax.text(x[i], y[i], str(scores[r["task_id"]]), ha="center",
                    va="center", color="white", fontsize=6, fontweight="bold", zorder=4)
        rho, p = spearmanr(x, y)
        stats[key] = {"rho": float(rho), "p_exploratory": float(p), "n": len(rows)}
        ax.text(.02, .98, f"Rank rho={rho:+.2f}; n={len(rows)}",
                transform=ax.transAxes, ha="left", va="top", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.8))
        ax.axhline(0, color=GRAY, linewidth=.8)
        ax.set_xlabel("Distinct direct proof-term declarations")
        ax.set_ylabel(title)
        ax.grid(alpha=.18)
    fig.text(.5, .01, score_line([{"task_id": r["task_id"]} for r in rows], scores),
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .04, 1, 1))
    save("10_direct_declaration_scatter")
    return stats


def plot_cohorts(tasks: list[dict], scores: dict[str, int]) -> None:
    groups = [("Previously favorable", [t for t in tasks if t["outcome_aware_retained"]]),
              ("Newly screened", [t for t in tasks if not t["outcome_aware_retained"]]),
              ("All reported", tasks)]
    fig, axes = plt.subplots(1, 3, figsize=(11, 3.4))
    for panel, (ax, key, title) in enumerate(zip(axes,
                              ("total_seconds_inclusive", "proof_code_lines", "total_tokens_net_new"),
                              ("Total active time", "Proof-code lines", "Net-new tokens"))):
        values = [100 * (sum(t["N"][key] for t in sub) - sum(t["L"][key] for t in sub)) /
                  sum(t["N"][key] for t in sub) for _, sub in groups]
        ax.barh(range(3), values, color=["#267e67" if v >= 0 else RED for v in values])
        labels = ([f"{name} (n={len(sub)})" for name, sub in groups]
                  if panel == 0 else [""] * 3)
        ax.set_yticks(range(3), labels, fontsize=8)
        ax.invert_yaxis()
        ax.axvline(0, color=GRAY, linewidth=.8)
        ax.set_xlim(-65, 65)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("N-to-L aggregate gain (%)")
        for i, v in enumerate(values):
            ax.text(v+(1 if v >= 0 else -1), i, f"{v:+.1f}%",
                    ha="left" if v >= 0 else "right", va="center", fontsize=8)
        ax.grid(axis="x", alpha=.18)
    fig.text(.5, .01, score_line(tasks, scores), ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("11_cohort_strata")


def plot_cumulative(tasks: list[dict], seconds: float, tokens: int,
                    scores: dict[str, int]) -> None:
    x = np.arange(1, len(tasks)+1)
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.5))
    for ax, key, warm, divisor, title in (
        (axes[0], "total_seconds_inclusive", seconds, 1, "Cumulative active seconds"),
        (axes[1], "total_tokens_net_new", tokens, 1000, "Cumulative net-new tokens (thousands)"),
    ):
        n = np.cumsum([t["N"][key] for t in tasks])/divisor
        l = np.cumsum([t["L"][key] for t in tasks])/divisor
        ax.plot(x, n, marker="o", ms=3, color=BLUE, label="N")
        ax.plot(x, l, marker="o", ms=3, color=ORANGE, label="L")
        ax.plot(x, l+warm/divisor, marker="o", ms=3, color=RED,
                label="L + one-time warm-up")
        ax.set_xticks(x)
        ax.set_xlabel("Task in reported sequence")
        ax.set_ylabel(title)
        ax.grid(alpha=.18)
    axes[0].legend(frameon=False, fontsize=8)
    fig.text(.5, .01, "Scores in sequence: " + ", ".join(
        str(scores[t["task_id"]]) + "/3" for t in tasks), ha="center", fontsize=7)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("12_cumulative_warm")


def plot_score_scatter(scored: list[dict], scores: dict[str, int]) -> dict:
    panels = (("total_time", "Total active-time gain (%)"),
              ("proof_lines", "Proof-code gain (%)"),
              ("proof_time", "Proof-time gain (%)"),
              ("total_tokens", "Net-new-token gain (%)"))
    fig, axes = plt.subplots(2, 2, figsize=(10, 7.1))
    stats = {}
    for ax, (key, title) in zip(axes.flat, panels):
        xs = []
        ys = []
        for i, row in enumerate(scored):
            score = row["score"]
            y = row["gains"][f"{key}_gain_pct"]
            x = score + ((i % 5)-2)*.045
            xs.append(score)
            ys.append(y)
            color = ORANGE if row["outcome_aware_retained"] else BLUE
            marker = "o" if row["outcome_aware_retained"] else "D"
            ax.scatter(x, y, s=100, color=color, marker=marker, zorder=3)
            ax.text(x, y, str(score), ha="center", va="center", color="white",
                    fontweight="bold", fontsize=6, zorder=4)
        rho, p = spearmanr(xs, ys)
        new_rows = [r for r in scored if not r["outcome_aware_retained"]]
        rho_new, p_new = spearmanr(
            [r["score"] for r in new_rows],
            [r["gains"][f"{key}_gain_pct"] for r in new_rows])
        stats[key] = {"rho": float(rho), "p_exploratory": float(p), "n": len(scored),
                      "new_only_rho": float(rho_new),
                      "new_only_p_exploratory": float(p_new), "new_only_n": len(new_rows)}
        ax.text(.02, .98, f"Rank rho: all {rho:+.2f}; new {rho_new:+.2f}",
                transform=ax.transAxes, ha="left", va="top", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.8))
        ax.set_xticks((1, 2, 3))
        ax.set_xlim(.65, 3.35)
        ax.set_xlabel("Realized reuse score (1-3)")
        ax.set_ylabel(title)
        ax.axhline(0, color=GRAY, linewidth=.8)
        ax.grid(alpha=.18)
    fig.text(.5, .01, score_line([{"task_id": r["task_id"]} for r in scored], scores),
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .04, 1, 1))
    save("14_reuse_scatter")
    return stats


def plot_score_groups(tasks: list[dict], scores: dict[str, int]) -> None:
    fig, axes = plt.subplots(1, 3, figsize=(11.2, 4))
    for ax, key, title in zip(axes,
                              ("total_seconds_inclusive", "proof_code_lines", "total_tokens_net_new"),
                              ("Active time", "Proof code", "Net-new tokens")):
        values = []
        counts = []
        for score in (1, 2, 3):
            group = [t for t in tasks if scores[t["task_id"]] == score]
            n = sum(t["N"][key] for t in group)
            l = sum(t["L"][key] for t in group)
            values.append(100*(n-l)/n)
            counts.append(len(group))
        y = np.arange(3)
        ax.barh(y, values, color=["#267e67" if v >= 0 else RED for v in values])
        ax.set_yticks(y, [f"Score {s}/3 (n={n})" for s, n in zip((1, 2, 3), counts)], fontsize=8)
        ax.invert_yaxis()
        ax.set_xlim(-75, 75)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Aggregate gain for L (%)")
        ax.axvline(0, color=GRAY, linewidth=.8)
        for i, value in enumerate(values):
            ax.text(value+(1 if value >= 0 else -1), i, f"{value:+.1f}%",
                    ha="left" if value >= 0 else "right", va="center", fontsize=8)
        ax.grid(axis="x", alpha=.18)
    fig.tight_layout()
    save("15_reuse_score_groups")


def plot_attempts(tasks: list[dict]) -> None:
    labels = [shared.short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 6.1), sharey=True)
    for ax, key, title in zip(axes,
                              ("formalization_submissions", "proof_submissions"),
                              ("Faithfulness submissions", "Proof submissions")):
        ax.barh(y-.19, [t["N"][key] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key] for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels, fontsize=8)
        ax.invert_yaxis()
        ax.set_xlim(0, 4.4)
        ax.set_xticks((0, 1, 2, 3, 4))
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Frozen submissions (maximum four)")
        ax.grid(axis="x", alpha=.18)
    axes[1].legend(frameon=False)
    shared.add_task_score_key(fig)
    fig.tight_layout(rect=(0, .05, 1, 1))
    save("16_attempts")


def write_tables(tasks: list[dict], scans: list[dict], reuse: list[dict]) -> None:
    with (GEN / "task_times_table.tex").open("w") as out:
        for t in tasks:
            n, l = t["N"], t["L"]
            values = [t["task_id"],
                      *(f'{v["formalization_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["proof_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["total_seconds_inclusive"]:.0f}' for v in (n, l)),
                      *(f'{v["total_tokens_net_new"]/1000:.0f}' for v in (n, l))]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "task_code_table.tex").open("w") as out:
        for t, scan in zip(tasks, scans):
            n, l = t["N"], t["L"]
            values = [t["task_id"], t["source_cluster"],
                      "yes" if t["outcome_aware_retained"] else "no",
                      str(n["statement_code_lines"]), str(l["statement_code_lines"]),
                      str(n["proof_code_lines"]), str(l["proof_code_lines"]),
                      str(scan["substantive_statement_count"]),
                      str(scan["proof_count"]),
                      str(l["formalization_submissions"]), str(l["proof_submissions"])]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "reuse_table.tex").open("w") as out:
        for r in reuse:
            values = [r["task_id"], str(r["score"]),
                      *("yes" if r["roles"][role]["used"] else "--"
                        for role in ("foundation", "computation", "analysis")),
                      *(f'{r["gains"][key]:+.0f}' for key in
                        ("proof_lines_gain_pct", "proof_time_gain_pct",
                         "total_time_gain_pct", "total_tokens_gain_pct"))]
            out.write(" & ".join(values) + r" \\" + "\n")
    with (GEN / "declarations_table.tex").open("w") as out:
        for scan in scans:
            def family(names):
                rules = (("fl_recursiveSum", "recursive sum"), ("fl_dotProduct", "dot product"),
                         ("SumTree", "sum tree"), ("FloatingPointFormat", "finite FP format"),
                         ("LSNormwiseBackwardError", "least squares"),
                         ("gamma", "gamma bound"), ("prod_error_bound", "product error"),
                         ("infNormVec", "infinity norm"))
                labels = [label for pattern, label in rules if any(pattern in name for name in names)]
                return ", ".join(labels[:3]) if labels else ("other" if names else "none")
            stmt = scan["substantive_statement_names"]
            proof = scan["proof_names"]
            values = [scan["task_id"], family(stmt), str(len(stmt)), family(proof), str(len(proof))]
            out.write(" & ".join(values) + r" \\" + "\n")


def write_aggregate_table(summary: dict) -> None:
    measured = summary["groups"]["reported"]["metrics"]
    rows = [
        ("Formalization seconds", "formalization_seconds_inclusive", 0),
        ("Proof seconds", "proof_seconds_inclusive", 0),
        ("Total active seconds", "total_seconds_inclusive", 0),
        ("Total + warm seconds", "total_seconds_inclusive", summary["warm_seconds"]),
        ("Formalization net-new tokens", "formalization_tokens_net_new", 0),
        ("Proof net-new tokens", "proof_tokens_net_new", 0),
        ("Total net-new tokens", "total_tokens_net_new", 0),
        ("Total + warm net-new tokens", "total_tokens_net_new", summary["warm_net_new_tokens"]),
        ("Statement code lines", "statement_code_lines", 0),
        ("Proof code lines", "proof_code_lines", 0),
    ]
    with (GEN / "aggregate_table.tex").open("w") as out:
        for label, metric, warm in rows:
            n = measured[metric]["N"]
            l = measured[metric]["L"] + warm
            displayed = ((f"{n:,.1f}", f"{l:,.1f}") if "seconds" in label
                         else (f"{n:,.0f}", f"{l:,.0f}"))
            out.write(f"{label} & {displayed[0]} & {displayed[1]} & "
                      f"{l/n:.3f} & {100*(n-l)/n:+.1f}\\% \\\\\n")
        out.write("\\bottomrule\n")


def main() -> None:
    FIG.mkdir(exist_ok=True)
    GEN.mkdir(exist_ok=True)
    selected_record = json.loads(SELECTION.read_text())
    assert selected_record["status"] == "POST_HOC_OUTCOME_SELECTED_EXPLORATORY_NOT_HELD_OUT"
    selected_ids = selected_record["selected_task_ids"]
    source = json.loads(SOURCE.read_text())
    tasks = [t for t in source["tasks"] if t["task_id"] in selected_ids]
    assert [t["task_id"] for t in tasks] == selected_ids and len(tasks) == 10
    assert all(t["paired_statement_eligible"] and t["paired_proof_eligible"] for t in tasks)
    assert all(t[c]["proof_status"] == "PROVED_FROZEN_STATEMENT"
               for t in tasks for c in ("N", "L"))
    assert sum(t["outcome_aware_retained"] for t in tasks) == 5
    selection_input_sha = selected_record["source_sha256"]
    assert selection_input_sha["primary_summary.json"] == digest(WARM)
    admission = json.loads(ADMISSION.read_text())
    reuse_full = json.loads(REUSE.read_text())
    reuse_map = {r["task_id"]: r for r in reuse_full["rows"]}
    reuse = [reuse_map[t["task_id"]] for t in tasks]
    scores = {r["task_id"]: r["score"] for r in reuse}
    scans = shared.declaration_scan(tasks)
    for task, scan, row in zip(tasks, scans, reuse):
        task_id = task["task_id"]
        packet = ROOT / f"paper_bencmark/formalization_benchmark/design33/packets/{task_id}.json"
        assert digest(packet) == admission["tasks"][task_id]["source_packet_sha256"]
        assert row["source_packet_sha256"] == digest(packet)
        statement = set(scan["statement_names"])
        proof = set(scan["proof_names"])
        for role in ("foundation", "computation", "analysis"):
            assert set(row["roles"][role]["witnesses"]) <= statement | proof
            if role == "analysis":
                assert set(row["roles"][role]["witnesses"]) <= proof
        assert row["score"] == sum(bool(row["roles"][role]["witnesses"])
                                   for role in ("foundation", "computation", "analysis"))
    warm = json.loads(WARM.read_text())
    seconds = warm["warm_seconds"]
    tokens = warm["warm_net_new_tokens"]
    shared.FIG = FIG
    shared.GENERATED = GEN
    shared.SCORE_BY_TASK = scores
    plot_pairbars(tasks, "total_seconds_inclusive", "Total active time, excluding one-time warm-up",
                  "Contestant-active seconds", "01_total_time_ex_warm")
    plot_pairbars(tasks, "total_seconds_inclusive", "Total active time, warm-up allocated over ten tasks",
                  f"Contestant-active seconds + {seconds/10:.2f} s/task for L",
                  "02_total_time_in_warm", warm_add=seconds/10)
    shared.phases(tasks, "seconds", "03_phase_times")
    plot_pairbars(tasks, "total_tokens_net_new", "Net-new tokens, excluding warm-up",
                  "Net-new tokens (thousands)", "04_total_tokens_ex_warm", scale=1000)
    plot_pairbars(tasks, "total_tokens_net_new", "Net-new tokens, warm-up allocated over ten tasks",
                  f"Net-new tokens (thousands) + {tokens/10000:.2f}k/task for L",
                  "05_total_tokens_in_warm", warm_add=tokens/10000, scale=1000)
    shared.phases(tasks, "tokens", "06_phase_tokens")
    plot_averages(tasks, seconds, tokens, scores)
    plot_code(tasks)
    shared.coverage_heatmap(scans, reuse)
    direct_correlations = plot_direct_count(scans, scores)
    plot_cohorts(tasks, scores)
    plot_cumulative(tasks, seconds, tokens, scores)
    shared.hardware(tasks)
    score_correlations = plot_score_scatter(reuse, scores)
    plot_score_groups(tasks, scores)
    plot_attempts(tasks)
    write_tables(tasks, scans, reuse)
    (GEN / "source_task_ledger.json").write_text(json.dumps({
        "status": "POST_OUTCOME_SELECTED_TEN_TASKS",
        "source_sha256": digest(SOURCE),
        "selection_manifest_sha256": digest(SELECTION),
        "tasks": tasks,
    }, indent=2) + "\n")
    (GEN / "declaration_scan.json").write_text(json.dumps(scans, indent=2) + "\n")
    (GEN / "realized_reuse.json").write_text(json.dumps({
        "scientific_status": "POST_OUTCOME_EXPLORATORY_MANUAL_ANNOTATION_NOT_BLIND",
        "source_ledger_sha256": digest(REUSE),
        "rows": reuse,
    }, indent=2) + "\n")
    (GEN / "source_registry.json").write_text(json.dumps({
        "source_admission_sha256": digest(ADMISSION),
        "tasks": {task_id: admission["tasks"][task_id] for task_id in selected_ids},
    }, indent=2) + "\n")
    metrics = ("formalization_seconds_inclusive", "proof_seconds_inclusive",
               "total_seconds_inclusive", "formalization_tokens_net_new",
               "proof_tokens_net_new", "total_tokens_net_new",
               "statement_code_lines", "proof_code_lines")
    groups = {"reported": tasks,
              "previously_favorable": [t for t in tasks if t["outcome_aware_retained"]],
              "newly_screened": [t for t in tasks if not t["outcome_aware_retained"]]}
    groups.update({f"score_{s}": [t for t in tasks if scores[t["task_id"]] == s]
                   for s in (1, 2, 3)})
    summary = {
        "status": "TEN_TASK_RETROSPECTIVE_OUTCOME_INFORMED_DEVELOPMENT_EVIDENCE",
        "selection_disclosure": "Task selection and reuse annotation were made after outcome review; not a held-out or causal estimate.",
        "source_sha256": {"sealed_result": digest(SOURCE), "selection_manifest": digest(SELECTION),
                          "warm_summary": digest(WARM), "reuse_ledger": digest(REUSE),
                          "admission": digest(ADMISSION)},
        "scheduled_task_ids": [t["task_id"] for t in tasks],
        "source_cluster_counts": dict(Counter(t["source_cluster"] for t in tasks)),
        "score_counts": dict(Counter(scores.values())),
        "warm_seconds": seconds,
        "warm_net_new_tokens": tokens,
        "groups": {},
        "direct_declaration_rank_correlations": direct_correlations,
        "reuse_score_rank_correlations": score_correlations,
    }
    for name, subset in groups.items():
        summary["groups"][name] = {"n": len(subset), "task_ids": [t["task_id"] for t in subset],
                                    "metrics": {}}
        for metric in metrics:
            n = sum(t["N"][metric] for t in subset)
            l = sum(t["L"][metric] for t in subset)
            summary["groups"][name]["metrics"][metric] = {
                "N": n, "L": l, "gain_pct": 100*(n-l)/n}
    summary["warm_inclusive"] = {
        "active_seconds_L": summary["groups"]["reported"]["metrics"]["total_seconds_inclusive"]["L"] + seconds,
        "net_new_tokens_L": summary["groups"]["reported"]["metrics"]["total_tokens_net_new"]["L"] + tokens,
    }
    summary["reach"] = {
        "substantive_statement_tasks": sum(bool(r["substantive_statement_names"]) for r in scans),
        "direct_proof_tasks": sum(bool(r["proof_names"]) for r in scans),
        "L_faster_tasks": sum(t["L"]["total_seconds_inclusive"] < t["N"]["total_seconds_inclusive"] for t in tasks),
        "L_shorter_proof_tasks": sum(t["L"]["proof_code_lines"] < t["N"]["proof_code_lines"] for t in tasks),
    }
    summary["audit_overhead"] = {
        c: {"seconds": sum(t[c]["audit_seconds_excluded"] for t in tasks),
            "provider_total_tokens": sum(t[c]["audit_usage_excluded"]["total_tokens"] for t in tasks)}
        for c in ("N", "L")}
    summary["hardware_sampled_peaks"] = {
        c: {"cpu_cores": max(t[c]["peak_cpu_cores_sampled"] for t in tasks),
            "ram_gib": max(t[c]["peak_ram_gib_sampled"] for t in tasks)}
        for c in ("N", "L")}
    (GEN / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    write_aggregate_table(summary)
    print("PASS: ten selected task pairs, exact source identities, reuse witnesses, and derived figures")
    print(json.dumps({"tasks": len(tasks), "source_clusters": summary["source_cluster_counts"],
                      "score_counts": summary["score_counts"],
                      "time_gain_pct": summary["groups"]["reported"]["metrics"]["total_seconds_inclusive"]["gain_pct"],
                      "proof_line_gain_pct": summary["groups"]["reported"]["metrics"]["proof_code_lines"]["gain_pct"]}, indent=2))


if __name__ == "__main__":
    main()
