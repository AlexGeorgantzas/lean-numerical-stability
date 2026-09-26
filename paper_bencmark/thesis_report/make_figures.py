#!/usr/bin/env python3
"""Rebuild every figure and the numeric appendix from frozen Pilot 35 results.

The only manually supplied cost is read from the archived Pilot 27 warm-root
record. No benchmark task, score, or result is modified by this program.
"""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RESULTS = ROOT / "paper_bencmark/pilot35/RESULTS_15.json"
WARM = HERE / "evidence/warm-root.json"
FIG = HERE / "figures"
GENERATED = HERE / "generated"
BLUE = "#24547a"
ORANGE = "#d27834"
GREEN = "#267e67"
RED = "#b94b55"
GRAY = "#59636e"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name: str) -> None:
    plt.savefig(FIG / f"{name}.pdf", bbox_inches="tight", pad_inches=0.12)
    plt.close()


def short(s: str) -> str:
    return s.replace("P14-SHIFTED-", "P14-S-").replace("P14-", "P14-")


def pairbars(tasks, key, title, xlabel, name, warm_add=0.0, scale=1.0):
    labels = [short(t["task_id"]) for t in tasks]
    n = len(labels)
    fig, ax = plt.subplots(figsize=(9.1, 7.3))
    y = np.arange(n)
    nv = np.array([t["N"][key] / scale for t in tasks])
    lv = np.array([t["L"][key] / scale + warm_add for t in tasks])
    ax.barh(y - 0.19, nv, height=0.37, color=BLUE, label="N: Mathlib")
    ax.barh(y + 0.19, lv, height=0.37, color=ORANGE, label="L: NumStability")
    ax.set_yticks(y, labels)
    ax.invert_yaxis()
    ax.set_xlabel(xlabel)
    ax.set_title(title, loc="left", fontweight="bold")
    ax.grid(axis="x", alpha=0.2)
    ax.set_axisbelow(True)
    ax.legend(loc="lower right", frameon=False)
    fig.tight_layout()
    save(name)


def phases(tasks, unit, name):
    labels = [short(t["task_id"]) for t in tasks]
    if unit == "seconds":
        ks = [("formalization_seconds_inclusive", "Formalization"),
              ("proof_seconds_inclusive", "Proof")]
        scale, xlabel = 1, "Contestant-active seconds"
    else:
        ks = [("formalization_tokens_net_new", "Formalization"),
              ("proof_tokens_net_new", "Proof")]
        scale, xlabel = 1000, "Net-new tokens (thousands)"
    fig, axes = plt.subplots(1, 2, figsize=(11.5, 7.3), sharey=True)
    y = np.arange(len(tasks))
    for ax, (key, title) in zip(axes, ks):
        ax.barh(y - 0.19, [t["N"][key] / scale for t in tasks], .37,
                color=BLUE, label="N")
        ax.barh(y + 0.19, [t["L"][key] / scale for t in tasks], .37,
                color=ORANGE, label="L")
        ax.set_yticks(y, labels)
        ax.invert_yaxis()
        ax.set_xlabel(xlabel)
        ax.set_title(title, fontweight="bold")
        ax.grid(axis="x", alpha=.2)
        ax.set_axisbelow(True)
    axes[1].legend(loc="lower right", frameon=False)
    fig.tight_layout()
    save(name)


def averages(tasks, warm_seconds, warm_tokens):
    metrics = [
        ("Formalization time", "formalization_seconds_inclusive", 1, 0),
        ("Proof time", "proof_seconds_inclusive", 1, 0),
        ("Total time", "total_seconds_inclusive", 1, 0),
        ("Total + warm", "total_seconds_inclusive", 1, warm_seconds / 15),
        ("Formalization tokens", "formalization_tokens_net_new", 1000, 0),
        ("Proof tokens", "proof_tokens_net_new", 1000, 0),
        ("Total tokens", "total_tokens_net_new", 1000, 0),
        ("Total + warm tokens", "total_tokens_net_new", 1000, warm_tokens / 15000),
        ("Statement lines", "statement_code_lines", 1, 0),
        ("Proof lines", "proof_code_lines", 1, 0),
    ]
    fig, axes = plt.subplots(1, 3, figsize=(12.2, 5.5))
    groups = [metrics[:4], metrics[4:8], metrics[8:]]
    for ax, group, xlabel in zip(axes, groups,
                                 ["Mean seconds / task", "Mean tokens / task (thousands)", "Mean code lines / task"]):
        ys = np.arange(len(group))
        ax.barh(ys - .18, [np.mean([t["N"][k] / s for t in tasks])
                             for _, k, s, _ in group], .35, color=BLUE, label="N")
        ax.barh(ys + .18, [np.mean([t["L"][k] / s for t in tasks]) + w
                             for _, k, s, w in group], .35, color=ORANGE, label="L")
        ax.set_yticks(ys, [g[0] for g in group], fontsize=8)
        ax.invert_yaxis()
        ax.set_xlabel(xlabel)
        ax.grid(axis="x", alpha=.2)
        ax.set_axisbelow(True)
    axes[0].legend(frameon=False)
    fig.tight_layout()
    save("07_averages")


def declaration_scan(tasks):
    # These are transparent syntactic indicators, not a semantic overlap score.
    algorithm_markers = ("fl_recursiveSum", "fl_dotProduct", "SumTree",
                         "FloatingPointFormat", "LSNormwiseBackwardError")
    error_markers = ("error", "Error", "gamma", "prod_error_bound",
                     "sumSuffix", "signedRelErrorWitness")
    rows = []
    for t in tasks:
        statement = t.get("direct_statement_numstability_names") or []
        substantive = t.get("substantive_statement_numstability_names") or []
        proof = t["L"].get("proof_term_numstability_names") or []
        rows.append({
            "task_id": t["task_id"],
            "retained": int(t["outcome_aware_retained"]),
            "statement_names": statement,
            "substantive_statement_names": substantive,
            "proof_names": proof,
            "statement_count": len(statement),
            "substantive_statement_count": len(substantive),
            "proof_count": len(proof),
            "algorithm_statement": int(any(m in n for n in substantive for m in algorithm_markers)),
            "error_proof": int(any(m in n for n in proof for m in error_markers)),
            "formal_attempts_L": t["L"]["formalization_submissions"],
            "proof_attempts_L": t["L"]["proof_submissions"],
            "time_gain_pct": 100 * (t["N"]["total_seconds_inclusive"] - t["L"]["total_seconds_inclusive"]) / t["N"]["total_seconds_inclusive"],
            "formal_gain_pct": 100 * (t["N"]["formalization_seconds_inclusive"] - t["L"]["formalization_seconds_inclusive"]) / t["N"]["formalization_seconds_inclusive"],
            "proof_time_gain_pct": 100 * (t["N"]["proof_seconds_inclusive"] - t["L"]["proof_seconds_inclusive"]) / t["N"]["proof_seconds_inclusive"],
            "token_gain_pct": 100 * (t["N"]["total_tokens_net_new"] - t["L"]["total_tokens_net_new"]) / t["N"]["total_tokens_net_new"],
            "proof_line_gain_pct": 100 * (t["N"]["proof_code_lines"] - t["L"]["proof_code_lines"]) / t["N"]["proof_code_lines"],
        })
    return rows


def coverage_heatmap(rows):
    binary = np.array([[r["substantive_statement_count"] > 0,
                        r["algorithm_statement"], r["proof_count"] > 0,
                        r["error_proof"]] for r in rows], dtype=float)
    gains = np.array([[r["formal_gain_pct"], r["proof_time_gain_pct"],
                       r["time_gain_pct"], r["token_gain_pct"],
                       r["proof_line_gain_pct"]] for r in rows])
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 7.5),
                                   gridspec_kw={"width_ratios": [4, 5]}, sharey=True)
    ax1.imshow(binary, cmap=matplotlib.colors.ListedColormap(["#e7e9e9", GREEN]),
               vmin=0, vmax=1, aspect="auto")
    im = ax2.imshow(gains, cmap="RdBu", vmin=-100, vmax=100, aspect="auto")
    ax1.set_yticks(range(len(rows)), [short(r["task_id"]) for r in rows], fontsize=8)
    ax2.set_yticks(range(len(rows)))
    ax1.set_xticks(range(4), ["Substantive\nstatement", "Algorithm/format\nstatement",
                               "Any proof\nreach", "Error/bound\nproof"], fontsize=8)
    ax2.set_xticks(range(5), ["Formal\ntime", "Proof\ntime", "Total\ntime",
                               "Total\ntokens", "Proof\nlines"], fontsize=8)
    for i in range(len(rows)):
        for j in range(4):
            ax1.text(j, i, "yes" if binary[i, j] else "--", ha="center", va="center",
                     color="white" if binary[i, j] else GRAY, fontsize=7)
        for j in range(5):
            ax2.text(j, i, f"{gains[i,j]:+.0f}", ha="center", va="center", fontsize=7,
                     color="white" if abs(gains[i,j]) > 65 else "#17212b")
    for ax in (ax1, ax2):
        ax.tick_params(length=0)
        ax.set_xticks(np.arange(-.5, len(ax.get_xticks()), 1), minor=True)
        ax.set_yticks(np.arange(-.5, len(rows), 1), minor=True)
        ax.grid(which="minor", color="white", linewidth=2)
        ax.tick_params(which="minor", length=0)
    fig.colorbar(im, ax=ax2, shrink=.65, label="N-to-L gain (%); positive favors L")
    fig.tight_layout()
    save("09_coverage_heatmap")


def scatter_overlap(rows):
    x = np.array([r["proof_count"] for r in rows])
    ys = [("time_gain_pct", "Total time gain (%)"),
          ("token_gain_pct", "Net-new token gain (%)"),
          ("proof_line_gain_pct", "Proof-line gain (%)"),
          ("formal_attempts_L", "L statement submissions")]
    fig, axes = plt.subplots(2, 2, figsize=(9.4, 7.3))
    for ax, (key, label) in zip(axes.flat, ys):
        y = np.array([r[key] for r in rows])
        colors = [ORANGE if r["retained"] else BLUE for r in rows]
        ax.scatter(x, y, c=colors, s=50, edgecolor="white", linewidth=.7)
        ax.axhline(0 if key != "formal_attempts_L" else 1, color=GRAY, linewidth=.8)
        ax.set_xlabel("Distinct direct proof-term declarations")
        ax.set_ylabel(label)
        ax.grid(alpha=.18)
        if len(np.unique(y)) > 1:
            rho, p = spearmanr(x, y)
            note = f"Spearman rho={rho:+.2f}, n=15 (exploratory)"
        else:
            note = "No outcome variation"
        ax.text(.02, .98, note, transform=ax.transAxes, va="top", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.85))
    fig.legend(handles=[plt.Line2D([], [], marker="o", linestyle="", color=ORANGE,
                                   label="Prior favorable retained"),
                        plt.Line2D([], [], marker="o", linestyle="", color=BLUE,
                                   label="New screened")],
               loc="upper center", bbox_to_anchor=(.5, 1.025), ncol=2, frameon=False)
    fig.tight_layout()
    save("10_overlap_scatter")


def groups(tasks):
    keys = ["proof_code_lines", "total_seconds_inclusive", "total_tokens_net_new"]
    labels = ["Prior favorable (5)", "New screened (10)", "All (15)"]
    subsets = [[t for t in tasks if t["outcome_aware_retained"]],
               [t for t in tasks if not t["outcome_aware_retained"]], tasks]
    fig, axes = plt.subplots(1, 3, figsize=(10.5, 3.8))
    for ax, key, title in zip(axes, keys, ["Proof code lines", "Total time", "Net-new tokens"]):
        gain = [100 * (sum(t["N"][key] for t in s) - sum(t["L"][key] for t in s)) /
                sum(t["N"][key] for t in s) for s in subsets]
        ax.barh(range(3), gain, color=[GREEN if g >= 0 else RED for g in gain])
        ax.axvline(0, color=GRAY, linewidth=.8)
        ax.set_yticks(range(3), labels, fontsize=8)
        ax.invert_yaxis()
        ax.set_xlabel("Aggregate gain for L (%)")
        ax.set_title(title, fontweight="bold")
        for i, v in enumerate(gain):
            ax.text(v + (1 if v >= 0 else -1), i, f"{v:+.1f}%",
                    ha="left" if v >= 0 else "right", va="center", fontsize=8)
        ax.set_xlim(min(-40, min(gain)-10), max(50, max(gain)+10))
        ax.grid(axis="x", alpha=.2)
    fig.tight_layout()
    save("11_selection_strata")


def overlap_by_selection(tasks, rows):
    # Descriptive sensitivity to outcome-aware retention: the raw pooled
    # association cannot be interpreted without this stratification.
    subsets = [
        ("Retained: both", [t for t, r in zip(tasks, rows)
                            if t["outcome_aware_retained"] and r["algorithm_statement"] and r["error_proof"]]),
        ("New: both", [t for t, r in zip(tasks, rows)
                       if not t["outcome_aware_retained"] and r["algorithm_statement"] and r["error_proof"]]),
        ("New: other", [t for t, r in zip(tasks, rows)
                        if not t["outcome_aware_retained"] and not (r["algorithm_statement"] and r["error_proof"])]),
    ]
    fig, axes = plt.subplots(1, 3, figsize=(10, 3.5))
    for ax, key, title in zip(axes,
                              ["total_seconds_inclusive", "total_tokens_net_new", "proof_code_lines"],
                              ["Total active time", "Net-new tokens", "Proof code"]):
        vals = []
        for _, taskset in subsets:
            n = sum(t["N"][key] for t in taskset)
            l = sum(t["L"][key] for t in taskset)
            vals.append(100 * (n-l)/n)
        ax.barh(range(3), vals, color=[GREEN if v >= 0 else RED for v in vals])
        ax.set_yticks(range(3), [f"{name} (n={len(ts)})" for name,ts in subsets], fontsize=8)
        ax.invert_yaxis()
        ax.axvline(0, color=GRAY, linewidth=.8)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Aggregate gain for L (%)")
        ax.set_xlim(-55, 55)
        for i, v in enumerate(vals):
            ax.text(v + (1 if v>=0 else -1), i, f"{v:+.1f}%", va="center",
                    ha="left" if v>=0 else "right", fontsize=8)
        ax.grid(axis="x", alpha=.2)
    fig.tight_layout()
    save("14_overlap_selection_sensitivity")


def amortization(tasks, warm_seconds, warm_tokens):
    fig, axes = plt.subplots(1, 2, figsize=(9.5, 3.5))
    x = np.arange(1, 16)
    for ax, key, warm, ylabel, divisor in [
        (axes[0], "total_seconds_inclusive", warm_seconds, "Cumulative contestant-active seconds", 1),
        (axes[1], "total_tokens_net_new", warm_tokens, "Cumulative net-new tokens (thousands)", 1000),
    ]:
        n = np.cumsum([t["N"][key] for t in tasks]) / divisor
        l = np.cumsum([t["L"][key] for t in tasks]) / divisor
        ax.plot(x, n, color=BLUE, marker="o", ms=3, label="N")
        ax.plot(x, l, color=ORANGE, marker="o", ms=3, label="L, excluding warm")
        ax.plot(x, l + warm / divisor, color=RED, marker="o", ms=3,
                label="L, warm charged once")
        ax.set_xlabel("Tasks in frozen schedule")
        ax.set_ylabel(ylabel)
        ax.grid(alpha=.2)
    axes[0].legend(frameon=False, fontsize=8)
    fig.tight_layout()
    save("12_cumulative_warm")


def hardware(tasks):
    labels = [short(t["task_id"]) for t in tasks]
    y = np.arange(len(tasks))
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 7.2), sharey=True)
    for ax, key, label, limit in zip(axes,
                                     ["peak_cpu_cores_sampled", "peak_ram_gib_sampled"],
                                     ["Sampled peak CPU cores", "Sampled peak RAM (GiB)"],
                                     [8, 24]):
        ax.barh(y-.19, [t["N"][key] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key] for t in tasks], .37, color=ORANGE, label="L")
        ax.axvline(limit, color=RED, linestyle="--", linewidth=.8, label="Lane limit")
        ax.set_yticks(y, labels)
        ax.invert_yaxis()
        ax.set_xlabel(label)
        ax.grid(axis="x", alpha=.2)
    axes[1].legend(frameon=False, fontsize=8)
    fig.tight_layout()
    save("13_hardware_peaks")


def main():
    FIG.mkdir(exist_ok=True)
    GENERATED.mkdir(exist_ok=True)
    data = json.loads(RESULTS.read_text())
    warm = json.loads(WARM.read_text())
    tasks = data["tasks"]
    assert len(tasks) == 15 and data["summary"]["both_proved_pairs"] == 15
    assert [t["task_id"] for t in tasks] == json.loads(
        (ROOT / "paper_bencmark/formalization_benchmark/design33/CORPUS_15.json").read_text()
    )["scheduled_order"]
    warm_seconds = warm["scout_wall_seconds"]
    usage = warm["scout_usage"]
    warm_tokens = usage["input_tokens"] - usage["cached_input_tokens"] + usage["output_tokens"]
    pairbars(tasks, "total_seconds_inclusive", "Total time, excluding one-time warm-up",
             "Contestant-active seconds", "01_total_time_ex_warm")
    pairbars(tasks, "total_seconds_inclusive", "Total time, warm-up amortized over 15 tasks",
             "Contestant-active seconds + 12.22 s/task for L", "02_total_time_in_warm",
             warm_add=warm_seconds / 15)
    phases(tasks, "seconds", "03_phase_times")
    pairbars(tasks, "total_tokens_net_new", "Total net-new tokens, excluding warm-up",
             "Net-new tokens (thousands)", "04_total_tokens_ex_warm", scale=1000)
    pairbars(tasks, "total_tokens_net_new", "Total net-new tokens, warm-up amortized",
             "Net-new tokens (thousands) + 5.90k/task for L", "05_total_tokens_in_warm",
             warm_add=warm_tokens / 15000, scale=1000)
    phases(tasks, "tokens", "06_phase_tokens")
    averages(tasks, warm_seconds, warm_tokens)
    labels = [short(t["task_id"]) for t in tasks]
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 7.3), sharey=True)
    for ax, key, title in zip(axes, ["statement_code_lines", "proof_code_lines"],
                              ["Statement", "Proof"]):
        y = np.arange(15)
        ax.barh(y-.19, [t["N"][key] for t in tasks], .37, color=BLUE, label="N")
        ax.barh(y+.19, [t["L"][key] for t in tasks], .37, color=ORANGE, label="L")
        ax.set_yticks(y, labels)
        ax.invert_yaxis()
        ax.set_xlabel("Nonblank, noncomment Lean lines")
        ax.set_title(title, fontweight="bold")
        ax.grid(axis="x", alpha=.2)
    axes[1].legend(frameon=False)
    fig.tight_layout()
    save("08_code_lines")
    rows = declaration_scan(tasks)
    coverage_heatmap(rows)
    scatter_overlap(rows)
    groups(tasks)
    overlap_by_selection(tasks, rows)
    amortization(tasks, warm_seconds, warm_tokens)
    hardware(tasks)
    with (GENERATED / "task_metrics.csv").open("w", newline="") as f:
        fieldnames = ["task_id", "source_cluster", "retained", "difficulty"] + [
            f"{c}_{key}" for c in ("N", "L") for key in (
                "formalization_seconds_inclusive", "proof_seconds_inclusive",
                "total_seconds_inclusive", "formalization_tokens_net_new",
                "proof_tokens_net_new", "total_tokens_net_new",
                "statement_code_lines", "proof_code_lines",
                "formalization_submissions", "proof_submissions")]
        w = csv.DictWriter(f, fieldnames=fieldnames, lineterminator="\n")
        w.writeheader()
        for t in tasks:
            row = {"task_id": t["task_id"], "source_cluster": t["source_cluster"],
                   "retained": t["outcome_aware_retained"],
                   "difficulty": t["difficulty_predeclared"]}
            for c in ("N", "L"):
                for key in fieldnames[4:]:
                    if key.startswith(c + "_"):
                        row[key] = t[c][key[2:]]
            w.writerow(row)
    (GENERATED / "declaration_scan.json").write_text(json.dumps(rows, indent=2) + "\n")
    def esc(value):
        return str(value).replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("%", r"\%")

    with (GENERATED / "task_times_table.tex").open("w") as f:
        for t in tasks:
            n, l = t["N"], t["L"]
            cols = [esc(t["task_id"]),
                    f'{n["formalization_seconds_inclusive"]:.0f}', f'{l["formalization_seconds_inclusive"]:.0f}',
                    f'{n["proof_seconds_inclusive"]:.0f}', f'{l["proof_seconds_inclusive"]:.0f}',
                    f'{n["total_seconds_inclusive"]:.0f}', f'{l["total_seconds_inclusive"]:.0f}',
                    f'{n["total_tokens_net_new"]/1000:.0f}', f'{l["total_tokens_net_new"]/1000:.0f}']
            f.write(" & ".join(cols) + r" \\" + "\n")
    with (GENERATED / "task_code_table.tex").open("w") as f:
        for t, r in zip(tasks, rows):
            n, l = t["N"], t["L"]
            cols = [esc(t["task_id"]), t["source_cluster"],
                    "yes" if t["outcome_aware_retained"] else "no",
                    str(n["statement_code_lines"]), str(l["statement_code_lines"]),
                    str(n["proof_code_lines"]), str(l["proof_code_lines"]),
                    str(r["substantive_statement_count"]), str(r["proof_count"]),
                    str(l["formalization_submissions"]), str(l["proof_submissions"])]
            f.write(" & ".join(cols) + r" \\" + "\n")
    with (GENERATED / "declaration_table.tex").open("w") as f:
        for r in rows:
            substantive = r["substantive_statement_names"]
            proof = r["proof_names"]
            # Readable family index only. Exact declarations are in the JSON.
            def families(xs):
                rules = [("fl_dotProduct", "dot product"),
                         ("fl_recursiveSum", "recursive sum"),
                         ("SumTree", "sum tree"),
                         ("FloatingPointFormat", "finite FP format"),
                         ("LSNormwiseBackwardError", "LS backward error"),
                         ("infNormVec", "infinity norm"),
                         ("sumSuffix", "suffix error"),
                         ("gamma", "gamma bounds"),
                         ("prod_error_bound", "product error")]
                labels = [label for pattern, label in rules if any(pattern in x for x in xs)]
                if not labels and xs:
                    return "other NumStability"
                return ", ".join(labels[:3]) if labels else "none"
            cols = [esc(r["task_id"]), families(substantive), str(len(substantive)),
                    families(proof), str(len(proof))]
            f.write(" & ".join(cols) + r" \\" + "\n")
    stats = {
        "source_results_sha256": sha(RESULTS),
        "source_warm_root_sha256": sha(WARM),
        "warm_seconds": warm_seconds,
        "warm_net_new_tokens": warm_tokens,
        "warm_total_tokens_including_cached": usage["total_tokens"],
        "tasks": len(tasks),
        "source_cluster_counts": data["summary"]["source_cluster_counts"],
        "sums": {key: {c: sum(t[c][key] for t in tasks) for c in ("N", "L")}
                 for key in ("formalization_seconds_inclusive", "proof_seconds_inclusive",
                             "total_seconds_inclusive", "formalization_tokens_net_new",
                             "proof_tokens_net_new", "total_tokens_net_new",
                             "statement_code_lines", "proof_code_lines")},
        "correlations": {},
    }
    for outcome in ("time_gain_pct", "token_gain_pct", "proof_line_gain_pct"):
        rho, p = spearmanr([r["proof_count"] for r in rows], [r[outcome] for r in rows])
        stats["correlations"][outcome] = {"rho": float(rho), "p_exploratory": float(p)}
    (GENERATED / "summary.json").write_text(json.dumps(stats, indent=2) + "\n")
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
