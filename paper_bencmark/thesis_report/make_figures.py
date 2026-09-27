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
REUSE_OBLIGATIONS = HERE / "reuse_obligations.json"
FIG = HERE / "figures"
GENERATED = HERE / "generated"
BLUE = "#24547a"
ORANGE = "#d27834"
GREEN = "#267e67"
RED = "#b94b55"
GRAY = "#59636e"
SCORE_BY_TASK = {}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name: str) -> None:
    plt.savefig(FIG / f"{name}.pdf", bbox_inches="tight", pad_inches=0.12)
    plt.close()


def short(s: str, with_score: bool = True) -> str:
    label = s.replace("P14-SHIFTED-", "P14-S-")
    if with_score:
        assert s in SCORE_BY_TASK, s
        label += f" (R={SCORE_BY_TASK[s]}/3)"
    return label


def score_distribution(tasks) -> str:
    counts = {score: sum(SCORE_BY_TASK[t["task_id"]] == score for t in tasks)
              for score in range(4)}
    return "Reuse scores: " + ", ".join(f"{score}/3 x {counts[score]}" for score in range(4))


def add_score_distribution(fig, tasks, bottom: float = .035) -> None:
    fig.text(.5, bottom, score_distribution(tasks), ha="center", va="bottom", fontsize=8)


def add_task_score_key(fig) -> None:
    fig.text(.5, .012, "Task label (R=x/3): realized NumStability reuse score",
             ha="center", va="bottom", fontsize=8)


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
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
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
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
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
    add_score_distribution(fig, tasks)
    fig.tight_layout(rect=(0, .07, 1, 1))
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


def realized_reuse(tasks, declaration_rows):
    """Score direct, task-relevant L reuse using the published post-run rubric.

    This is deliberately an ordinal breadth score, not a count of imported or
    transitively reached declarations, nor a causal/pre-run coverage measure.
    """
    rubric = json.loads(REUSE_OBLIGATIONS.read_text())
    roles = ("foundation", "computation", "analysis")
    assert rubric["schema_version"] == "realized-reuse-obligations-1"
    assert set(rubric["tasks"]) == {t["task_id"] for t in tasks}
    admission = json.loads((ROOT / "paper_bencmark/formalization_benchmark/design33/ADMISSION_15.json").read_text())
    scored = []
    for task, scan in zip(tasks, declaration_rows):
        task_id = task["task_id"]
        assert scan["task_id"] == task_id
        packet = ROOT / f"paper_bencmark/formalization_benchmark/design33/packets/{task_id}.json"
        assert sha(packet) == admission["tasks"][task_id]["source_packet_sha256"]
        spec = rubric["tasks"][task_id]
        assert set(spec) == set(roles)
        statement = set(scan["statement_names"])
        proof = set(scan["proof_names"])
        covered = {}
        for role in roles:
            entry = spec[role]
            assert entry["obligation"] and isinstance(entry["witnesses"], list)
            witnesses = entry["witnesses"]
            assert len(witnesses) == len(set(witnesses))
            assert all(name.startswith("NumStability.") for name in witnesses)
            assert all(name in statement | proof for name in witnesses), (task_id, role)
            if role == "analysis":
                assert all(name in proof for name in witnesses), task_id
            covered[role] = {
                "source_obligation": entry["obligation"],
                "witnesses": witnesses,
                "statement_witnesses": [name for name in witnesses if name in statement],
                "proof_witnesses": [name for name in witnesses if name in proof],
                "used": bool(witnesses),
            }
        n, l = task["N"], task["L"]
        gains = {}
        for label, key in (
            ("formalization_time", "formalization_seconds_inclusive"),
            ("proof_time", "proof_seconds_inclusive"),
            ("total_time", "total_seconds_inclusive"),
            ("formalization_tokens", "formalization_tokens_net_new"),
            ("proof_tokens", "proof_tokens_net_new"),
            ("total_tokens", "total_tokens_net_new"),
            ("statement_lines", "statement_code_lines"),
            ("proof_lines", "proof_code_lines"),
        ):
            gains[f"{label}_gain_pct"] = 100 * (n[key] - l[key]) / n[key]
        scored.append({
            "task_id": task_id,
            "source_cluster": task["source_cluster"],
            "outcome_aware_retained": bool(task["outcome_aware_retained"]),
            "source_packet_sha256": sha(packet),
            "score": sum(covered[role]["used"] for role in roles),
            "statement_roles": sum(bool(covered[role]["statement_witnesses"]) for role in roles),
            "proof_roles": sum(bool(covered[role]["proof_witnesses"]) for role in roles),
            "direct_proof_declaration_count": scan["proof_count"],
            "roles": covered,
            "gains": gains,
        })
    return rubric, scored


def reuse_summary(tasks, scored):
    def group(indices):
        ts = [tasks[i] for i in indices]
        out = {"n": len(ts), "retained_n": sum(t["outcome_aware_retained"] for t in ts)}
        for label, key in (("proof_lines", "proof_code_lines"),
                           ("proof_time", "proof_seconds_inclusive"),
                           ("formalization_time", "formalization_seconds_inclusive"),
                           ("total_time", "total_seconds_inclusive"),
                           ("total_tokens", "total_tokens_net_new")):
            n = sum(t["N"][key] for t in ts)
            l = sum(t["L"][key] for t in ts)
            out[f"{label}_N_sum"] = n
            out[f"{label}_L_sum"] = l
            out[f"{label}_aggregate_gain_pct"] = 100 * (n - l) / n if n else None
        return out
    groups = {}
    for selection, allowed in (("all", lambda r: True),
                               ("new_only", lambda r: not r["outcome_aware_retained"])):
        groups[selection] = {}
        for bucket, filt in ((str(score), lambda s, score=score: s == score)
                             for score in range(4)):
            indices = [i for i, r in enumerate(scored) if allowed(r) and filt(r["score"])]
            groups[selection][bucket] = group(indices)
    correlations = {}
    for selection, allowed in (("all", lambda r: True),
                               ("new_only", lambda r: not r["outcome_aware_retained"])):
        rows = [r for r in scored if allowed(r)]
        correlations[selection] = {}
        for label in ("proof_lines", "proof_time", "formalization_time", "total_time", "total_tokens"):
            rho, p = spearmanr([r["score"] for r in rows],
                               [r["gains"][f"{label}_gain_pct"] for r in rows])
            correlations[selection][label] = {"rho": float(rho), "p_exploratory": float(p), "n": len(rows)}
    return {"group_aggregates": groups, "rank_associations": correlations}


def reuse_scatter(scored, summary):
    panels = (("proof_lines", "Proof-code gain (%)"),
              ("proof_time", "Proof-time gain (%)"),
              ("total_time", "Total active-time gain (%)"),
              ("total_tokens", "Net-new-token gain (%)"))
    fig, axes = plt.subplots(2, 2, figsize=(10.2, 7.6), sharex=True)
    for ax, (key, ylabel) in zip(axes.flat, panels):
        for retained, color, marker, label in ((False, BLUE, "D", "New screened"),
                                                (True, ORANGE, "o", "Prior favorable retained")):
            subset = [(i, r) for i, r in enumerate(scored) if r["outcome_aware_retained"] == retained]
            xs = [r["score"] + ((i % 5) - 2) * .045 for i, r in subset]
            ys = [r["gains"][f"{key}_gain_pct"] for _, r in subset]
            ax.scatter(xs, ys, s=105, color=color, marker=marker, label=label,
                       edgecolor="white", linewidth=.7, zorder=3)
            for x_value, y_value, (_, row) in zip(xs, ys, subset):
                ax.text(x_value, y_value, str(row["score"]), ha="center", va="center",
                        fontsize=6, color="white", fontweight="bold", zorder=4)
        ax.axhline(0, color=GRAY, linewidth=.8)
        ax.set_xticks([0, 1, 2, 3])
        ax.tick_params(axis="x", labelbottom=True)
        ax.set_xlim(-.3, 3.3)
        ax.set_xlabel("Realized reuse score (0-3)")
        ax.set_ylabel(ylabel)
        rho_all = summary["rank_associations"]["all"][key]["rho"]
        rho_new = summary["rank_associations"]["new_only"][key]["rho"]
        ax.text(.02, .98, f"Rank rho: all {rho_all:+.2f}; new {rho_new:+.2f}",
                transform=ax.transAxes, ha="left", va="top", fontsize=8,
                bbox=dict(facecolor="white", edgecolor="none", alpha=.85))
        ax.grid(alpha=.18)
    handles, labels = axes[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, .96))
    save("15_realized_reuse_scatter")


def reuse_strata(summary):
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.8))
    for ax, label, title in zip(axes, ("proof_lines", "total_time"),
                                ("Proof code", "Total active time")):
        buckets = ("0", "1", "2", "3")
        y = np.arange(len(buckets))
        all_values = []
        for selection, delta, color, name in (("all", -.18, BLUE, "All 15"),
                                               ("new_only", .18, ORANGE, "New screened 10")):
            subset = summary["group_aggregates"][selection]
            vals = [subset[b][f"{label}_aggregate_gain_pct"] for b in buckets]
            all_values.extend(vals)
            ax.barh(y + delta, vals, height=.33, color=color, label=name)
            for i, (b, v) in enumerate(zip(buckets, vals)):
                ax.text(v + (1 if v >= 0 else -1), i + delta,
                        f"{v:+.1f}% (n={subset[b]['n']})", va="center",
                        ha="left" if v >= 0 else "right", fontsize=8)
        ax.axvline(0, color=GRAY, linewidth=.8)
        ax.set_yticks(y, [f"Score {b}" for b in buckets])
        ax.invert_yaxis()
        ax.set_xlabel("Aggregate N-to-L gain (%)")
        ax.set_title(title, fontweight="bold")
        extent = max(abs(v) for v in all_values) + 35
        ax.set_xlim(-extent, extent)
        ax.grid(axis="x", alpha=.18)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False, fontsize=8)
    fig.tight_layout(rect=(0, 0, 1, .92), w_pad=3)
    save("16_realized_reuse_selection")


def coverage_heatmap(rows, scored):
    assert [r["task_id"] for r in rows] == [r["task_id"] for r in scored]
    binary = np.array([[r["substantive_statement_count"] > 0,
                        r["algorithm_statement"], r["proof_count"] > 0,
                        r["error_proof"]] for r in rows], dtype=float)
    scores = np.array([r["score"] for r in scored], dtype=int)
    gains = np.array([[r["formal_gain_pct"], r["proof_time_gain_pct"],
                       r["time_gain_pct"], r["token_gain_pct"],
                       r["proof_line_gain_pct"]] for r in rows])
    fig, (ax1, axscore, ax2) = plt.subplots(
        1, 3, figsize=(12.4, 7.5),
        gridspec_kw={"width_ratios": [4, 1.05, 5]}, sharey=True)
    ax1.imshow(binary, cmap=matplotlib.colors.ListedColormap(["#e7e9e9", GREEN]),
               vmin=0, vmax=1, aspect="auto")
    axscore.imshow(scores[:, None],
                   cmap=matplotlib.colors.ListedColormap(
                       ["#e7e9e9", "#b9d9d0", "#69ad98", GREEN]),
                   vmin=-.5, vmax=3.5, aspect="auto")
    im = ax2.imshow(gains, cmap="RdBu", vmin=-100, vmax=100, aspect="auto")
    ax1.set_yticks(range(len(rows)), [short(r["task_id"], with_score=False) for r in rows], fontsize=8)
    axscore.set_yticks(range(len(rows)))
    ax2.set_yticks(range(len(rows)))
    ax1.set_xticks(range(4), ["Substantive\nstatement", "Algorithm/format\nstatement",
                               "Any proof\nreach", "Error/bound\nproof"], fontsize=8)
    axscore.set_xticks([0], ["Reuse\nscore"], fontsize=8)
    ax2.set_xticks(range(5), ["Formal\ntime", "Proof\ntime", "Total\ntime",
                               "Total\ntokens", "Proof\nlines"], fontsize=8)
    for i in range(len(rows)):
        for j in range(4):
            ax1.text(j, i, "yes" if binary[i, j] else "--", ha="center", va="center",
                     color="white" if binary[i, j] else GRAY, fontsize=7)
        axscore.text(0, i, f"{scores[i]}/3", ha="center", va="center",
                     color="white" if scores[i] == 3 else "#17212b", fontsize=8,
                     fontweight="bold")
        for j in range(5):
            ax2.text(j, i, f"{gains[i,j]:+.0f}", ha="center", va="center", fontsize=7,
                     color="white" if abs(gains[i,j]) > 65 else "#17212b")
    for ax in (ax1, axscore, ax2):
        ax.tick_params(length=0)
        ax.set_xticks(np.arange(-.5, len(ax.get_xticks()), 1), minor=True)
        ax.set_yticks(np.arange(-.5, len(rows), 1), minor=True)
        ax.grid(which="minor", color="white", linewidth=2)
        ax.tick_params(which="minor", length=0)
    fig.colorbar(im, ax=ax2, shrink=.65, label="N-to-L gain (%); positive favors L")
    fig.tight_layout()
    save("09_coverage_heatmap")


def scatter_overlap(rows, tasks):
    x = np.array([r["proof_count"] for r in rows])
    ys = [("time_gain_pct", "Total time gain (%)"),
          ("token_gain_pct", "Net-new token gain (%)"),
          ("proof_line_gain_pct", "Proof-line gain (%)"),
          ("formal_gain_pct", "Formalization-time gain (%)")]
    fig, axes = plt.subplots(2, 2, figsize=(9.4, 7.3))
    for ax, (key, label) in zip(axes.flat, ys):
        y = np.array([r[key] for r in rows])
        colors = [ORANGE if r["retained"] else BLUE for r in rows]
        x_display = x.astype(float).copy()
        coincident = {}
        for i, pair in enumerate(zip(x, y)):
            coincident.setdefault(pair, []).append(i)
        for indices in coincident.values():
            for rank, index in enumerate(indices):
                x_display[index] += (rank - (len(indices) - 1) / 2) * .9
        ax.scatter(x_display, y, c=colors, s=100, edgecolor="white", linewidth=.7,
                   zorder=3)
        for x_value, y_value, row in zip(x_display, y, rows):
            ax.text(x_value, y_value, str(SCORE_BY_TASK[row["task_id"]]),
                    ha="center", va="center", color="white", fontsize=6,
                    fontweight="bold", zorder=4)
        ax.axhline(0, color=GRAY, linewidth=.8)
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
    add_score_distribution(fig, tasks)
    fig.tight_layout(rect=(0, .06, 1, .96))
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
    add_score_distribution(fig, tasks)
    fig.tight_layout(rect=(0, .07, 1, 1))
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
    for panel, (ax, key, title) in enumerate(zip(axes,
                              ["total_seconds_inclusive", "total_tokens_net_new", "proof_code_lines"],
                              ["Total active time", "Net-new tokens", "Proof code"])):
        vals = []
        for _, taskset in subsets:
            n = sum(t["N"][key] for t in taskset)
            l = sum(t["L"][key] for t in taskset)
            vals.append(100 * (n-l)/n)
        ax.barh(range(3), vals, color=[GREEN if v >= 0 else RED for v in vals])
        labels = [f"{name} (n={len(ts)})" for name, ts in subsets] if panel == 0 else [""] * 3
        ax.set_yticks(range(3), labels, fontsize=8)
        ax.invert_yaxis()
        ax.axvline(0, color=GRAY, linewidth=.8)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("Aggregate gain for L (%)")
        ax.set_xlim(-55, 55)
        for i, v in enumerate(vals):
            ax.text(v + (1 if v>=0 else -1), i, f"{v:+.1f}%", va="center",
                    ha="left" if v>=0 else "right", fontsize=8)
        ax.grid(axis="x", alpha=.2)
    profiles = []
    for name, taskset in subsets:
        counts = {score: sum(SCORE_BY_TASK[t["task_id"]] == score for t in taskset)
                  for score in range(4)}
        present = ",".join(f"{score}x{counts[score]}" for score in range(4) if counts[score])
        profiles.append(f"{name}: {present}")
    fig.text(.5, .012, "Reuse scores by row (each /3) - " + "; ".join(profiles),
             ha="center", va="bottom", fontsize=7)
    fig.tight_layout(rect=(0, .07, 1, 1))
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
    score_sequence = ", ".join(f"{SCORE_BY_TASK[t['task_id']]}/3" for t in tasks)
    fig.text(.5, .012, "Task reuse scores in plotted order: " + score_sequence,
             ha="center", va="bottom", fontsize=7)
    fig.tight_layout(rect=(0, .07, 1, 1))
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
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
    save("13_hardware_peaks")


def main():
    global SCORE_BY_TASK
    FIG.mkdir(exist_ok=True)
    GENERATED.mkdir(exist_ok=True)
    data = json.loads(RESULTS.read_text())
    warm = json.loads(WARM.read_text())
    tasks = data["tasks"]
    assert len(tasks) == 15 and data["summary"]["both_proved_pairs"] == 15
    assert [t["task_id"] for t in tasks] == json.loads(
        (ROOT / "paper_bencmark/formalization_benchmark/design33/CORPUS_15.json").read_text()
    )["scheduled_order"]
    rows = declaration_scan(tasks)
    reuse_rubric, reuse_rows = realized_reuse(tasks, rows)
    reuse_stats = reuse_summary(tasks, reuse_rows)
    SCORE_BY_TASK = {r["task_id"]: r["score"] for r in reuse_rows}
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
    add_task_score_key(fig)
    fig.tight_layout(rect=(0, .045, 1, 1))
    save("08_code_lines")
    coverage_heatmap(rows, reuse_rows)
    scatter_overlap(rows, tasks)
    reuse_scatter(reuse_rows, reuse_stats)
    reuse_strata(reuse_stats)
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
    (GENERATED / "realized_reuse.json").write_text(json.dumps({
        "scientific_status": reuse_rubric["scientific_status"],
        "rubric_sha256": sha(REUSE_OBLIGATIONS),
        "source_results_sha256": sha(RESULTS),
        "rows": reuse_rows,
        "summary": reuse_stats,
    }, indent=2) + "\n")
    with (GENERATED / "realized_reuse.csv").open("w", newline="") as f:
        columns = ["task_id", "source_cluster", "outcome_aware_retained", "score",
                   "foundation", "computation", "analysis", "statement_roles", "proof_roles",
                   "direct_proof_declaration_count", "proof_lines_gain_pct", "proof_time_gain_pct",
                   "formalization_time_gain_pct", "total_time_gain_pct", "total_tokens_gain_pct"]
        writer = csv.DictWriter(f, fieldnames=columns, lineterminator="\n")
        writer.writeheader()
        for r in reuse_rows:
            writer.writerow({
                **{key: r[key] for key in ("task_id", "source_cluster", "outcome_aware_retained",
                                            "score", "statement_roles", "proof_roles",
                                            "direct_proof_declaration_count")},
                **{role: int(r["roles"][role]["used"]) for role in
                   ("foundation", "computation", "analysis")},
                **{f"{label}_gain_pct": r["gains"][f"{label}_gain_pct"] for label in
                   ("proof_lines", "proof_time", "formalization_time", "total_time", "total_tokens")},
            })
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
    with (GENERATED / "realized_reuse_table.tex").open("w") as f:
        for r in reuse_rows:
            cols = [esc(r["task_id"]), str(r["score"]),
                    *["yes" if r["roles"][role]["used"] else "--" for role in
                      ("foundation", "computation", "analysis")],
                    f'{r["gains"]["proof_lines_gain_pct"]:+.0f}',
                    f'{r["gains"]["proof_time_gain_pct"]:+.0f}',
                    f'{r["gains"]["total_time_gain_pct"]:+.0f}',
                    f'{r["gains"]["total_tokens_gain_pct"]:+.0f}']
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
