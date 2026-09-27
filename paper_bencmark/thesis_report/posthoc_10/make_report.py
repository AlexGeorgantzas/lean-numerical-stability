#!/usr/bin/env python3
"""Reproduce the explicitly post-hoc ten-task sensitivity analysis.

This filters the already sealed 15-task result. It never changes or reruns a
benchmark attempt. Positive gain means that L used less of the given metric.
"""

from __future__ import annotations

import csv
import hashlib
import json
from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
GENERATED = HERE / "generated"
FIGURES = HERE / "figures"
METRICS = PARENT / "generated/task_metrics.csv"
REUSE = PARENT / "generated/realized_reuse.csv"
PRIMARY = PARENT / "generated/summary.json"

# Chosen by the user after inspecting the fifteen-task results, 2026-09-28.
EXCLUDED = (
    "HI21-EQ2.7",
    "P14-SHIFTED-SUM",
    "P14-ALT-SOFTMAX",
    "P14-SHIFTED-LOG",
    "P14-SHIFTED-WEIGHTED",
)

BLUE = "#24547a"
ORANGE = "#d27834"
RED = "#b94b55"
GRAY = "#78828c"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nvalue(row: dict, condition: str, metric: str) -> float:
    return float(row[f"{condition}_{metric}"])


def totals(rows: list[dict], metric: str) -> tuple[float, float]:
    return (sum(nvalue(row, "N", metric) for row in rows),
            sum(nvalue(row, "L", metric) for row in rows))


def gain(n: float, l: float) -> float:
    return 100 * (n - l) / n


def group_gain(rows: list[dict], metric: str) -> float:
    return gain(*totals(rows, metric))


def tex_label(task_id: str) -> str:
    return task_id


def make_task_plot(selected: list[dict], scores: dict[str, int]) -> None:
    labels = [f"{row['task_id'].replace('P14-SHIFTED-', 'P14-S-')}  (R={scores[row['task_id']]}/3)"
              for row in selected]
    fig, axes = plt.subplots(1, 2, figsize=(10.8, 5.1), sharey=True)
    for ax, metric, title in zip(
            axes,
            ("total_seconds_inclusive", "proof_code_lines"),
            ("Total active time", "Proof-code lines")):
        vals = [gain(nvalue(row, "N", metric), nvalue(row, "L", metric))
                for row in selected]
        colors = [ORANGE if row["retained"] == "True" else BLUE for row in selected]
        y = np.arange(len(selected))
        ax.barh(y, vals, color=colors, height=.68)
        ax.set_yticks(y, labels, fontsize=8.3)
        ax.invert_yaxis()
        ax.axvline(0, color="#303b45", linewidth=.8)
        ax.set_xlim(-58, 70)
        ax.grid(axis="x", alpha=.16)
        ax.set_axisbelow(True)
        ax.set_title(title, fontweight="bold")
        ax.set_xlabel("N-to-L gain (%); positive favors L")
        for yy, value in zip(y, vals):
            ax.text(value + (1.2 if value >= 0 else -1.2), yy,
                    f"{value:+.0f}%", va="center",
                    ha="left" if value >= 0 else "right", fontsize=7.5)
    fig.text(.54, .01, "Orange: five previously favorable retained tasks; blue: five newly screened tasks.",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .045, 1, 1))
    fig.savefig(FIGURES / "ten_task_gains.pdf", bbox_inches="tight", pad_inches=.12)
    plt.close(fig)


def make_selection_plot(all_rows: list[dict], selected: list[dict],
                        scores: dict[str, int]) -> None:
    selected_ids = {row["task_id"] for row in selected}
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.05))
    for ax, metric, title in zip(
            axes,
            ("total_seconds_inclusive", "proof_code_lines"),
            ("Total active time", "Proof-code lines")):
        for row in all_rows:
            task = row["task_id"]
            value = gain(nvalue(row, "N", metric), nvalue(row, "L", metric))
            score = scores[task]
            if task not in selected_ids:
                marker, color, size, alpha = "x", GRAY, 55, .80
            elif row["retained"] == "True":
                marker, color, size, alpha = "o", ORANGE, 105, 1
            else:
                marker, color, size, alpha = "D", BLUE, 90, 1
            # Deterministic visual jitter separates integer-score ties only.
            jitter = (int(sha_text(task)[:4], 16) / 65535 - .5) * .23
            ax.scatter(score + jitter, value, s=size, marker=marker,
                       color=color, alpha=alpha, zorder=3)
            if task in selected_ids:
                ax.text(score + jitter, value, str(score), color="white",
                        ha="center", va="center", fontsize=7, fontweight="bold", zorder=4)
        ax.axhline(0, color="#303b45", linewidth=.8)
        ax.set_xlim(-.35, 3.35)
        ax.set_xticks(range(4))
        ax.set_xlabel("Realized reuse score (0-3)")
        ax.set_ylabel("N-to-L gain (%); positive favors L")
        ax.set_title(title, fontweight="bold")
        ax.grid(alpha=.17)
        ax.set_axisbelow(True)
    from matplotlib.lines import Line2D
    handles = [Line2D([], [], marker="o", linestyle="", color=ORANGE,
                      label="Selected: prior favorable"),
               Line2D([], [], marker="D", linestyle="", color=BLUE,
                      label="Selected: newly screened"),
               Line2D([], [], marker="x", linestyle="", color=GRAY,
                      label="Excluded after results")]
    fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, fontsize=8)
    fig.tight_layout(rect=(0, .12, 1, 1))
    fig.savefig(FIGURES / "selection_map.pdf", bbox_inches="tight", pad_inches=.12)
    plt.close(fig)


def sha_text(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def main() -> None:
    GENERATED.mkdir(exist_ok=True)
    FIGURES.mkdir(exist_ok=True)
    all_rows = list(csv.DictReader(METRICS.open()))
    reuse_rows = list(csv.DictReader(REUSE.open()))
    scores = {row["task_id"]: int(row["score"]) for row in reuse_rows}
    assert len(all_rows) == len(reuse_rows) == len(scores) == 15
    assert len(set(EXCLUDED)) == 5
    assert set(EXCLUDED) <= {row["task_id"] for row in all_rows}
    assert set(scores) == {row["task_id"] for row in all_rows}
    selected = [row for row in all_rows if row["task_id"] not in EXCLUDED]
    excluded = [row for row in all_rows if row["task_id"] in EXCLUDED]
    assert len(selected) == 10 and len(excluded) == 5
    assert Counter(row["retained"] for row in selected) == {"True": 5, "False": 5}
    warm = json.loads(PRIMARY.read_text())

    metrics = ("formalization_seconds_inclusive", "proof_seconds_inclusive",
               "total_seconds_inclusive", "formalization_tokens_net_new",
               "proof_tokens_net_new", "total_tokens_net_new",
               "statement_code_lines", "proof_code_lines")
    summary = {
        "status": "POST_HOC_OUTCOME_SELECTED_EXPLORATORY_NOT_HELD_OUT",
        "selection_date": "2026-09-28",
        "excluded_task_ids": list(EXCLUDED),
        "selected_task_ids": [row["task_id"] for row in selected],
        "source_sha256": {"task_metrics.csv": sha(METRICS),
                          "realized_reuse.csv": sha(REUSE),
                          "primary_summary.json": sha(PRIMARY)},
        "groups": {},
        "one_time_L_warm_seconds": warm["warm_seconds"],
        "one_time_L_warm_net_new_tokens": warm["warm_net_new_tokens"],
    }
    groups = {"all_15": all_rows, "selected_10": selected,
              "selected_prior_favorable_5": [r for r in selected if r["retained"] == "True"],
              "selected_new_5": [r for r in selected if r["retained"] == "False"],
              "excluded_5": excluded}
    groups.update({f"selected_score_{score}":
                   [r for r in selected if scores[r["task_id"]] == score]
                   for score in range(4)})
    for name, rows in groups.items():
        summary["groups"][name] = {
            "n": len(rows),
            "task_ids": [row["task_id"] for row in rows],
            "metrics": {metric: {"N": totals(rows, metric)[0],
                                 "L": totals(rows, metric)[1],
                                 "gain_pct": group_gain(rows, metric)}
                        for metric in metrics if rows},
        }
    n_time, l_time = totals(selected, "total_seconds_inclusive")
    n_tokens, l_tokens = totals(selected, "total_tokens_net_new")
    summary["selected_10_with_one_time_L_warm"] = {
        "total_seconds_N": n_time,
        "total_seconds_L": l_time + warm["warm_seconds"],
        "time_gain_pct": gain(n_time, l_time + warm["warm_seconds"]),
        "net_new_tokens_N": n_tokens,
        "net_new_tokens_L": l_tokens + warm["warm_net_new_tokens"],
        "token_gain_pct": gain(n_tokens, l_tokens + warm["warm_net_new_tokens"]),
    }
    (GENERATED / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    with (GENERATED / "ten_task_table.tex").open("w") as out:
        for row in selected:
            task = tex_label(row["task_id"])
            score = scores[row["task_id"]]
            tg = gain(nvalue(row, "N", "total_seconds_inclusive"),
                      nvalue(row, "L", "total_seconds_inclusive"))
            lg = gain(nvalue(row, "N", "proof_code_lines"),
                      nvalue(row, "L", "proof_code_lines"))
            out.write(f"\\texttt{{{task}}} & {score}/3 & "
                      f"{'prior' if row['retained'] == 'True' else 'new'} & "
                      f"{tg:+.1f} & {lg:+.1f} \\\\\n")
        out.write("\\bottomrule\n")
    with (GENERATED / "score_table.tex").open("w") as out:
        for score in (1, 2, 3):
            rows = groups[f"selected_score_{score}"]
            out.write(f"{score}/3 & {len(rows)} & "
                      f"{group_gain(rows, 'total_seconds_inclusive'):+.1f} & "
                      f"{group_gain(rows, 'proof_code_lines'):+.1f} & "
                      f"{group_gain(rows, 'total_tokens_net_new'):+.1f} \\\\\n")
        out.write("\\bottomrule\n")
    with (GENERATED / "excluded_table.tex").open("w") as out:
        for row in excluded:
            tg = gain(nvalue(row, "N", "total_seconds_inclusive"),
                      nvalue(row, "L", "total_seconds_inclusive"))
            lg = gain(nvalue(row, "N", "proof_code_lines"),
                      nvalue(row, "L", "proof_code_lines"))
            out.write(f"\\texttt{{{tex_label(row['task_id'])}}} & "
                      f"{scores[row['task_id']]}/3 & {tg:+.1f} & {lg:+.1f} \\\\\n")
        out.write("\\bottomrule\n")
    make_task_plot(selected, scores)
    make_selection_plot(all_rows, selected, scores)
    print("PASS: original 15 preserved; user-specified five excluded only in derived ten-task report")
    print("Selected ten: time gain %.2f%%, proof-line gain %.2f%%; with warm time gain %.2f%%"
          % (group_gain(selected, "total_seconds_inclusive"),
             group_gain(selected, "proof_code_lines"),
             summary["selected_10_with_one_time_L_warm"]["time_gain_pct"]))


if __name__ == "__main__":
    main()
