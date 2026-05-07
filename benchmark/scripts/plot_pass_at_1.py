#!/usr/bin/env python3
"""Plot benchmark pass@1 results from archived metrics.tsv files."""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.patches import Patch


DEFAULT_TASKS = [
    "T01_ScaledDot",
    "T02_ShiftedDot",
    "T03_ResidualCertificate",
    "T04_ForwardSubResidual",
    "T05_Gemv",
    "T06_TriangularSolveSingle",
    "T07_LUSolveGrowth",
    "T08_CholeskySolveGrowth",
    "T09_OneStepRefinement",
    "T10_StationaryForwardSub",
]

DEFAULT_TASK_LABELS = {
    "T01_ScaledDot": "T01\nScaled Dot",
    "T02_ShiftedDot": "T02\nShifted Dot",
    "T03_ResidualCertificate": "T03\nResidual Cert.",
    "T04_ForwardSubResidual": "T04\nTri. Residual",
    "T05_Gemv": "T05\nGEMV",
    "T06_TriangularSolveSingle": "T06\nTri. Solve",
    "T07_LUSolveGrowth": "T07\nLU Growth",
    "T08_CholeskySolveGrowth": "T08\nChol. Growth",
    "T09_OneStepRefinement": "T09\nRefinement",
    "T10_StationaryForwardSub": "T10\nStationary",
}

CONDITION_LABELS = {
    "condition_a": "Condition A",
    "condition_c": "Condition C",
}


@dataclass(frozen=True)
class Metric:
    task: str
    run: str
    condition: str
    codex_exit: int | None
    validation_exit: int | None
    timeout: str
    started_at_utc: str
    finished_at_utc: str
    codex_event_lines: int
    diff_lines: int
    proof_lines: int
    placeholder_count: int
    forbidden_decl_count: int

    @property
    def passed(self) -> bool:
        return self.validation_exit == 0

    @property
    def elapsed_minutes(self) -> float:
        fmt = "%Y-%m-%dT%H:%M:%SZ"
        try:
            start = datetime.strptime(self.started_at_utc, fmt)
            finish = datetime.strptime(self.finished_at_utc, fmt)
        except ValueError:
            return 0.0
        return max(0.0, (finish - start).total_seconds() / 60.0)


def parse_int(value: str) -> int | None:
    try:
        return int(value)
    except ValueError:
        return None


def select_run(task_dir: Path, date_prefix: str | None) -> Path:
    candidates = [p for p in task_dir.iterdir() if p.is_dir()]
    if date_prefix:
        candidates = [p for p in candidates if p.name.startswith(date_prefix)]
    candidates = [p for p in candidates if (p / "metrics.tsv").is_file()]
    if not candidates:
        raise FileNotFoundError(f"no metrics.tsv run found for {task_dir.name}")
    return sorted(candidates, key=lambda p: p.name)[-1]


def generated_label(task: str) -> str:
    if "_" not in task:
        return task
    prefix, rest = task.split("_", 1)
    words = rest.replace("_", " ")
    return f"{prefix}\n{words}"


def read_task_list(path: Path) -> tuple[list[str], dict[str, str]]:
    tasks: list[str] = []
    labels: dict[str, str] = {}
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t")
            task = parts[0].strip()
            if not task or task == "task":
                continue
            label = parts[1].strip().replace("\\n", "\n") if len(parts) > 1 else generated_label(task)
            tasks.append(task)
            labels[task] = label
    if not tasks:
        raise ValueError(f"no tasks found in {path}")
    return tasks, labels


def task_config(args: argparse.Namespace) -> tuple[list[str], dict[str, str]]:
    if args.task_list:
        return read_task_list(Path(args.task_list))
    if args.tasks:
        tasks = [task.strip() for task in args.tasks.split(",") if task.strip()]
        if not tasks:
            raise ValueError("--tasks did not contain any task names")
        return tasks, {task: generated_label(task) for task in tasks}
    return DEFAULT_TASKS, DEFAULT_TASK_LABELS


def read_metrics(results_root: Path, date_prefix: str | None, tasks: list[str]) -> list[Metric]:
    rows: list[Metric] = []
    for task in tasks:
        run_dir = select_run(results_root / task, date_prefix)
        with (run_dir / "metrics.tsv").open(newline="") as f:
            reader = csv.DictReader(f, delimiter="\t")
            for row in reader:
                rows.append(
                    Metric(
                        task=task,
                        run=run_dir.name,
                        condition=row["condition"],
                        codex_exit=parse_int(row["codex_exit"]),
                        validation_exit=parse_int(row["validation_exit"]),
                        timeout=row["timeout"],
                        started_at_utc=row["started_at_utc"],
                        finished_at_utc=row["finished_at_utc"],
                        codex_event_lines=int(row["codex_event_lines"]),
                        diff_lines=int(row["diff_lines"]),
                        proof_lines=int(row["proof_lines"]),
                        placeholder_count=int(row["placeholder_count"]),
                        forbidden_decl_count=int(row["forbidden_decl_count"]),
                    )
                )
    return rows


def write_aggregate(rows: list[Metric], output_dir: Path) -> None:
    with (output_dir / "aggregate_metrics.tsv").open("w", newline="") as f:
        writer = csv.writer(f, delimiter="\t")
        writer.writerow(
            [
                "task",
                "run",
                "condition",
                "codex_exit",
                "validation_exit",
                "passed",
                "timeout",
                "elapsed_minutes",
                "codex_event_lines",
                "diff_lines",
                "proof_lines",
                "placeholder_count",
                "forbidden_decl_count",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.task,
                    row.run,
                    row.condition,
                    row.codex_exit,
                    row.validation_exit,
                    int(row.passed),
                    row.timeout,
                    f"{row.elapsed_minutes:.2f}",
                    row.codex_event_lines,
                    row.diff_lines,
                    row.proof_lines,
                    row.placeholder_count,
                    row.forbidden_decl_count,
                ]
            )


def save_plot(fig: plt.Figure, output_dir: Path, stem: str) -> None:
    fig.savefig(output_dir / f"{stem}.png", dpi=220, bbox_inches="tight")
    fig.savefig(output_dir / f"{stem}.pdf", bbox_inches="tight")
    plt.close(fig)


def plot_pass_matrix(
    rows: list[Metric],
    output_dir: Path,
    tasks: list[str],
    task_labels: dict[str, str],
) -> None:
    by_key = {(row.task, row.condition): row for row in rows}
    fig, ax = plt.subplots(figsize=(12, 3.8))
    colors = {True: "#2e7d32", False: "#c62828"}

    for y, condition in enumerate(["condition_a", "condition_c"]):
        for x, task in enumerate(tasks):
            row = by_key[(task, condition)]
            ax.barh(y, 0.86, left=x - 0.43, height=0.62, color=colors[row.passed])
            ax.text(
                x,
                y,
                "PASS" if row.passed else "FAIL",
                ha="center",
                va="center",
                color="white",
                fontsize=9,
                fontweight="bold",
            )

    ax.set_yticks([0, 1], [CONDITION_LABELS["condition_a"], CONDITION_LABELS["condition_c"]])
    ax.set_xticks(range(len(tasks)), [task_labels.get(t, generated_label(t)) for t in tasks], fontsize=8)
    ax.set_xlim(-0.55, len(tasks) - 0.45)
    ax.set_xlabel("Predefined task order")
    ax.set_title("Pass@1 Validation Outcome")
    ax.legend(
        handles=[Patch(color=colors[True], label="Pass"), Patch(color=colors[False], label="Fail")],
        loc="upper center",
        bbox_to_anchor=(0.5, -0.18),
        ncols=2,
        frameon=False,
    )
    ax.spines[["top", "right", "left", "bottom"]].set_visible(False)
    ax.tick_params(axis="both", length=0)
    save_plot(fig, output_dir, "pass_matrix")


def plot_grouped_bars(
    rows: list[Metric],
    output_dir: Path,
    tasks: list[str],
    task_labels: dict[str, str],
    stem: str,
    title: str,
    ylabel: str,
    value_fn,
) -> None:
    by_key = {(row.task, row.condition): row for row in rows}
    xs = list(range(len(tasks)))
    width = 0.36
    a_values = [value_fn(by_key[(task, "condition_a")]) for task in tasks]
    c_values = [value_fn(by_key[(task, "condition_c")]) for task in tasks]

    fig, ax = plt.subplots(figsize=(12, 4.4))
    ax.bar([x - width / 2 for x in xs], a_values, width, label="Condition A", color="#7b8da6")
    ax.bar([x + width / 2 for x in xs], c_values, width, label="Condition C", color="#2f6f9f")
    ax.set_xticks(xs, [task_labels.get(t, generated_label(t)) for t in tasks], fontsize=8)
    ax.set_xlabel("Predefined task order")
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    ax.legend(frameon=False)
    ax.grid(axis="y", color="#d9d9d9", linewidth=0.8)
    ax.set_axisbelow(True)
    ax.spines[["top", "right"]].set_visible(False)
    save_plot(fig, output_dir, stem)


def plot_elapsed(
    rows: list[Metric],
    output_dir: Path,
    tasks: list[str],
    task_labels: dict[str, str],
) -> None:
    plot_grouped_bars(
        rows,
        output_dir,
        tasks,
        task_labels,
        "elapsed_minutes",
        "Solver Attempt Duration",
        "minutes",
        lambda row: row.elapsed_minutes,
    )


def plot_proof_lines(
    rows: list[Metric],
    output_dir: Path,
    tasks: list[str],
    task_labels: dict[str, str],
) -> None:
    plot_grouped_bars(
        rows,
        output_dir,
        tasks,
        task_labels,
        "proof_lines",
        "Proof Body Lines in Final Attempt",
        "lines",
        lambda row: row.proof_lines,
    )


def plot_event_lines(
    rows: list[Metric],
    output_dir: Path,
    tasks: list[str],
    task_labels: dict[str, str],
) -> None:
    plot_grouped_bars(
        rows,
        output_dir,
        tasks,
        task_labels,
        "codex_event_lines",
        "Codex Event Log Lines",
        "JSONL lines",
        lambda row: row.codex_event_lines,
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results-root", default="benchmark/results")
    parser.add_argument("--date-prefix", default="20260505")
    parser.add_argument("--output-dir", default="benchmark/results/plots/pass_at_1_20260505")
    parser.add_argument("--task-list", help="TSV file with task and optional label columns")
    parser.add_argument("--tasks", help="Comma-separated task names; overrides the default T-suite")
    args = parser.parse_args()

    results_root = Path(args.results_root)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    tasks, task_labels = task_config(args)
    rows = read_metrics(results_root, args.date_prefix, tasks)
    write_aggregate(rows, output_dir)
    plot_pass_matrix(rows, output_dir, tasks, task_labels)
    plot_elapsed(rows, output_dir, tasks, task_labels)
    plot_proof_lines(rows, output_dir, tasks, task_labels)
    plot_event_lines(rows, output_dir, tasks, task_labels)

    print(f"wrote plots to {output_dir}")


if __name__ == "__main__":
    main()
