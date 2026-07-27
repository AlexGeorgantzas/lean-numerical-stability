#!/usr/bin/env python3
"""Render the local HighamBench construction and validation report.

The renderer accepts only a complete offline validation matrix tied to the
current frozen benchmark.  It labels the local timings honestly and refuses to
turn them into agent-performance scores.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import statistics
import subprocess
import sys
from typing import Any, Iterable


BENCHMARK_ROOT = Path(__file__).resolve().parents[1]
if str(BENCHMARK_ROOT) not in sys.path:
    sys.path.insert(0, str(BENCHMARK_ROOT))

from tools.common import BenchmarkToolError, read_json, sha256_file  # noqa: E402
from tools.hashes import load_manifest, verify_manifest  # noqa: E402
from tools.run_matrix import environment_bundle_digest  # noqa: E402


EXPECTED_SCHEMA = "highambench-offline-validation-0.1"
EXPECTED_KIND = "offline-private-proof-validation-timing"


def esc(value: Any) -> str:
    """Escape plain text for LaTeX."""

    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def fmt_seconds(value: float | None) -> str:
    return "--" if value is None else f"{value:.2f}"


def short_hash(value: str) -> str:
    return value[:16] + r"\ldots{}"


def itemize(items: Iterable[str]) -> str:
    return "\n".join(
        [r"\begin{itemize}[leftmargin=*,itemsep=2pt]"]
        + [rf"\item {esc(item)}" for item in items]
        + [r"\end{itemize}"]
    )


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise BenchmarkToolError(message)


def _task_rows(root: Path) -> list[dict[str, Any]]:
    return [
        read_json(root / "tasks" / "P01" / tier / "task.json")
        for tier in ("T1", "T2", "T3")
    ]


def _validate_inputs(
    project_root: Path, benchmark_root: Path, measurement_path: Path
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], list[dict[str, Any]]]:
    measurement = read_json(measurement_path)
    _require(measurement.get("schema_version") == EXPECTED_SCHEMA, "wrong measurement schema")
    _require(measurement.get("kind") == EXPECTED_KIND, "wrong measurement kind")
    _require(measurement.get("status") == "complete", "measurement matrix is incomplete")
    _require(len(measurement.get("runs", [])) == 18, "measurement matrix must contain 18 runs")
    _require(measurement.get("summary", {}).get("passed") == 18, "not all local validations passed")
    privacy = measurement.get("privacy", {})
    _require(privacy.get("external_model_called") is False, "external model use was recorded")
    _require(privacy.get("authentication_read_or_copied") is False, "authentication use was recorded")
    _require(privacy.get("network_required") is False, "network use was recorded")

    config_path = benchmark_root / "metadata" / "config.json"
    environment_path = benchmark_root / "metadata" / "environment.json"
    release_path = benchmark_root / "metadata" / "release_files.json"
    construction_path = benchmark_root / "metadata" / "evidence" / "construction_validation.json"
    run_order_path = benchmark_root / "metadata" / "run_order.json"
    config = read_json(config_path)
    environment = read_json(environment_path)
    frozen = config["frozen_environment"]
    identity = measurement["fixed_identity"]
    _require(identity["environment_id"] == frozen["environment_id"], "environment ID changed")
    _require(
        identity["environment_bundle_sha256"] == environment_bundle_digest(config, environment),
        "environment bundle changed",
    )
    expected_hashes = {
        "config_sha256": sha256_file(config_path),
        "environment_record_sha256": sha256_file(environment_path),
        "release_manifest_sha256": sha256_file(release_path),
        "construction_validation_sha256": sha256_file(construction_path),
        "run_order_sha256": sha256_file(run_order_path),
    }
    for key, digest in expected_hashes.items():
        _require(identity.get(key) == digest, f"measurement has stale {key}")

    release = load_manifest(release_path)
    release_check = verify_manifest(benchmark_root, release)
    _require(release_check["ok"], "frozen release manifest no longer verifies")

    construction = read_json(construction_path)
    _require(construction.get("pass") is True, "construction evidence is not a pass")
    _require(construction.get("summary", {}).get("passed") == 6, "six construction checks did not pass")

    planned = [run_id for pair in read_json(run_order_path)["pairs"] for run_id in pair["run_ids"]]
    actual = [row["run_id"] for row in measurement["runs"]]
    _require(actual == planned, "offline measurements do not follow the frozen run order")
    for row in measurement["runs"]:
        validator = row.get("result", {}).get("validator") or {}
        _require(row["result"].get("pass") is True, f"{row['run_id']} failed")
        _require(validator.get("pass") is True, f"{row['run_id']} validator failed")
        _require(validator.get("semantic_statement_equal") is True, f"{row['run_id']} changed the theorem")
        _require(validator.get("dependency_audit_complete") is True, f"{row['run_id']} audit incomplete")
        _require(validator.get("forbidden_dependency_count") == 0, f"{row['run_id']} used a forbidden dependency")
        expected_use = row["condition"] == "L"
        _require(validator.get("library_use") is expected_use, f"{row['run_id']} library-use mismatch")

    paper = read_json(benchmark_root / "tasks" / "P01" / "paper.json")
    paper_source = project_root / paper["source"]["local_path"]
    spec_source = project_root / paper["benchmark_specification"]["local_path"]
    _require(sha256_file(paper_source) == paper["source"]["sha256"], "paper PDF changed")
    _require(
        sha256_file(spec_source) == paper["benchmark_specification"]["sha256"],
        "benchmark specification PDF changed",
    )

    reviews = [
        read_json(benchmark_root / "metadata" / "reviews" / name)
        for name in ("reviewer_1.json", "reviewer_2.json")
    ]
    for review in reviews:
        _require("final pass" in review.get("overall_status", ""), "a review is not final")
    _require(reviews[1].get("release_blockers") == [], "protocol reviewer has a release blocker")
    return measurement, config, environment, reviews


def _statistics(measurement: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for run in measurement["runs"]:
        grouped[(run["task_id"], run["condition"])].append(run)
    result: dict[tuple[str, str], dict[str, Any]] = {}
    for key, rows in grouped.items():
        times = [float(row["elapsed_seconds"]) for row in rows]
        result[key] = {
            "count": len(rows),
            "passed": sum(bool(row["result"]["pass"]) for row in rows),
            "mean": statistics.fmean(times),
            "median": statistics.median(times),
            "minimum": min(times),
            "maximum": max(times),
        }
    return result


def _task_table(tasks: list[dict[str, Any]]) -> str:
    rows = []
    for task in tasks:
        anchors = ", ".join(
            entry.get("equation", entry.get("anchor", ""))
            for entry in task["source_locations"]
        )
        rows.append(
            rf"{esc(task['task_id'])} & {esc(task['tier_label'])} & "
            rf"{esc(anchors)} & {esc(task['formal_statement']['plain_language'])} \\"
        )
    return "\n".join(rows)


def _assumption_sections(tasks: list[dict[str, Any]]) -> str:
    sections = []
    for task in tasks:
        source_text = "; ".join(
            f"PDF page {entry['pdf_page']} (printed page {entry['printed_page']}), "
            + entry.get("equation", entry.get("anchor", ""))
            for entry in task["source_locations"]
        )
        sections.append(
            rf"\subsection{{{esc(task['task_id'])}: {esc(task['tier_label'])}}}"
            + "\n"
            + rf"\textbf{{Fixed theorem name:}} \texttt{{{esc(task['formal_statement']['theorem_name'])}}}."
            + "\n\n"
            + rf"\textbf{{Source:}} {esc(source_text)}."
            + "\n\n"
            + rf"\textbf{{Statement in plain language:}} {esc(task['formal_statement']['plain_language'])}"
            + "\n\n"
            + rf"\textbf{{Why this tier:}} {esc(task['tier_rationale'])}"
            + "\n\n"
            + r"\textbf{Minimal assumptions kept in the Lean statement:}"
            + "\n"
            + itemize(task["assumptions"])
            + "\n"
            rf"\textbf{{Proof idea supplied to an evaluated agent:}} {esc(task['informal_proof'])}"
        )
    return "\n\n".join(sections)


def _aggregate_table(stats: dict[tuple[str, str], dict[str, Any]]) -> str:
    rows = []
    for task_id in ("P01-T1", "P01-T2", "P01-T3"):
        for condition in ("N", "L"):
            values = stats[(task_id, condition)]
            rows.append(
                rf"{esc(task_id)} & {condition} & {values['passed']}/{values['count']} & "
                rf"{fmt_seconds(values['mean'])} & {fmt_seconds(values['median'])} & "
                rf"{fmt_seconds(values['minimum'])} & {fmt_seconds(values['maximum'])} \\"
            )
    return "\n".join(rows)


def _raw_table(measurement: dict[str, Any]) -> str:
    rows = []
    for run in measurement["runs"]:
        validator = run["result"]["validator"]
        rows.append(
            rf"\texttt{{{esc(run['run_id'])}}} & {fmt_seconds(run['elapsed_seconds'])} & "
            rf"yes & {'yes' if validator['library_use'] else 'no'} \\"
        )
    return "\n".join(rows)


def _bar_chart(stats: dict[tuple[str, str], dict[str, Any]]) -> str:
    maximum = max(values["mean"] for values in stats.values())
    rows = []
    colors = {"N": "Nblue", "L": "Lgreen"}
    for task_id in ("P01-T1", "P01-T2", "P01-T3"):
        for condition in ("N", "L"):
            mean = stats[(task_id, condition)]["mean"]
            width = 9.0 * mean / maximum
            rows.append(
                rf"{esc(task_id)} / {condition} & "
                rf"\textcolor{{{colors[condition]}}}{{\rule{{{width:.3f}cm}}{{2.6mm}}}} "
                rf"{mean:.2f} s \\"
            )
    return "\n".join(rows)


def _paired_differences(measurement: dict[str, Any]) -> tuple[str, float]:
    pairs: dict[str, dict[str, float]] = defaultdict(dict)
    for run in measurement["runs"]:
        pairs[run["pair_id"]][run["condition"]] = float(run["elapsed_seconds"])
    rows = []
    differences = []
    for pair_id in [pair["pair_id"] for pair in read_json(BENCHMARK_ROOT / "metadata" / "run_order.json")["pairs"]]:
        values = pairs[pair_id]
        difference = values["L"] - values["N"]
        differences.append(difference)
        rows.append(
            rf"\texttt{{{esc(pair_id)}}} & {values['N']:.2f} & {values['L']:.2f} & {difference:+.2f} \\"
        )
    return "\n".join(rows), statistics.fmean(differences)


def _direct_dependency_latex(measurement: dict[str, Any], task_id: str) -> str:
    names: set[str] = set()
    for run in measurement["runs"]:
        if run["task_id"] == task_id and run["condition"] == "L":
            names.update(run["result"]["validator"]["direct_library_declarations"])
    wanted = {
        "P01-T1": [
            "NumStability.pairwiseSum_forward_error_bound",
        ],
        "P01-T2": [
            "NumStability.pairwiseSum_forward_error_bound",
            "NumStability.recursiveSum_forward_error_bound",
            "NumStability.gammaValid_mono",
            "NumStability.gamma_mono",
        ],
        "P01-T3": [
            "NumStability.noGuardAddWitness",
            "NumStability.noGuardAddWitness_error_eq",
        ],
    }[task_id]
    selected = [name for name in wanted if name in names]
    _require(selected == wanted, f"important dependencies missing for {task_id}")
    return "\n".join(
        [r"\begin{itemize}[leftmargin=*,itemsep=1pt,topsep=1pt]"]
        + [rf"\item \path{{{name}}}" for name in selected]
        + [r"\end{itemize}"]
    )


def _latex(
    project_root: Path,
    benchmark_root: Path,
    measurement_path: Path,
    measurement: dict[str, Any],
    config: dict[str, Any],
    environment: dict[str, Any],
    reviews: list[dict[str, Any]],
) -> str:
    tasks = _task_rows(benchmark_root)
    stats = _statistics(measurement)
    paired_rows, mean_paired_difference = _paired_differences(measurement)
    n_mean = measurement["summary"]["by_condition"]["N"]["mean_seconds"]
    l_mean = measurement["summary"]["by_condition"]["L"]["mean_seconds"]
    construction = read_json(
        benchmark_root / "metadata" / "evidence" / "construction_validation.json"
    )
    package = construction["verification_basis"]["packages_runtime"]
    source_manifest = construction["verification_basis"]["numstability_source"]
    compiled_manifest = construction["verification_basis"]["numstability_compiled"]
    frozen = config["frozen_environment"]
    paper = read_json(benchmark_root / "tasks" / "P01" / "paper.json")
    measurement_sha = sha256_file(measurement_path)
    reviewer_hashes = [
        sha256_file(benchmark_root / "metadata" / "reviews" / name)
        for name in ("reviewer_1.json", "reviewer_2.json")
    ]
    target_hashes = {
        task["task_id"]: sha256_file(
            project_root / task["formal_statement"]["target_file"]
        )
        for task in tasks
    }

    return rf"""\documentclass[11pt]{{article}}
\usepackage[T1]{{fontenc}}
\usepackage{{lmodern}}
\usepackage[margin=25mm]{{geometry}}
\usepackage{{booktabs,longtable,tabularx,array}}
\usepackage{{enumitem}}
\usepackage[table]{{xcolor}}
\usepackage{{seqsplit}}
\usepackage{{microtype}}
\usepackage{{fancyhdr}}
\usepackage[hidelinks]{{hyperref}}
\definecolor{{Nblue}}{{RGB}}{{42,95,160}}
\definecolor{{Lgreen}}{{RGB}}{{38,132,82}}
\definecolor{{lightgray}}{{RGB}}{{245,246,248}}
\newcolumntype{{Y}}{{>{{\raggedright\arraybackslash}}X}}
\newcommand{{\hashtext}}[1]{{\texttt{{\seqsplit{{#1}}}}}}
\setlength{{\parindent}}{{0pt}}
\setlength{{\parskip}}{{6pt}}
\setlength{{\headheight}}{{14pt}}
\pagestyle{{fancy}}
\fancyhf{{}}
\lhead{{HighamBench P01}}
\rhead{{Offline construction report}}
\cfoot{{\thepage}}
\title{{HighamBench P01\\Offline Construction and Validation Report}}
\author{{Prepared by Codex for the NumStability project}}
\date{{26 July 2026}}
\begin{{document}}
\maketitle

\begin{{center}}
\fcolorbox{{black}}{{lightgray}}{{\parbox{{0.90\textwidth}}{{
\textbf{{Privacy and meaning.}} Nothing in the measured matrix was sent to an outside service. No model was called and no authentication file was read or copied. The 18 measured rows time the local proof-checking machinery with already-written private proofs. They are not model proof-search results and they are not an official HighamBench score.
}}}}
\end{{center}}

\tableofcontents
\newpage

\section{{Short result}}

I built one complete benchmark entry for the paper \emph{{The Accuracy of Floating Point Summation}} by Nicholas J. Higham. No other paper was added. The entry contains one T1 task, one T2 task, and one T3 task. T1 means a direct use of a nearby library result. T2 means several results must be joined. T3 means a new bridge or proof must be built.

The three fixed Lean statements compile in both conditions. Lean is a program that checks mathematical proofs. Condition N has Lean and Mathlib, which is Lean's standard mathematics library, but has no NumStability files. Condition L is identical except that it also has the frozen NumStability source and compiled files.

All six complete construction proofs passed: one proof for each task and condition. I then repeated each local validation three times in the frozen condition order. All 18 validations passed. N passed 9/9 and L passed 9/9. N never used a NumStability declaration. Every L proof used at least one real NumStability declaration.

Mean local validation time was {n_mean:.2f} seconds in N and {l_mean:.2f} seconds in L. The paired mean L-minus-N difference was {mean_paired_difference:+.2f} seconds. This small timing difference describes compilation and checking overhead for fixed proofs. It does not show how much the library helps an agent discover a proof.

\section{{What I read and how I chose the tasks}}

I read all {paper['source']['pdf_pages']} PDF pages of the supplied journal paper. I also read all four pages of the benchmark specification. The paper does not place its main claims in named theorem boxes. I therefore used the numbered equations and their nearby explanations as exact source anchors.

The source paper fingerprint is \hashtext{{{esc(paper['source']['sha256'])}}}. SHA-256 means a content fingerprint: changing even one byte changes this value. The specification fingerprint is \hashtext{{{esc(paper['benchmark_specification']['sha256'])}}}.

\begin{{longtable}}{{@{{}}p{{16mm}}p{{18mm}}p{{40mm}}p{{75mm}}@{{}}}}
\toprule
Task & Tier & Paper anchor & Fixed result \\
\midrule
\endfirsthead
\toprule
Task & Tier & Paper anchor & Fixed result \\
\midrule
\endhead
{_task_table(tasks)}
\bottomrule
\end{{longtable}}

The labels were fixed before any measured validation. This prevents changing a tier after seeing whether a proof is easy or hard.

\section{{The three formal tasks and their minimal settings}}

A formal statement is a claim written precisely enough for Lean to check. A minimal setting means the smallest shared definitions and assumptions needed to state the paper result honestly in both conditions. None of the three target statements imports or names NumStability. This keeps N and L comparable.

{_assumption_sections(tasks)}

\section{{Shared Lean setting}}

The file \texttt{{shared/HighamBench/Definitions.lean}} supplies the common language used by all three targets. It defines:

{itemize([
        'StandardAddModel: a record describing rounded addition with the usual relative-error rule and a nonnegative unit roundoff.',
        'GammaValid and gamma: the usual condition k*u < 1 and the coefficient k*u/(1-k*u).',
        'pairwiseSum: balanced tree summation for exactly 2^r inputs.',
        'recursiveSum: left-to-right summation that keeps the first input exact.',
        'NoGuardAddModel: an addition rule with separate local errors on the old computed sum and the new input.',
        'noGuardRecursiveRunningBudget: the sum of computed-prefix and new-input sizes used by equation (5.3).',
    ])}

This shared file has fingerprint \hashtext{{{esc(environment['lean']['shared_definitions_sha256'])}}}. Its compiled Lean object has fingerprint \hashtext{{{esc(environment['lean']['shared_definitions_olean_sha256'])}}}. A compiled object is the checked binary form that Lean loads later.

\section{{Condition N and condition L}}

\subsection{{Condition N: no NumStability}}

Each N workspace contains only the controlled task package, the shared compiled definitions, Lean, Mathlib source, and the exact compiled support files required by Lean. Before a proof is copied into the workspace, a preflight check scans the whole staged task for NumStability names and asks Lean to import NumStability. The import must fail for the expected missing-module reason. All nine measured N runs passed this check. Their dependency audits found zero NumStability declarations.

\subsection{{Condition L: with NumStability}}

Each L workspace receives the same controlled task files plus read-only copies of the frozen NumStability source and compiled objects. The source snapshot contains {source_manifest['file_count']} files. The compiled snapshot contains {compiled_manifest['file_count']} files. Every L proof used real library declarations, confirmed by a transitive dependency audit. Transitive means the check follows helper results used by the proof instead of looking only at names typed in the last theorem.

The most important direct library declarations recorded were:

\begin{{description}}[leftmargin=31mm,style=nextline]
\item[P01-T1] {_direct_dependency_latex(measurement, 'P01-T1')}
\item[P01-T2] {_direct_dependency_latex(measurement, 'P01-T2')}
\item[P01-T3] {_direct_dependency_latex(measurement, 'P01-T3')}
\end{{description}}

\section{{How a proof is accepted}}

The validator is the trusted checking program. It performs these steps for every proof:

{itemize([
        'Check that the submitted source still has the fixed theorem name and theorem header.',
        'Reject sorry, admit, new local axioms, unsafe checking bypasses, and forbidden imports. These are shortcuts that would avoid a complete proof.',
        'Compile the candidate proof into a fresh uniquely named object.',
        'Compile a hidden copy of the expected theorem statement.',
        'Ask Lean whether the candidate theorem type and expected theorem type are definitionally equal. This means Lean itself confirms they are the same statement after normal simplification.',
        'Audit every proof dependency and reject a forbidden or missing helper.',
        'Recheck the controlled-file fingerprints before compilation, after compilation, after expected-statement compilation, and after the dependency audit.',
    ])}

No accepted construction or measured validation contained \texttt{{sorry}}, \texttt{{admit}}, a new axiom, or an unsafe bypass. All 18 semantic type checks passed. Semantic means the check compares mathematical meaning as understood by Lean, not just text formatting.

\section{{Isolation and frozen environment}}

Each validation uses a fresh Bubblewrap namespace. Bubblewrap is a Linux tool that gives a process a restricted view of files and processes. The Lean subprocess also receives an unshared network namespace, meaning it has no usable network interface. The external Codex runner was not started for this report.

The common pruned package tree contains exactly {package['file_count']:,} files and {package['total_bytes']:,} bytes. It has {package['mathlib_source_file_count']:,} Mathlib source files, {package['base_olean_file_count']:,} main compiled objects, and {package['compiled_support_file_count']:,} compiled support files. The complete tree was scanned for NumStability markers before N validation; none were found.

The frozen environment identifier is \texttt{{{esc(frozen['environment_id'])}}}. Its bundle fingerprint is \hashtext{{{esc(frozen['environment_bundle_sha256'])}}}. The release manifest contains 47 controlled files and has fingerprint \hashtext{{{esc(frozen['release_manifest_sha256'])}}}.

The run uses Lean {esc(environment['lean']['version'])}, Mathlib commit \texttt{{{esc(environment['lean']['mathlib_commit'])}}}, and NumStability commit \texttt{{{esc(environment['lean']['numstability_commit'])}}}. There is no OCI image. An OCI image is a fully packaged operating-system filesystem. Instead, the run uses fresh namespaces and read-only host system folders. Because those host folders are not one fully fingerprinted image, these results remain an observational local check.

\section{{Local measurement method}}

The fixed order has nine task--repetition pairs. Each pair contains N and L in an order chosen earlier from a recorded SHA-256 rule. I followed that exact order. Each of the 18 rows created a fresh workspace, staged the controlled task, copied the already-written private construction proof as the submission, and ran the complete hidden validator.

The clock starts immediately before staging and stops after validation. It includes task staging, the N absence check when applicable, helper compilation for T1 and T2, candidate compilation, expected-statement compilation, and the dependency audit. It excludes the one-time 5.48 GB release scan, which took {measurement['verification_basis_seconds']:.2f} seconds.

No proof search occurred in these rows. The proof was already written. No model token count exists, so every token field is null. This method answers ``does the complete local benchmark path work repeatedly in both conditions?'' It cannot answer ``does NumStability help Codex find proofs?''

\section{{Results}}

\subsection{{Summary by task and condition}}

\begin{{center}}
\begin{{tabular}}{{llrrrrr}}
\toprule
Task & Cond. & Pass & Mean & Median & Min. & Max. \\
& & & \multicolumn{{4}}{{c}}{{seconds}} \\
\midrule
{_aggregate_table(stats)}
\bottomrule
\end{{tabular}}
\end{{center}}

\subsection{{Mean-time diagram}}

The bars compare local validation time only. A longer bar does not mean that the theorem is harder for an agent to prove.

\begin{{center}}
\begin{{tabular}}{{p{{27mm}}p{{105mm}}}}
{_bar_chart(stats)}
\end{{tabular}}
\end{{center}}

\subsection{{Paired condition differences}}

Positive L-minus-N means the L validation took longer. Negative means it took less time. These differences are small system-timing changes, not proof-search benefits.

\begin{{center}}
\begin{{tabular}}{{lrrr}}
\toprule
Pair & N seconds & L seconds & L minus N \\
\midrule
{paired_rows}
\bottomrule
\end{{tabular}}
\end{{center}}

\subsection{{All 18 rows}}

\begin{{longtable}}{{p{{55mm}}rrr}}
\toprule
Run & Seconds & Passed & Used NumStability \\
\midrule
\endfirsthead
\toprule
Run & Seconds & Passed & Used NumStability \\
\midrule
\endhead
{_raw_table(measurement)}
\bottomrule
\end{{longtable}}

\section{{Code and files added}}

The benchmark implementation is under \texttt{{paper\_bencmark/highambench}}. The main parts are:

{itemize([
        'agent_prompt.md: the fixed instructions given to an evaluated proof agent.',
        'shared/HighamBench/Definitions.lean: the common formal language used in N and L.',
        'tasks/P01/T1, T2, and T3: each fixed target, plain context, and task record.',
        'metadata/controlled: exact four-file manifests for each execution package.',
        'tools/runner.py and tools/run_matrix.py: the resumable external-agent path, left unused because no data may be sent outside.',
        'tools/validator.py and tools/dependency_audit.lean: hidden proof and dependency checks.',
        'tools/lean_isolated.py and tools/offline_shell.c: filesystem and network isolation.',
        'tools/check_construction.py: the six private construction checks.',
        'offline_reporting/measure_validation.py: the new local-only 18-run timing tool.',
        'offline_reporting/render_report.py: the input-checking LaTeX report generator used for this document.',
    ])}

The offline measurement JSON is stored at \path{{{measurement_path.relative_to(project_root).as_posix()}}}. Its fingerprint is \hashtext{{{esc(measurement_sha)}}}. The source PDFs and private proofs remain under \texttt{{scratch\_pad}} and are not in the controlled release.

\section{{Testing and independent review}}

The final code test suite passed 91 of 91 tests. It covers manifest handling, N isolation, condition-specific mounts, token controls, network-attempt recording, result-set checks, report refusal rules, and attacks against the validator. The C isolation program was rebuilt with its documented C11 compiler command, and the rebuilt binary exactly matched the frozen binary.

Six fresh complete construction proofs passed the hidden validator. The construction evidence fingerprint is \hashtext{{{esc(measurement['fixed_identity']['construction_validation_sha256'])}}}.

Two independent Codex review passes checked different concerns. Review 1 re-read the paper and checked mathematical meaning, assumptions, source anchors, and tier honesty. Review 2 checked the formal interfaces, manifests, isolation, package tree, build reproduction, tests, and startup gate. Their final statuses are:

\begin{{itemize}}[leftmargin=*,itemsep=4pt]
\item Review 1: {esc(reviews[0]['overall_status'])}.\\ Fingerprint: \hashtext{{{esc(reviewer_hashes[0])}}}.
\item Review 2: {esc(reviews[1]['overall_status'])}.\\ Fingerprint: \hashtext{{{esc(reviewer_hashes[1])}}}.
\end{{itemize}}

\section{{Limits and correct interpretation}}

This release contains one paper only. It cannot represent all numerical analysis papers. The three repetition labels are not fixed model seeds. A seed is a control intended to reproduce a model's random choices. No frozen OCI image is available. Most importantly, the external model matrix was not run because no benchmark material may be sent to another service.

Therefore this report makes three narrow claims:

{itemize([
        'The paper was classified into honest T1, T2, and T3 tasks with exact source anchors.',
        'Each fixed statement has a complete Lean proof in both N and L, and the validator distinguishes library use correctly.',
        'The complete local checking path is repeatable: all 18 offline validations passed.',
    ])}

It does not claim a NumStability proof-search improvement, model success rate, model token saving, or official HighamBench score. Reporting such a number without fresh agent attempts would be fabricated. The code for a future authorized agent study remains present, but it was not used here.

\section{{Exact target fingerprints}}

\begin{{center}}
\begin{{tabular}}{{ll}}
\toprule
Target & SHA-256 fingerprint \\
\midrule
P01-T1 & \hashtext{{{esc(target_hashes['P01-T1'])}}} \\
P01-T2 & \hashtext{{{esc(target_hashes['P01-T2'])}}} \\
P01-T3 & \hashtext{{{esc(target_hashes['P01-T3'])}}} \\
\bottomrule
\end{{tabular}}
\end{{center}}

\section{{Final conclusion}}

The requested one-paper benchmark entry is built, frozen, reviewed, and locally exercised in both conditions. The T1 statement is a direct specialization, T2 joins separate error bounds and a coefficient comparison, and T3 formalizes the no-guard computed-prefix bound. All formal statements and complete proofs pass. The local 18-run validation matrix is complete and private. Its timing numbers describe the checking machinery only, which is the strongest accurate result possible without sending task material to a proof agent service.

\end{{document}}
"""


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path, default=BENCHMARK_ROOT)
    parser.add_argument("--measurement", type=Path, required=True)
    parser.add_argument("--output-tex", type=Path, required=True)
    parser.add_argument("--compile-pdf", action="store_true")
    return parser


def main() -> int:
    args = _parser().parse_args()
    project_root = args.project_root.resolve()
    benchmark_root = args.benchmark_root.resolve()
    measurement_path = args.measurement.resolve()
    measurement, config, environment, reviews = _validate_inputs(
        project_root, benchmark_root, measurement_path
    )
    latex = _latex(
        project_root,
        benchmark_root,
        measurement_path,
        measurement,
        config,
        environment,
        reviews,
    )
    args.output_tex.parent.mkdir(parents=True, exist_ok=True)
    args.output_tex.write_text(latex, encoding="utf-8")
    output: dict[str, Any] = {
        "tex": str(args.output_tex.resolve()),
        "tex_sha256": sha256_file(args.output_tex.resolve()),
        "pdf": None,
        "measurement_sha256": sha256_file(measurement_path),
    }
    if args.compile_pdf:
        command = [
            "latexmk",
            "-pdf",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-outdir={args.output_tex.parent.resolve()}",
            str(args.output_tex.resolve()),
        ]
        completed = subprocess.run(
            command,
            cwd=project_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if completed.returncode != 0:
            tail = "\n".join(completed.stdout.splitlines()[-80:])
            raise BenchmarkToolError(f"LaTeX compilation failed:\n{tail}")
        pdf = args.output_tex.with_suffix(".pdf").resolve()
        _require(pdf.is_file(), "LaTeX reported success but made no PDF")
        output["pdf"] = str(pdf)
        output["pdf_sha256"] = sha256_file(pdf)
        output["pdf_bytes"] = pdf.stat().st_size
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BenchmarkToolError as error:
        print(f"report error: {error}", file=sys.stderr)
        raise SystemExit(2)
