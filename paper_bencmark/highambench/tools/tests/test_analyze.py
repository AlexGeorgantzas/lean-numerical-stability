from __future__ import annotations

import csv
import json
from pathlib import Path
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from analyze import analyze, load_runs, render_latex, write_csv_tables  # noqa: E402


def run(
    tier: str,
    condition: str,
    passed: bool,
    seconds: float,
    tokens: int | None,
    *,
    scored: bool = True,
) -> dict:
    pair_id = f"paper-1:{tier}:seed-7"
    return {
        "schema_version": 1,
        "kind": "highambench-run",
        "run_id": pair_id + ":" + condition,
        "pair_id": pair_id,
        "paper_id": "paper-1",
        "task_id": "task-" + tier,
        "tier": tier,
        "condition": condition,
        "repetition_id": "rep-01",
        "backend_seed": 7,
        "seed": 7,
        "agent": {"id": "codex", "version": "1", "model": "test-model"},
        "pass": passed,
        "scored": scored,
        "failure_code": None if passed else "PROOF_ERROR",
        "scored_elapsed_seconds": seconds,
        "token_usage": None if tokens is None else {"model_tokens": tokens},
        "library_use": condition == "L" and passed,
    }


class AnalysisTests(unittest.TestCase):
    def records(self) -> list[dict]:
        return [
            run("T1", "N", False, 100, 100),
            run("T1", "L", True, 20, 80),
            run("T2", "N", True, 30, 50),
            run("T2", "L", True, 10, 40),
            run("T3", "N", True, 20, None),
            run("T3", "L", False, 100, None),
            run("T1", "N", True, 1, 1, scored=False),
        ]

    def test_condition_and_paired_statistics(self) -> None:
        result = analyze(
            self.records(),
            include_unscored=False,
            bootstrap_resamples=50,
            bootstrap_seed=9,
        )
        self.assertEqual(result["analyzed_run_count"], 6)
        self.assertEqual(result["excluded_run_count"], 1)
        self.assertEqual(result["pair_problems"], [])
        overall_n = next(
            row
            for row in result["condition_summaries"]
            if row["scope"] == "overall" and row["condition"] == "N"
        )
        self.assertAlmostEqual(overall_n["pass_rate"], 2 / 3)
        self.assertEqual(overall_n["median_scored_seconds"], 30)
        overall_pair = next(
            row for row in result["paired_comparisons"] if row["scope"] == "overall"
        )
        self.assertEqual(overall_pair["pass_rate_change"], 0)
        self.assertEqual(overall_pair["median_paired_time_change"], -20)
        self.assertEqual(overall_pair["median_paired_token_change"], -15)
        self.assertFalse(overall_pair["bootstrap"]["informative"])
        self.assertIn("degenerate", overall_pair["bootstrap"]["note"])

    def test_writes_machine_and_latex_tables(self) -> None:
        result = analyze(
            self.records(),
            include_unscored=False,
            bootstrap_resamples=5,
            bootstrap_seed=2,
        )
        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw)
            write_csv_tables(output, result)
            with (output / "condition_summary.csv").open() as stream:
                condition_rows = list(csv.DictReader(stream))
            with (output / "paired_summary.csv").open() as stream:
                paired_rows = list(csv.DictReader(stream))
            self.assertTrue(condition_rows)
            self.assertTrue(paired_rows)
            latex = render_latex(result)
            self.assertIn("HighamBench result tables", latex)
            self.assertIn("Paired changes", latex)
            self.assertIn("\\end{document}", latex)

    def test_jsonl_loader_reports_bad_lines(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "runs.jsonl"
            good = self.records()[0]
            path.write_text(json.dumps(good) + "\nnot-json\n{}\n", encoding="utf-8")
            runs, malformed = load_runs([path])
            self.assertEqual(runs, [good])
            self.assertEqual(len(malformed), 2)


if __name__ == "__main__":
    unittest.main()
