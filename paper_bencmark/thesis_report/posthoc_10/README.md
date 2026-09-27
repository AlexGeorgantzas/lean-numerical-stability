# Ten-task post-hoc sensitivity report

This is a **post-outcome, user-selected subset**, not a new benchmark or a
replacement for the complete fifteen-task report. The excluded task IDs are
hardcoded in `make_report.py` and all five still appear in the exclusion table
and selection plot. The original sealed N/L runs are unchanged.

The Python script reads only the primary report's generated `task_metrics.csv`,
`realized_reuse.csv`, and `summary.json`; validates task identities and counts;
then regenerates `generated/summary.json`, three LaTeX tables, and two figures.
The derived JSON includes input SHA-256 hashes and full-precision values.

From the repository root:

```sh
python3 paper_bencmark/thesis_report/verify_release.py
python3 paper_bencmark/thesis_report/posthoc_10/make_report.py
cd paper_bencmark/thesis_report/posthoc_10
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../../output/pdf -jobname=posthoc_10_sensitivity report.tex
```

The resulting PDF is `output/pdf/posthoc_10_sensitivity.pdf`. Matplotlib and
NumPy are required for the figures, as in the primary report. Positive
N-to-L gains mean lower L cost. The task selection and realized-reuse rubric
were both applied after results were observed; neither is blinded or causal.
