# Ten-task NumStability benchmark evidence report

This is a standalone report about the ten tasks named in the dated selection
manifest. It covers the complete source-first N/L protocol, prompts, models,
hardware, time/token/code metrics, warm-up accounting, declaration usage,
realized-reuse scoring, audit overhead, task-level appendices, and limitations.
Seven binned heatmaps compare reuse score with each requested gain, and
formalization versus proof and total time versus net-new tokens. Their exact
bin edges and members are in `generated/heatmap_cells.json`.

Scientific status: **retrospective, outcome-informed development evidence**.
The task set and three-role realized-reuse rubric were chosen/annotated after
outcomes were available. The document does not present the cohort as held-out
or independently sampled. It does not rerun or edit a benchmark task. The
selection manifest remains in the repository for provenance.

From the repository root, with Python packages `matplotlib`, `numpy`, and
`scipy` and a TeX Live installation:

```sh
python3 paper_bencmark/thesis_report/verify_release.py
python3 paper_bencmark/thesis_report/ten_task_report/make_figures.py
cd paper_bencmark/thesis_report/ten_task_report
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../../output/pdf -jobname=numstability_ten_task_report report.tex
```

The final PDF is `output/pdf/numstability_ten_task_report.pdf`. The plotting
program generates only ten-task figures and tables under this directory's
`figures/` and `generated/` folders. `generated/source_task_ledger.json`
holds the exact sealed task records used; `generated/summary.json` records
aggregates, source SHA-256 identities, and the selection-manifest digest.
`generated/realized_reuse.json` records exact statement/proof witnesses.
The primary verifier checks immutable pair and archive evidence before the
derived script runs. Third-party source PDFs and authentication state are
not redistributed by this report.
