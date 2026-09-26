# NumStability proof-required benchmark: thesis evidence release

This directory publishes the complete **analysis inputs and selected raw evidence** for
the fifteen-task, two-campaign Pilot 34/35 development composite. The measured
tasks, prompts, conditions, and results have not been edited for this report.
This is exploratory and outcome-aware, not a held-out confirmatory trial.

## Build the report

From the repository root, using Python 3.14 or another supported Python with
compatible wheels:

```sh
python3 paper_bencmark/thesis_report/verify_release.py
python3 -m venv /tmp/numstability-report-venv
/tmp/numstability-report-venv/bin/pip install -r paper_bencmark/thesis_report/requirements.txt
/tmp/numstability-report-venv/bin/python paper_bencmark/thesis_report/make_figures.py
cd paper_bencmark/thesis_report
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=../../output/pdf report.tex
```

The compiled deliverable is `output/pdf/report.pdf` at the repository root.
All figures, the task CSV, declaration scan, summary JSON, and table fragments
are regenerated directly from:

- `paper_bencmark/pilot35/RESULTS_15.json` — SHA-256
  `3faeb35af66f5c3c9d16e0800a4c88bd5cef09e1a35f0bc10e6c387f40d9c050`
- `paper_bencmark/thesis_report/evidence/warm-root.json` — SHA-256
  `3401426d25ee278cbf33e48da80f665d5bcc4ad8bcab721a4fa69cae0095ee39`

The script checks the task IDs against the frozen scheduled order in
`design33/CORPUS_15.json`. Positive gain is `(N - L) / N`; a negative value
favors N. The warm-inclusive per-task panels allocate the *single* warm-scout
cost evenly over fifteen tasks, whereas the cumulative panel charges it once.

## Protocol, inputs, and raw result evidence

The frozen schedule and source-PDF SHA-256 values are in
`paper_bencmark/formalization_benchmark/design33/CORPUS_15.json` and
`ADMISSION_15.json`; screening and metric contracts are `SCREENING.md` and
`METRICS.md` in that directory. Source packets are in `design33/packets/`.
The common/L/scout/proof prompts are in `design27/prompts/`. The operative
no-hole proof reminder is
`paper_bencmark/prospective_proof_no_holes/PROOF_PROMPT.md`. Pilot 34 and 35
controllers, recovery protocol, and hash-checked composite reporter remain
in the repository under `paper_bencmark/pilot35/` and their referenced
`formalization_benchmark` modules. The full elaborated proof-dependency scan
source is `paper_bencmark/formalization_benchmark/tools/design33_proof_dependencies.lean`.

The two evidence archives preserve **four sealed Pilot 34 pairs** and
**eleven sealed Pilot 35 pairs**, plus Pilot 34's excluded partial
CAST08-PROP3.1 audit incident. They contain campaign metadata; pair and
condition reports; all final and submitted Lean candidates; statement/proof
validation; observed formalizer prompts, events and turn metadata; auditor
prompts, outputs and adjudications; and hardware snapshots. Audit role event
streams, compiled `.olean` caches, network-violation binary traces, and
private Codex state are omitted from this compact publication bundle. The
complete original roots remain on Titan and can be used for full
`composite_report.py` revalidation; the compact archives alone are not a
substitute for every original file hash.

| Artifact | SHA-256 | Members |
| --- | --- | ---: |
| `evidence/pilot34-high-overlap-20260924-a-thesis-evidence.tar.gz` | `7f9b3774458a8e9ca1cc871ec6e1718933911cb2c2843b604a55bffe2a5cc3fc` | 312 |
| `evidence/pilot35-audit-recovery-20260925-a-thesis-evidence.tar.gz` | `c4c5b8fac97cc2172d811e13a3e81acbf5eb10d76482867d5681e62283b7f438` | 712 |
| `evidence/library-snapshot.json` | `c82dc7ec24af3a49569b94e28bb6e4942f45e2f910cbec59628836d76345b84a` | — |
| `evidence/library-build-record.json` | `6f4581380982e51fd52a342cc380db5c8bae5d427d32be9c8f2aa9d136de8058` | — |
| `evidence/runtime-snapshot.json` | `9fac78511309a5919d31424eb0adc5964a26f0e334542639fdd9f81fd3979fc6` | — |
| `evidence/warm-scout/turn.json` | `520f7efaa34ba72ad89b2d7e7826721244ac58c94b4b158cd190b4480b20fbc2` | — |

Inspect safely with `tar -tzf ARCHIVE` or extract to a new temporary
directory. Do not extract onto an existing campaign root. Neither archive
contains an authentication file, Codex checkpoint database, or paper PDF.
The archives were scanned for the known SSH password and common token-key
markers before publication. The source PDFs are third-party works and are
not newly redistributed here; exact hashes and bibliographic acquisition
details are in each frozen packet and `ADMISSION_15.json`. The Higham book
chapter in particular should be supplied by an authorized local copy.

## Re-running the *experiment*, not just the report

1. Provision a Linux x86-64 host with three disjoint 8-logical-CPU/24-GiB
   cgroup lanes, swap disabled and the recorded affinity/pid limits. The
   archived campaign JSON and hardware-before records specify the exact CPU
   sets. Codex CLI 0.156.0 used ChatGPT sign-in; no API key or billing secret
   is published.
2. Checkout NumStability commit
   `45813a95dacf577461bae13f033af0dbc985a225`, Lean
   `leanprover/lean4:v4.29.0-rc3`, and Mathlib commit
   `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`. The library build record
   documents dependency-cache preparation and its separate measured full
   build (1,315.18 s). Rebuild compiled objects rather than copying private
   or host-specific caches into the public branch.
3. Supply the five exact hash-verified source PDFs named in the packets. The
   source packets and tasks' own `source/task.md` define the target and scope.
   Private admission skeletons are **screening evidence only**, not contestant
   input. Do not put them in N or L workspaces.
4. Configure both conditions with GPT-6 Sol/high, audit roles with GPT-6
   Astra/high, the frozen prompts and paper packets, a four-statement and
   four-proof submission limit, a full NumStability mount only for L, and
   disabled contestant subagents. Create the task-neutral warm root once
   before L tasks. The runner and protocol files in `design27`, `design33`,
   and `pilot35` document the remaining checks.
5. Launch under a **new pilot identity**. Model conversations are stochastic:
   this is a protocol rerun, not bit-for-bit replay. Never overwrite Pilot
   34/35, silently rerun a measured pair, or reclassify a failed task after
   inspecting the outcome. Report a new run separately.

The unchanged original Titan campaign roots are
`/hdd/alexgeorgantzas/highambench/pilot34-high-overlap-20260924-a` and
`/hdd/alexgeorgantzas/highambench/pilot35-audit-recovery-20260925-a`. Pilot 35
is a disclosed incident recovery, not an independent replicate. The hash-
checked results were produced by `paper_bencmark/pilot35/composite_report.py`.
This publication bundle intentionally does not contain private credentials,
third-party PDFs that were not already tracked, or a runnable authenticated
session checkpoint.

## Scientific interpretation

All fifteen pairs were audited faithful and kernel-proved. L saved 10.2% proof
code and 14.6% active time overall, but used 24.4% more net-new tokens. Five
known favorable retained tasks contribute the aggregate proof-line gain. The
ten new tasks alone have 6.7% more L proof code. Eight new tasks share one
paper, and a descriptive declaration-usage heatmap cannot establish a causal
``enough overlap means improvement'' rule. The report preserves that
limitation rather than selecting only successful tasks.
