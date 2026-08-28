# HighamBench execution corpus

This directory is the executable package for measuring whether access to the
NumStability Lean library helps an agent complete fixed numerical-analysis
proofs.

The corpus contains 60 tasks from 20 papers, with three tasks per paper:

- `T1`: direct use or specialization of a nearby library result;
- `T2`: combination of multiple results with additional reasoning;
- `T3`: a material extension beyond a ready-made library theorem.

The ordered paper and task catalog, source hashes, selected source locations,
and fixed theorem declarations are recorded in `metadata/manifest.json`.

## Conditions

Every task is run under two conditions with the same target, context, shared
Lean scaffold, model, limits, and runtime:

- `N`: Lean and Mathlib are available, but no NumStability source, compiled
  file, documentation, index, or cache is visible.
- `L`: the frozen NumStability package is additionally available as read-only
  source at `/library/NumStability`, a curated lookup index at
  `/library/docs/LIBRARY_LOOKUP.md`, and compiled modules at `/library-olean`.

Condition L uses NumStability commit
`4ec1ec874353010ad93cc0bb76370ac321da4681`. The repository root's
`lakefile.toml` installs that commit under `.lake/packages/numStability`; the
library source is not copied into this branch.

The common prompt is `agent_prompt.md`. Only L receives the neutral package
location and discovery notice in `condition_prompts/L.md`.

## Controlled task input

An attempt starts from an empty workspace. Its task-specific controlled
manifest stages only:

- `agent_prompt.md`;
- `shared/HighamBench/Core.lean`;
- the exact paper-scoped shared modules declared by the central manifest;
- one `Target.lean`;
- one `context.md`.

`task.json` and `paper.json` are trusted runner metadata and are not prompt
material. Task construction proofs, reference PDFs, audit files, and earlier
agent outputs are not part of this branch or any attempt.

## Fixed matrix

The planned matrix is:

```text
60 tasks x 3 repetitions x 2 conditions = 360 runs
```

`rep-01`, `rep-02`, and `rep-03` are repetition identifiers, not backend random
seeds. `metadata/run_order.json` records the deterministic N/L order within
each task-repetition pair.

Each attempt has a 1,800-second wall-clock limit and a 5,000,000-token limit.
The frozen agent preset is `gpt-5.6-sol` with `ultra` reasoning and at most four
concurrent root/subagent inference threads.

## Layout

| Path | Purpose |
| --- | --- |
| `tasks/P*/T*/` | Fixed target, context, and task metadata |
| `shared/HighamBench/` | Condition-neutral task definitions |
| `metadata/controlled/` | Exact staged-file manifest for each task |
| `metadata/manifest.json` | Corpus and theorem catalog |
| `metadata/config.json` | Conditions, limits, and frozen environment contract |
| `metadata/run_order.json` | Complete paired assignment order |
| `tools/run_matrix.py` | Resumable 360-run orchestrator |
| `tools/runner.py` | Isolated single-attempt runner and hidden validation |
| `tools/analyze.py` | Completeness checks and summary statistics |

## Bootstrap

From the repository root:

```bash
lake update
lake exe cache get
```

This materializes the exact package revisions in `lake-manifest.json`. Final
compiled artifacts must be produced on the frozen Linux execution host as
described in `EXECUTION_FREEZE.md`.

## Run

After the final Linux freeze has produced and authenticated the external
artifacts, run from the repository root:

```bash
python3 paper_bencmark/highambench/tools/run_matrix.py \
  --benchmark-root paper_bencmark/highambench \
  --project-root . \
  --results-root artifacts/results \
  --codex <CODEX_BINARY> \
  --auth-file <CODEX_AUTH_FILE> \
  --offline-shell artifacts/bin/offline_shell \
  --toolchain-root <LEAN_TOOLCHAIN_ROOT> \
  --packages-root .lake/packages \
  --packages-runtime-root artifacts/packages_runtime \
  --shared-olean-root artifacts/shared_olean \
  --library-source .lake/packages/numStability/NumStability \
  --library-root-file .lake/packages/numStability/NumStability.lean \
  --library-olean artifacts/library_olean \
  --release-manifest paper_bencmark/highambench/metadata/release_files.json \
  --agent-network-verified \
  --token-control-verified
```

The runner verifies task hashes, package commits, compiled manifests, tool
hashes, host identity, isolation controls, and live canaries before releasing
the first prompt. It fails closed when any frozen input is missing or stale.

## Analyze

After all assignments complete:

```bash
python3 paper_bencmark/highambench/tools/analyze.py \
  artifacts/results/runs.jsonl \
  --output-dir artifacts/results/analysis \
  --run-order paper_bencmark/highambench/metadata/run_order.json \
  --config paper_bencmark/highambench/metadata/config.json \
  --manifest paper_bencmark/highambench/metadata/manifest.json \
  --repository-root .
```

Use `tools/result_set.py` to authenticate the complete result set before
accepting any summary. Publication-oriented report generation belongs outside
this execution-only branch.

## Current status

The task corpus is final, but this checkout must remain non-runnable until the
new Higham-only NumStability package, shared `.olean` bundles, package runtime,
host identity, release manifest, and two live canaries are rebuilt together on
the Linux benchmark host. Do not start measured runs while
`metadata/manifest.json` says `measurements prohibited`.

The experiment measures proof completion, time, token use, and observed library
use for fixed Lean statements. It does not measure translation from unrestricted
paper prose into Lean.
