# HighamBench source-first formalization pilot

This directory is the control plane for the source-first HighamBench pilot. It
does not use the legacy fixed-target proof runner in
`paper_bencmark/highambench/tools/runner.py`.

The pilot accepts exactly these tasks:

- `P01-T2`
- `P02-T2`
- `P03-T2`
- `P13-T2`
- `P14-T2`

For each requested task, the controller runs one condition N formalizer and one
condition L formalizer in the frozen order recorded in `config.json`.
Both formalizers receive the same paper and common prompt. L alone receives the
frozen NumStability snapshot and the explicit encouragement appendix. That
appendix names the read-only source at `/library/NumStability`, explains that
compiled declarations are on `LEAN_PATH`, and gives concrete `find`, `rg`, and
`import NumStability` discovery/import guidance.

The benchmark measures the construction of a faithful Lean proposition. The
root declaration is deliberately left as `by sorry`; proof search is outside
the outcome. A condition may submit at most four times in one persistent Codex
conversation and one live raw-event-enabled app-server process. Validation and
fresh-agent faithfulness auditing happen while the contestant clock is paused.
For each attempt, the model-active interval begins immediately before the
`turn/start` request and runs through contestant-process quiescence. The later
candidate copy/hash is timed and charged as a separate component; validation,
telemetry settling, and auditing stay off-clock. The two charged components are
summed against an 18,000-second cumulative limit. Exact provider usage is
metered and reported but does not stop the benchmark.

## Operator commands

On Titan, use the installed launcher so every command enters the fixed hardware
envelope:

```bash
~/.local/bin/run-highambench-formalization doctor --task-id P01-T2
~/.local/bin/run-highambench-formalization run --task-id P01-T2
~/.local/bin/run-highambench-formalization status --task-id P01-T2
```

Use `--dry-run` with `run` to exercise admission, staging, condition isolation,
and hashing without making provider calls or consuming the task's one official
pair slot.

Every real run enters a transient user service with systemd-enforced affinity
to the setup-frozen eight logical CPUs and cgroup limits of 32 GiB RAM, 512
tasks, and no swap. Generated shell-command trees are additionally confined to
a delegated child cgroup limited to 24 GiB RAM, 384 tasks, and no swap, leaving
protected capacity for the trusted controller. The outer service denies
affinity changes throughout its process tree, every strict hardware snapshot
tests that denial, and the generated-command seccomp policy repeats it.

Setup also performs one clean full build of the frozen NumStability snapshot.
It cleans the workspace, rehydrates the frozen dependency cache off-clock, and
proves the root project build tree is empty immediately before measurement.
The build runs in the same fixed outer hardware envelope but is never charged
to either contestant. Its wall/CPU
time, peak memory and other GNU `time` statistics, hardware/cgroup snapshots,
sanitized environment, source/configuration and dependency-cache digests,
source/object counts, complete build output, and hashes are retained under
`runtime/library/build/` in the private deployment and authenticated by every
doctor run.

## Private inputs

PDFs are intentionally not committed. The deployment root must contain the five
hash-verified files named by `manifest.json`. The NumStability source and
compiled snapshot are also private runtime inputs and must resolve to commit
`45813a95dacf577461bae13f033af0dbc985a225`.

The controller never stages the old `Target.lean`, `context.md`, shared
HighamBench definitions, construction metadata, audit history, Git repository,
or the other condition's output into a contestant workspace.

See `PROTOCOL.md` for the frozen experimental contract, `ARCHITECTURE.md` for
the control/data flow and script inventory, and `deployment/TITAN.md` for
installation and hardware containment.
