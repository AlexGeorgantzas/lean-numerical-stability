# HighamBench source-first formalization pilot

This directory is the control plane for the source-first HighamBench pilot-4. It
does not use the legacy fixed-target proof runner in
`paper_bencmark/highambench/tools/runner.py`.

Pilots 1, 2, and 3 are preserved as sealed, unscored predecessors. Pilot-1 P01-T2
stopped on a provider multi-agent capability incident. Pilot-2 P01-T2
(`P01-T2-20260916T084145Z-6dad064a`) stopped after N submitted one compiling
candidate: the provider rejected the blind-translation audit response schema,
so no faithfulness verdict was produced and L never started. Pilot-3 P01-T2
(`P01-T2-20260916T150151Z-40b3a1dd`) stopped after an unchanged placeholder
candidate because the Codex Code Mode host was absent inside the sandbox;
paper-facing auditors could not read their workspace and L never started.
Pilot-4 starts all five tasks anew under its own release identity. Do not pool observations across
pilots, alter the old evidence, or use an older launcher for a replacement run.

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
summed against an 18,000-second cumulative termination threshold. A measured
timer or final-freeze overshoot is retained and yields an unscored
`ACTIVE_TIME_LIMIT`, never a faithful acceptance. Exact provider usage is
metered and reported but does not stop the benchmark.

## Operator commands

On Titan, use the installed launcher so every command enters the fixed hardware
envelope:

```bash
~/.local/bin/run-highambench-formalization-pilot-4-r1 doctor --task-id P01-T2
~/.local/bin/run-highambench-formalization-pilot-4-r1 qualify-provider --task-id P01-T2
~/.local/bin/run-highambench-formalization-pilot-4-r1 run --task-id P01-T2
~/.local/bin/run-highambench-formalization-pilot-4-r1 status --task-id P01-T2
```

Use `--dry-run` with `run` to exercise admission, staging, condition isolation,
and hashing without making provider calls or consuming the task's one official
pair slot.

The exact app-server configuration disables agent delegation through
`agents.enabled=false` and both multi-agent feature flags. The controller
attests the effective configuration and features before model inference and
fails closed on any collaboration or foreign-thread event. A paid but
off-benchmark provider canary qualifies this capability before a fresh
official pair is indexed. It also submits the exact frozen schemas for blind
translation, direct judgment, round-trip judgment, and adjudication through
live provider calls with synthetic checkable outputs. It also requires
trace-backed reads of a seeded workspace file for both role types and a
checked write for the formalizer, and rejects Code Mode startup failures. This
closes the pilot-3 gap: its schema-only qualification passed while workspace
tools were unavailable. Qualification time and tokens never enter
contestant totals.
The Codex binary and its same-package Code Mode host are both hash-pinned by
the deployment, and the host is mounted read-only beside `/codex` inside the
minimal Bubblewrap filesystem.
Provider-free `doctor` and `--dry-run` do not make this inference call.
`qualify-provider` runs these paid checks without consuming an official task
slot; a later `run` verifies and reuses its sealed record.

Release repair, installation, and qualification are preparation, not an
instruction to start an official pair. Check all five statuses after setup;
issue `run` only when explicitly requested for that task.

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
