---
name: run-highambench-experiments
description: Prepare, preflight, launch, resume, validate, and report fixed HighamBench T1–T3 Condition N/L benchmarking experiments in this repository. Use for measurement and campaign operations; not for task construction, T4 corpora, or NumStability formalization.
---

# Run HighamBench Experiments

## Operating scope

Operate the fixed T1–T3 corpus under `paper_bencmark/highambench` through its
trusted tools and the allowlisted launchers in `paper_bencmark/scratch_pad`.
This is an operator skill. Never place this skill, its instructions, or operator
state inside a measured agent's prompt, workspace, Codex home, or mounted files.

Do not use this skill to select, construct, revise, or reclassify tasks; build a
T4 corpus; formalize NumStability; or repair controlled content to make a run
pass. A controlled change returns to construction and requires a new snapshot,
validation, review, and authorization before measurement.

Treat an explicit request to run a named experiment stage as authorization only
for that stage. Inspection, cleanup, planning, preflight, or report requests do
not authorize campaign or result-root creation, paid provider calls, live
canaries, snapshot refresh, canary promotion, publication, commit, or push. Keep all measurements private unless
the user separately authorizes release.

## Load context progressively

Before any provider process or scored run:

1. Read `paper_bencmark/highambench/README.md` completely as the protocol and
   current-status authority.
2. Read [the operations map](references/operations.md) completely, then read
   the selected launcher or manager before invoking it.
3. Inspect `metadata/config.json`, `environment.json`, `manifest.json`,
   `release_files.json`, `run_order.json`, `library_source.json`, and the
   relevant compiled/runtime manifests through the canonical admission tools.
   Do not hand-edit derived hashes or treat CLI values as overrides.

For a status-only, offline verification, or report request, load only the
operation-specific files routed by the operations map. Do not load private
proofs, gold solutions, unrelated result roots, or paper PDFs into a measured
context.

## Non-negotiable experiment invariants

- Derive task, repetition, condition order, model, limits, toolchain, package,
  prompt, runtime, and hardware expectations from the frozen metadata. The
  current T1–T3 design is P01–P20, one T1/T2/T3 task per paper, three
  repetitions, and paired N/L attempts; any catalog discrepancy is a hard stop.
- N and L use byte-identical controlled task/context/shared inputs. N receives
  no NumStability source, object, documentation, index, name list, or cache. L
  alone receives the frozen L supplement and exact read-only NumStability
  source/object mounts.
- Condition L uses the authenticated `NumStability/` and `NumStability.lean`
  in the current project checkout. Never substitute files from another branch,
  mutable checkout, or unverified build.
- Preserve fresh isolated workspaces, provider conversations, and private state
  for every attempt. Never expose private construction proofs or proof hints.
- Use the frozen order in `metadata/run_order.json`. Do not reorder N/L, invent
  seeds, change limits, or describe repetition IDs as random seeds.
- Treat the N/L pair as the hardware unit: both conditions must finish in the
  same authenticated allocation and node. Parallelize complete pairs only;
  never split the two conditions across jobs or machines.
- Keep raw-access P01 results separate from signposted-library measurements.
  Never pool, overwrite, or count them as repetitions of the current protocol.

## Fail-closed admission

Before a provider call, require the canonical release and runner admission
checks to authenticate the exact controlled files, source and object manifests,
pinned commit, Lean/Mathlib/runtime, host, interpreter, provider binary, prompt,
hardware, and both live-canary descriptors. All status fields and gates must
agree. A dirty ignored result directory is not itself a failure, but drift in
any controlled or release-listed path is.

Stop before provider startup when any required item is stale, missing,
unscorable, contradictory, or mismatched; when the host cannot supply the
complete pair time envelope; when a launcher pin differs from current frozen
metadata; when a result root collides; or when an active marker or incident
cannot be authenticated. Report the exact failed gate and evidence path. Never
silently refresh metadata, edit launcher pins, relax validation, bypass
canaries, use `--force`, or repair the corpus during measurement admission.

If a descriptor explicitly requires replacement and the user authorized live
canaries, run the synthetic Ultra canary, explicitly promote and verify it, then
run the token-control canary, explicitly promote and verify it. Promotion is a
controlled metadata mutation and must finish before campaign-index creation.
Synthetic canaries must never receive benchmark task bytes.

## Execute the smallest authorized unit

Prefer one immutable N/L pair transaction through `tools/run_matrix.py` and the
appropriate reviewed campaign manager. Treat frozen CLI options as equality
assertions, not knobs. Do not default a request for a check or canary to the
360-run matrix. Do not invent a whole-corpus Slurm command when no reviewed
runbook exists for it.

For each managed pair: begin the transaction, run the exact pair, record the
exit, and manager-commit only a verified terminal pair. Exit 75 is a clean zero-work
deadline checkpoint to archive and resubmit, not a proof failure. Any other
nonzero exit is archived as failed and stops that campaign for audit.

Never delete, move, reuse, or overwrite permanent/staging/active result roots;
clear an active marker; replay useful work; or bypass a hard-stop incident. The
only automatic retry is the protocol's single authenticated pre-prompt system
failure. Useful-work, second-startup, token, time, rule, syntax, elaboration,
proof, and unverifiable incidents retain their frozen terminal semantics.
The accepted Ultra nested-submit boundary and token-limit endpoint may be
non-drained only when their exact frozen boundary/gate evidence authenticates
that state; never generalize those exceptions to ordinary attempts.

## Validate and report

Authenticate a complete result set before analysis, and analysis before report
rendering. Use the P01 checkpoint and pair-shard reporting paths only for their
declared scopes; never present a partial report as the complete matrix.

Report the requested stage, exact assignment/pair IDs, frozen identifiers,
commands, exit classifications, verified counts, result/evidence paths,
incidents, retries, and remaining gates. Distinguish a clean checkpoint,
unscored incident, failed proof, incomplete campaign, and complete authenticated
matrix. Never claim measurement readiness or publishability from file presence
alone.

Keep result roots and ledgers private under ignored scratch storage, with the
runbooks' restrictive permissions. Never stage or expose credentials, raw
rollout/provider data, immutable ledgers, private proofs, or result roots.
Preserve the frozen protocol disclosure: these are amended HighamBench-derived
measurements, not strict HighamBench 0.2, because of the signposted L prompt,
undemonstrated backend seed, lack of a frozen OCI image, and external provider
gate. Do not weaken that disclosure in reports.
