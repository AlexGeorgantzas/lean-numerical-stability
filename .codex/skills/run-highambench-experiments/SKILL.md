---
name: run-highambench-experiments
description: Operate the source-first HighamBench faithful-formalization pilot for P01-T2, P02-T2, P03-T2, P13-T2, or P14-T2. Use when the user says "Run benchmark for P01-T2" or asks to preflight, run, resume, validate, or report exactly one N/L formalization pair. Do not use for the legacy fixed-target proof benchmark, task construction, or a wider campaign.
---

# Run HighamBench Formalization Experiments

## Scope

This is pilot-3 (`formalization-benchmark-t2-pilot-3`). Pilot-1 and pilot-2 are
sealed, unscored predecessors. Pilot-2 P01-T2 stopped after N submitted one
compiling candidate: the provider rejected a blind-auditor response schema,
no faithfulness verdict was produced, and L never started. Preserve both older
deployments and incidents; never reuse their launchers or run IDs, resume their
P01-T2 pairs, or pool their data with pilot-3. All five pilot-3 tasks begin as
fresh single pairs under one frozen release.

Preparing or qualifying a repaired release does not authorize an official
pair. Run one only in response to an explicit task-run request.

Treat a command such as `Run benchmark for P01-T2` as authorization to run
exactly one Condition N run and one Condition L run for that named task.
The pilot allowlist is exactly:

- `P01-T2`
- `P02-T2`
- `P03-T2`
- `P13-T2`
- `P14-T2`

Reject any other task or request for repetitions unless the frozen protocol and
manifests have first been deliberately revised outside measurement. Never
expand a one-task request into the five-task pilot. Do not create three
repetitions: this pilot has one N/L pair per task.

This benchmark measures production of a compiling, source-faithful Lean
formalization. It does not ask for or score a proof. The designated root theorem
must have proof body `by sorry`; that root `sorry` is the only permitted
placeholder in the complete candidate.

## Load the frozen contract

Before any provider call or benchmark-state mutation on Titan:

1. Read [the operations reference](references/operations.md) completely.
2. Use only the installed `~/.local/bin/run-highambench-formalization-pilot-3-r1`
   launcher. Its deployment record binds the exact release checkout, so the
   command works regardless of the current directory.
3. Run the launcher's provider-free `verify-release` command.
4. Authenticate the selected packet, prompts, runtime snapshots, executable
   identities, deployment record, and hardware through the installed
   launcher's `doctor` gate.
5. Require the pilot-1/pilot-2 predecessor lineage and account-global registry
   to authenticate. A fresh official `run` requires an off-benchmark
   provider-backed qualification before any pair slot is created. Besides
   single-agent capability, it must exercise the exact frozen output schemas
   for blind translation, direct judgment, round-trip judgment, and
   adjudication through live provider calls.
6. Stop if any gate is absent or fails. Never use legacy
   `paper_bencmark/highambench/tools/runner.py` or `tools/run_matrix.py` as a
   substitute.

The installed release's protocol and frozen manifests are authoritative. Treat command-line values
as equality assertions, not experimental knobs. Never repair, refresh, or
silently regenerate controlled inputs during admission or measurement.

The exact provider capability contract disables `agents.enabled`,
`multi_agent`, and `multi_agent_v2`. Require effective global/thread
attestations and reject collaboration or foreign-thread events as provider
infrastructure incompatibility, not contestant misconduct. The deprecated
`multiAgentMode` value is not evidence of this capability. `doctor` and
`run --dry-run` remain provider-free; the qualification usage is never charged
to N or L. Local JSON-schema validation alone does not replace the live
provider-schema check that pilot-2 lacked.

## Preserve the N/L treatment

N and L receive byte-identical paper packets and byte-identical common base
prompts. The packet identifies the exact paper result and accompanies its
frozen PDF with locators, neutral clarification, scope constraints, and hashes.
It must not expose
an old HighamBench target, task-specific common Lean scaffold, gold theorem,
gold proof, prior audit output, or NumStability declaration hint.

The common prompt must say that the exact result is required, faithfulness is
known to be achievable, the statement will be independently audited, and the
formalizer should check every supporting definition before submitting.

Condition N receives only the frozen Lean/Mathlib environment and neutral
harness. Verify that NumStability is absent from every tool-visible source,
object, cache, index, history, environment variable, and filesystem path.

Condition L receives that same environment plus the frozen NumStability source
and compiled snapshot. Append only the frozen L treatment message, which must
explicitly encourage the formalizer to inspect, import, reuse, adapt, or draw
inspiration from relevant NumStability material while still satisfying the
source contract. The measured treatment is library availability plus this
explicit encouragement. The frozen appendix identifies
`/library/NumStability`, `/library/NumStability.lean`, and `LEAN_PATH`, and gives
concrete `find`, `rg`, and `import NumStability` discovery/import examples.

## Enforce the submission and audit loop

Use one fresh persistent formalizer conversation per condition. Each condition
allows at most four total submissions: the initial candidate plus at most three
repairs. Every submission consumes a slot, including a compile- or
integrity-invalid candidate.

For each attempt, start the model-active interval immediately before the
`turn/start` RPC and stop it after post-terminal cleanup proves the contestant
process tree is quiescent. Ordered telemetry settling and trusted bookkeeping
are off-clock. Separately time and charge the stable candidate copy/hash, then
run compilation and integrity checks off-clock. A valid, previously unaudited
semantic candidate receives a fresh, stateless, condition-blind and
attempt-blind faithfulness audit. If rejected and a submission remains, freeze
condition-neutral feedback and deliver it to the same formalizer conversation;
resume metering immediately before delivery.

Use 18,000 cumulative contestant-active seconds across all four submissions as
the termination threshold. Any timer or final-candidate-freeze overshoot is
measured rather than clamped and yields the unscored `ACTIVE_TIME_LIMIT`
outcome; no accepted or otherwise scored condition may exceed the threshold.
There is no benchmark token cap: record contestant tokens as an outcome and
never stop a run because of their count. Validator, audit, adjudication, and
feedback-rendering time and tokens belong to separate overhead ledgers and do
not affect the contestant metrics.

## Execute fail closed

Normalize the requested ID, require an exact allowlist match, and run only the
source-first pair command documented in the operations reference. Require the
runner to own prompt publication, process-tree metering, candidate freezing,
validation, audit handoff, feedback publication, persistent-conversation
continuation, and terminal state. Do not simulate these boundaries with manual
timestamps or copied chat messages.

Do not overwrite, delete, reuse, or hand-edit run directories, snapshots,
hashes, ledgers, attempt counters, audit decisions, or active markers. Use the
provider-free `status` command for inspection. Reissue the same authenticated
source-first `run` command only to intentionally retrieve an existing terminal
result or continue before the first turn or between sealed conditions.
A submitted condition cannot be cold-resumed because its exact raw usage stream
belongs to its live app-server process. Stop on
missing telemetry, a hash mismatch, source ambiguity, an evaluator incident,
an unsupported CLI transition, or any condition-isolation failure.

## Report observable evidence only

Report the task, pair/run IDs, condition order, frozen identifiers, admission
result, terminal status, submission count, active time, contestant tokens,
validation/audit overhead, classifications, and artifact paths. Distinguish
`faithful`, `attempt_limit`, `time_limit`, validation failure, audit-system
incident, infrastructure incident, and invalid telemetry.

When setup status or deployment provenance is in scope, also report the
authenticated NumStability clean-build record and its hardware envelope. Keep
that one-time wall/CPU/resource measurement explicitly separate from every
contestant clock; its record, complete build output, and raw GNU `time` output
live under the private deployment's `runtime/library/build/` directory.

Never request, expose, reconstruct, store, or claim to have recorded hidden
chain-of-thought. The allowed trace comprises visible messages, exposed
reasoning summaries when the interface provides them, provider-reported input,
cached-input, cache-write-input, output, reasoning-output, and total token
counts, tool calls, commands, outputs,
candidate snapshots, and audited artifacts. Redact
credentials and restricted system/developer material from user-facing reports.
