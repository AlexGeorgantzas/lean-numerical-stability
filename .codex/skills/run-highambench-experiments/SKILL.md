---
name: run-highambench-experiments
description: Operate Pilot-9 of the source-first HighamBench faithful-formalization benchmark for one frozen paper task or Higham problem. Use when the user says "Run benchmark for H22-11", "Run benchmark for P01-T2", or asks to preflight, run, resume, validate, or report exactly one N/L pair. Do not use for the legacy fixed-target proof benchmark or task construction.
---

# Run HighamBench Formalization Experiments

## Scope

Pilot-9 (`formalization-benchmark-pilot-9`) is a separate frozen release.
Pilots 1--8 and all of their runs, incidents, and deployment records are
read-only predecessor evidence. Never reinterpret an older decision, resume an
older sealed condition, pool results across pilots, or use an older launcher as
a substitute. Pilot-8's H22-11 attempt is sealed as an audit-interface
incident; Pilot-9 corrects that interface mismatch without reusing its result.

Preparing, installing, repairing, or qualifying Pilot-9 never authorizes an
official pair. Run one only after an explicit request naming exactly one task.

The allowlist is:

- `P01-T2`, `P02-T2`, `P03-T2`, `P13-T2`, `P14-T2`
- `H22-11`, `H22-5`, `H20-6`, `H7-12`, `H20-9`, `H20-8`
- `H23-6`, `H5-5`, `H10-7`, `H12-4`, `H19-5`, `H7-14`, `H15-3`

A request such as `Run benchmark for H22-11` authorizes exactly one N/L pair
for H22-11. It does not authorize repetitions or other tasks.

The benchmark scores a compiling, source-faithful Lean proposition, not its
proof. The unique root theorem must end in `by sorry`; that is the only allowed
placeholder.

## Load the frozen contract

Before any provider call or benchmark-state mutation:

1. Read [the operations reference](references/operations.md) completely.
2. Require
   `~/.local/bin/run-highambench-formalization-pilot-9-r1` and its distinct,
   digest-bound deployment record.
3. Run provider-free `verify-release`.
4. Run provider-free `doctor --task-id <TASK>` through that launcher.
5. Require authenticated PDF, packet, prompts, runtime, NumStability build
   evidence, executables, hardware, predecessor lineage, and account-global
   registry/locks.
6. Require the one-shot off-benchmark live qualification for the exact models,
   reasoning efforts, all four audit output schemas, workspace read paths,
   formalizer write path, and Code Mode host.
7. Stop on any missing or failed gate. Never fall back to
   `paper_bencmark/highambench/tools/runner.py`, `run_matrix.py`, or an older
   launcher.

The installed release is authoritative. Command-line values are equality
assertions, not experimental knobs. Never regenerate hashes or modify controlled
inputs during admission or measurement.

Agent delegation must be disabled globally and per thread. Collaboration or
foreign-thread events are provider incompatibilities, not contestant
misconduct. Doctor and dry-run are provider-free; qualification usage is not
charged to N or L.

## Preserve the N/L treatment

N and L receive byte-identical PDFs, packets, common prompts, Lean, and Mathlib.
The packet contains neutral source clarification, locations, and hashes, but no
old Lean target, shared task scaffold, proof, prior audit, or NumStability name.

N must have no tool-visible NumStability source, object, cache, index,
documentation, history, environment value, or path.

L adds the frozen NumStability source and compiled snapshot. Append only the
frozen L message, which explicitly encourages inspection, import, reuse,
adaptation, or inspiration. It points to `/library/NumStability`,
`/library/NumStability.lean`, compiled declarations on `LEAN_PATH`, and
concrete `find`, `rg`, and import examples.

## Enforce the loop

Use one fresh persistent formalizer conversation per condition. Permit four
immutable submissions: initial plus three repairs. Every frozen submission
consumes a slot, including compile/integrity failures.

For each attempt:

1. start metering immediately before `turn/start`;
2. stop the model-active interval only after contestant processes are quiescent;
3. settle telemetry and trusted bookkeeping off-clock;
4. time and charge the stable candidate copy/hash separately;
5. compile and validate off-clock;
6. build the recursive pseudonymized semantic dossier off-clock;
7. run fresh blind, direct, and round-trip roles;
8. adjudicate only on a frozen trigger;
9. if unfaithful and a slot remains, freeze neutral feedback and deliver it to
   the same formalizer conversation immediately after metering resumes.

The blind translator and direct judge must each account for every `Dxxx`
dependency in order. `Dxxx` is the identity; the required `name` is a
human-readable semantic label and need not reproduce the dossier label. Both
judges must complete S01--S16 and both implication
directions. Equivalent and genuinely stronger candidates are faithful. Weaker,
different, restricted, vacuous, or partial-case candidates are unfaithful. An
intermediate undetermined classification mandates adjudication; the final
candidate outcome is only faithful or unfaithful. Infrastructure failures are
separate incidents.

Use 18,000 cumulative contestant-active seconds per condition. Preserve any
overshoot and terminate unscored as `ACTIVE_TIME_LIMIT`. There is no token
cap; record exact token use rather than stopping on count. Validator and audit
overhead never enter contestant metrics.

## Execute fail closed

Normalize the task ID and require an exact allowlist match. Use only the
source-first command in the operations reference. The trusted runner must own
prompt delivery, metering, freeze, validation, audit, feedback, conversation
continuation, and state transitions.

Never edit, delete, overwrite, or reuse run directories, snapshots, ledgers,
hashes, audit decisions, or active markers. Use provider-free `status` for
inspection. Reissue `run` only to retrieve a terminal result or continue at an
advertised safe boundary before the first turn or between sealed conditions.
A submitted condition cannot be cold-resumed without its live raw-usage stream.

Stop on missing telemetry, hash mismatch, unresolved source ambiguity,
evaluator incident, unsupported transition, or isolation failure.

## Report observable evidence

Report the task, pair ID, condition order, release identifiers, admission,
terminal statuses, submission counts, active time, contestant tokens,
validation/audit overhead, classifications, and artifact paths. Keep the
one-time NumStability build metrics separate from contestant clocks.

Never request or claim hidden chain-of-thought. Report only visible messages,
API-exposed reasoning summaries, provider token fields, tool events, commands,
outputs, candidate snapshots, audit artifacts, and authenticated hashes. Redact
credentials and restricted system/developer material.
