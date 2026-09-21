# HighamBench source-first formalization benchmark

This directory is the frozen Pilot-13 warm-start control plane. It does not use
the legacy fixed-target proof runner. Pilot-12 and earlier evidence remain
sealed and are never reinterpreted, resumed, or pooled with Pilot-13. Pilot-9
observations are retained as L-cold evidence. Pilot-11 produced a valid,
task-neutral warm root, but its first H22-11 L fork failed before `turn/start`
because the controller rejected exact inherited-history usage telemetry.
Pilot-12 corrected that boundary, then exposed a second provider-interface
fact: warm forks emit exact per-response cumulative/`last` token notifications
but no `rawResponse/completed` usage events. Its H22-11 run is sealed as a
telemetry incident. Pilot-13 admits that exact notification surface under
strict cross-checks and qualifies it with a real off-benchmark warm fork.

Pilot ID: `formalization-benchmark-pilot-13`.

## Tasks

Pilot-13 supports 18 fresh N/L pairs:

- Paper tasks: `P01-T2`, `P02-T2`, `P03-T2`, `P13-T2`, `P14-T2`.
- Higham problems: `H22-11`, `H22-5`, `H20-6`, `H7-12`,
  `H20-9`, `H20-8`, `H23-6`, `H5-5`, `H10-7`, `H12-4`,
  `H19-5`, `H7-14`, `H15-3`.

The condition order is frozen in `config.json` and balanced nine N-first /
nine L-first. Each task has one official pair slot.

Both formalizers receive the same PDF, task packet, common task prompt, Lean,
and Mathlib. Before tasks begin, L performs exactly one task-neutral library
scout. Every L task is a genuine independent fork of that frozen root and has
read-only NumStability access. N has no direct or indirect NumStability
material.

The formalizer is `gpt-5.6-sol` at `xhigh`. Each condition has one initial
submission and at most three same-conversation repairs, a cumulative
18,000-second contestant-active threshold, and no token cap. The target proof
is deliberately `by sorry`; success is statement faithfulness.

## Audit

Every compiling candidate gets a recursively expanded, pseudonymized semantic
dossier and fresh blind, direct, and round-trip roles. Blind and direct outputs
must account for every ordered `Dxxx` dependency; their accompanying names are
human-readable labels, not identity fields. Both judges must complete all 16
semantic checks and both implication directions. Equivalent and genuinely
stronger candidates are faithful; weaker, different, restricted, vacuous, or
partial-case candidates are unfaithful.

An intermediate `undetermined` judge classification triggers a fresh
adjudicator. The final candidate verdict is always exactly `faithful` or
`unfaithful`; infrastructure failures are separate incidents.

See [PROTOCOL.md](PROTOCOL.md) for the complete frozen contract.

## Titan commands

After Pilot-13 is installed and provider-qualified on Titan:

```bash
~/.local/bin/run-highambench-formalization-pilot-13-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-13-r1 doctor --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-13-r1 qualify-provider --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-13-r1 run --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-13-r1 status --task-id H22-11
```

`run --dry-run` checks admission and staging without model calls or consuming
an official pair. Installation and qualification never authorize an official
run; a measured pair starts only after an explicit user request for that task.

Natural-language examples:

```text
Run benchmark for H22-11
Run benchmark for H5-5
Run benchmark for P03-T2
```

## Private inputs and build evidence

The 18 source PDFs are private and are matched by basename and SHA-256 from
`manifest.json`. Reused chapter PDFs are stored once in the deployment.
Pilot-13 authenticates and directly reuses Pilot-11's clean full NumStability
build under the same eight-CPU/32-GiB/no-swap outer envelope. Its build
duration, GNU `time` metrics, hardware/cgroup observations, complete output,
source/object counts, and hashes remain the one build record for this frozen
library snapshot. Pilot-13 records zero new library builds and zero new scout
turns.

The controller never stages old targets, shared benchmark scaffolds, prior
audit history, Git history, or the other condition's output into a contestant
workspace.
