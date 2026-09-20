# HighamBench source-first formalization benchmark

This directory is the frozen Pilot-8 control plane. It does not use the legacy
fixed-target proof runner. Pilot-7 and earlier evidence remain sealed and are
never reinterpreted, resumed, or pooled with Pilot-8. Pilot-7's provider
qualification failed before any role completed; Pilot-8 is its fresh,
authentication-repaired successor.

Pilot ID: `formalization-benchmark-pilot-8`.

## Tasks

Pilot-8 supports 18 fresh N/L pairs:

- Paper tasks: `P01-T2`, `P02-T2`, `P03-T2`, `P13-T2`, `P14-T2`.
- Higham problems: `H22-11`, `H22-5`, `H20-6`, `H7-12`,
  `H20-9`, `H20-8`, `H23-6`, `H5-5`, `H10-7`, `H12-4`,
  `H19-5`, `H7-14`, `H15-3`.

The condition order is frozen in `config.json` and balanced nine N-first /
nine L-first. Each task has one official pair slot.

Both formalizers receive the same PDF, task packet, common prompt, Lean, and
Mathlib. L alone receives the read-only NumStability snapshot and the frozen
appendix that explicitly encourages discovery, import, reuse, adaptation, or
inspiration from the library. N has no direct or indirect NumStability
material.

The formalizer is `gpt-5.6-sol` at `xhigh`. Each condition has one initial
submission and at most three same-conversation repairs, a cumulative
18,000-second contestant-active threshold, and no token cap. The target proof
is deliberately `by sorry`; success is statement faithfulness.

## Audit

Every compiling candidate gets a recursively expanded, pseudonymized semantic
dossier and fresh blind, direct, and round-trip roles. Blind and direct outputs
must account for every `Dxxx` dependency. Both judges must complete all 16
semantic checks and both implication directions. Equivalent and genuinely
stronger candidates are faithful; weaker, different, restricted, vacuous, or
partial-case candidates are unfaithful.

An intermediate `undetermined` judge classification triggers a fresh
adjudicator. The final candidate verdict is always exactly `faithful` or
`unfaithful`; infrastructure failures are separate incidents.

See [PROTOCOL.md](PROTOCOL.md) for the complete frozen contract.

## Titan commands

After Pilot-8 is installed and provider-qualified on Titan:

```bash
~/.local/bin/run-highambench-formalization-pilot-8-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-8-r1 doctor --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-8-r1 qualify-provider --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-8-r1 run --task-id H22-11
~/.local/bin/run-highambench-formalization-pilot-8-r1 status --task-id H22-11
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
Setup also performs and records a clean full NumStability build under the same
eight-CPU/32-GiB/no-swap outer envelope. Build duration, GNU `time` metrics,
hardware/cgroup observations, complete output, source/object counts, and hashes
are authenticated under `runtime/library/build/` and excluded from contestant
measurements.

The controller never stages old targets, shared benchmark scaffolds, prior
audit history, Git history, or the other condition's output into a contestant
workspace.
