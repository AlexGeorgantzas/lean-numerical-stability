# HighamBench formalization benchmark - Pilot 15

Pilot 15 is the proof-required, retrieval-indexed successor to Pilot 14. All
Pilot 14 and earlier runs remain sealed evidence and are never resumed,
rewritten, or pooled with Pilot 15.

Pilot ID: `formalization-benchmark-pilot-15`.

## What changed

- The audited statement is still the primary scientific object, but every
  candidate must now include a complete kernel-checked proof. No `sorry`,
  `admit`, new axiom/constant, `opaque`, `unsafe`, or checker bypass is allowed.
- Condition L receives a deterministic, task-neutral declaration atlas at
  `/library-index` and `LIBRARY_GUIDE.md`. It must search this compact surface
  before recursively scanning source and must reuse compatible declarations.
- Exact declaration hits have a bounded `show.py` API/source view. The guide
  tells L to stop broad discovery, compile a minimal library wrapper first, and
  add only paper-specific bridges afterward.
- Exact duplicate provider token-usage notifications are recorded as
  idempotent repeats. Changed duplicates and genuine usage disagreements still
  fail closed.
- The atlas is generated once at installation from the already frozen
  NumStability source. Pilot 15 performs no new library build and no new scout
  turn; it inherits the one frozen task-neutral warm root.
- Each submission records imports, raw and non-comment code lines, declaration
  count, reached NumStability declarations/modules, and atlas/source-search
  telemetry. These private treatment metrics never reach the blind auditors.
- H00-00 is a one-page synthetic end-to-end canary and is explicitly excluded
  from scientific results.

## Conditions

- N: frozen Lean 4 and Mathlib, no NumStability source, OLean, atlas, guide, or
  warm conversation.
- L: the identical task prompt, PDF, hardware, Lean, and Mathlib, plus the
  frozen NumStability OLean/source trees, inherited task-neutral warm root, and
  declaration atlas.

Both formalizers use `gpt-5.6-sol` at `xhigh`. Fresh, stateless, condition-blind
audit roles use `gpt-6-astra` at `high`.

## Tasks and effect gate

There are 19 fresh one-shot pair slots: the previous 18 paper/Higham tasks plus
H00-00. The predeclared primary effect set is H5-5, H7-12, H10-7, and H23-6.

The Pilot-15 gate passes only when all four pairs complete with both conditions
faithful, at least three tasks have lower L active time, median L active-time
reduction is at least 20%, and median L net-new-token reduction is at least
20%. H00-00 never contributes to this calculation.

## Titan commands

```bash
~/.local/bin/run-highambench-formalization-pilot-15-r1 verify-release
~/.local/bin/run-highambench-formalization-pilot-15-r1 doctor --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-15-r1 qualify-provider --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-15-r1 run --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-15-r1 status --task-id H00-00
~/.local/bin/run-highambench-formalization-pilot-15-r1 evaluate-gate
```

Each `(pilot_id, task_id)` can consume exactly one official N/L pair. Repairs
continue in the same condition conversation, for at most four submissions
(initial plus three repairs), under one cumulative five-hour active-time budget
and no benchmark token cap.

See [PROTOCOL.md](PROTOCOL.md), [ARCHITECTURE.md](ARCHITECTURE.md), and
[deployment/TITAN.md](deployment/TITAN.md).
