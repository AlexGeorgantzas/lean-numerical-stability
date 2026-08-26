# Documentation map

The current accepted checkpoint is C0007 at code
`4e26820d1f4989ec4ec77b7113085f593570e11b`. The executable inventory covers
2,927 of 2,927 production modules with zero unclassified, mixed, or
noncanonical modules. M13/I01 is planned with exactly twelve modules;
bounded-phase and repository-wide completion are both incomplete.

## Archived checkpoint synopsis

The following C0005-C0007 synopsis is retained as historical evidence. It does
not override the current policy section below.

C0005 accepts M04/R04 and M08/R08 at exact integrated code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`. Its generated evidence records
2,818 production modules: 2,685 classified, 133 unclassified, and 0 mixed. M04
and M08 are accepted and M07 is ready. B0010/R07 is delivered at
`2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` and its code is integrated on
`main` at `b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5` under exact R0011 and the
reviewed supplemental correction, after which the live tree recorded 2,860
production modules: 2,770 classified, 90 unclassified, and 0 mixed. R09 and R10
were then integrated at `09512c1b15fd4f6892a313341b1edc8c02bb913d`, after which
the live tree records 2,927 production modules: 2,927 classified, 0 unclassified,
and 0 mixed, with zero noncanonical names.
Checkpoint C0006 (exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`) is accepted: M07 is accepted,
B0010 is accepted with retirement due, P0010 is retired, and R0011 is
applied.

Checkpoint C0007 (exact code commit
`4e26820d1f4989ec4ec77b7113085f593570e11b`, green on Lean CI run 32794282084)
is accepted: M09 and M10 are accepted, B0011 and B0012 are accepted with
retirement due, P0011 and P0012 are retired, and R0012 and R0013 are applied as
the reviewed 25-path union. The remaining queue is exactly I01=12; branch
retirement remains a separate later control.

This directory separates current policy from dated evidence and source-audit
history. When two documents disagree, use the precedence order below.

## Current repository policy

1. [`../ARCHITECTURE.md`](../ARCHITECTURE.md) defines public layers and entry
   points.
2. [`architecture/NAMING.md`](architecture/NAMING.md) defines module placement
   and naming.
3. [`../CONTRIBUTING.md`](../CONTRIBUTING.md) defines required checks.
4. [`architecture/TIERS.md`](architecture/TIERS.md) and
   [`architecture/COMPATIBILITY.md`](architecture/COMPATIBILITY.md) define the
   reviewed tier and forwarding-path contracts.
5. [`architecture/PROVENANCE.md`](architecture/PROVENANCE.md) defines the
   per-file licensing and upstream-attribution policy.
6. [`architecture/phases/2026-08-repository-reorganization-completion/`](architecture/phases/2026-08-repository-reorganization-completion/README.md)
   is the active repository-wide scope, authority, wave, checkpoint, and branch
   contract. Its current checkpoint is C0007 at exact code commit
   `4e26820d1f4989ec4ec77b7113085f593570e11b`. M09/M10 are accepted;
   B0011/B0012 are accepted with retirement due; P0011/P0012 are retired; and
   R0012/R0013 are applied. The exact remaining bounded wave is M13/I01=12.
   Both bounded-phase and repository-wide completion remain incomplete.

## Current source coverage

- [`source_coverage/`](source_coverage/) contains the concise per-chapter
  coverage ledgers.
- `chapterNN/` directories contain detailed inventories, proof-source ledgers,
  formalization reports, and explicitly deferred claims for selected chapters.
- [`LIBRARY_LOOKUP.md`](LIBRARY_LOOKUP.md) is a large navigation index. It is
  not the authority for module placement; canonical paths come from the
  architecture and compatibility documents above.

## Migration and generated evidence

- [`architecture/migrations/`](architecture/migrations/) records reviewed path
  changes and their verification evidence.
- [`architecture/baselines/`](architecture/baselines/) contains immutable,
  dated architecture snapshots. Do not edit an older baseline to describe the
  current tree; generate a new snapshot.
- [`architecture/reviews/`](architecture/reviews/) records bounded design and
  outlier reviews.
- [`architecture/phases/`](architecture/phases/) contains active and retained
  machine-validated operating contracts. The active phase has precedence over
  historical handoffs.

## Historical reports

Documents whose names begin with `SPLIT`, `RENAME`, or a dated broad-audit
label record how the formalization was produced. They may cite historical
module paths. Keep them for provenance, but do not use them as current import
guidance.
