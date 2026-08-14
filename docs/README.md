# Documentation map

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
   contract. Its current checkpoint is C0003 at exact green code commit
   `e20de2f931caa12221e708c341e9cb4f64d29b25`; M03/R03 is accepted/applied,
   B0005 is accepted with retirement due, and P0005 is retired. Meanwhile, 254
   production modules and 310 distinct debt rows remain. Bounded-phase
   and repository-wide completion therefore remain incomplete. M05/M06 are
   ready, M07 and every other unaccepted milestone remain planned, and no
   successor wave is activated. Dated worker packets do not override it.

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
