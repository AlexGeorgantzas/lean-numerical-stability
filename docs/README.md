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

## Historical reports

Documents whose names begin with `SPLIT`, `RENAME`, or a dated broad-audit
label record how the formalization was produced. They may cite historical
module paths. Keep them for provenance, but do not use them as current import
guidance.
