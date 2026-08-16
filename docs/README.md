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
   contract. Its current checkpoint is C0004 at exact green code commit
   `783ae9a4951407ece046adb8631d5a8ff1795a18`; Lean CI run 31962707569
   (job 95203051003) passed. M05/R05 and M06/R06 are accepted,
   B0006/B0007 are accepted with retirement due, P0006/P0007 are retired, and
   R0006/R0007/R0008 are applied. The temporary operator expansion and wave
   reservations are released. M04/R04 and M08/R08 are ready; every other
   unaccepted milestone remains planned and no successor wave is activated.
   Retirement awaits acceptance-control CI, so both exact delivery refs and
   named worktrees remain present. The official baseline, inventory, and
   111-path ledger SHA-256 values are
   `D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
   `08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
   and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`.
   Bounded-phase and repository-wide completion remain incomplete with 200
   debt rows: 191 unclassified modules, 125 noncanonical names, and eight
   declaration-bearing umbrellas. Dated worker packets do not override it.

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
