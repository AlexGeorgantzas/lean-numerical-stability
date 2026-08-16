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
   P0006/P0007 are retired, and R0006/R0007/R0008 are applied. The temporary
   operator expansion and wave reservations are released. M04/R04 and M08/R08
   are ready; every other unaccepted milestone remains planned and no successor
   wave is activated.
   Acceptance-control commit `131a0c6f333de0eb47a67698decf36ee82e01dab`
   passed Lean CI run 31966141900 (job 95211495907); `primary-human` retired
   B0006/B0007 at `2026-08-16T19:08:57Z`. Both exact remote refs were deleted
   atomically under expected-tip leases and verified absent. The archive root
   `C:\Users\qed_s\higham-worktrees\retired-worker-artifacts\C0004-R05-R06-20260816`
   contains five verified R05 files totaling 117,327,061 bytes; R06 had no
   material artifacts. Named worktrees `completion-r05-claude` and
   `completion-r06-codex` were removed without force with no residue. Local
   branches remain at
   `26e89100b3c7c8a64a41426d517cbd563a40db72` and
   `bfaf2ae917ed79165caa6cc58b3782984aa8d3d9`. The
   [`R05/R06 retirement review`](architecture/phases/2026-08-repository-reorganization-completion/reviews/R05-R06-retirement.md)
   records the exact cleanup evidence. The official baseline, inventory, and
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
