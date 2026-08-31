# Documentation map

This directory separates current policy from dated evidence and source-audit
history. When two documents disagree, use the precedence order below.

The operative reorganization process is
[`architecture/PROCESS.md`](architecture/PROCESS.md): per-batch static gates,
plain-language recorded review, and fast-forward-only `main`. The bounded
worker lifecycle was retired by the primary human's recorded 2026-08-30
cutover decision. C0008 (exact code commit
`897557779a2102aa0e23b0b2f63edeb35b06bc68`) is the current accepted
checkpoint: it accepts milestone M13 with its I01 wave, whose reviewed
R0014/R0015 union was applied on `main` at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0`, after which the live tree records
2,928 production modules: 2,928 classified, 0 unclassified, and 0 mixed, with
zero noncanonical names and zero declaration-bearing umbrellas. Bounded-phase
completion is recorded complete with C0008 as its evidence checkpoint;
repository-wide completion remains incomplete. The normative current-state summary and measurements
are recorded in the
[`C0007 governance reconciliation`](architecture/phases/2026-08-repository-reorganization-completion/reviews/C0007-governance-reconciliation.md).

## Archived chronology

C0005 accepted M04/R04 and M08/R08 at exact integrated code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`. Its generated evidence records
2,818 production modules: 2,685 classified, 133 unclassified, and 0 mixed. M04
and M08 were accepted and M07 was ready. B0010/R07 was delivered at
`2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` and its code was integrated on
`main` at `b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5` under exact R0011 and the
reviewed supplemental correction, after which the live tree recorded 2,860
production modules: 2,770 classified, 90 unclassified, and 0 mixed. R09 and R10
were then integrated at `09512c1b15fd4f6892a313341b1edc8c02bb913d`, after which
the live tree recorded 2,927 production modules: 2,927 classified, 0 unclassified,
and 0 mixed, with zero noncanonical names.
Checkpoint C0006 (exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`) is accepted: M07 is accepted,
B0010 is accepted with retirement due, P0010 is retired, and R0011 is
applied.

Checkpoint C0007 (exact code commit
`4e26820d1f4989ec4ec77b7113085f593570e11b`, green on Lean CI run 32794282084)
is accepted: M09 and M10 are accepted, B0011 and B0012 are accepted with
retirement due, P0011 and P0012 are retired, and R0012 and R0013 are applied as
the reviewed 25-path union. The reserved I01 wave open at C0007 acceptance has
since landed as the R0014/R0015 integration recorded above; branch retirement
remains a separate later control.

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
   contract. Its current checkpoint is C0008 at exact code commit
   `897557779a2102aa0e23b0b2f63edeb35b06bc68`, accepting M13/I01 on top of
   C0007 at exact code commit
   `4e26820d1f4989ec4ec77b7113085f593570e11b`, which accepted the R09/R10
   epoch on top of C0006 at exact integrated code commit
   `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`. M04/R04 and M08/R08 are
   accepted; P0008/P0009 are retired evidence, R0009/R0010 are applied, and the
   temporary operator expansion and wave reservations are released. M07 is
   accepted: B0010/R07 was activated, delivered, and integrated on `main`, and
   C0006 accepted M07, accepted B0010 with retirement due, retired P0010, and
   applied R0011.
   The rest of this item is dated acceptance evidence retained for provenance.
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
   records the exact cleanup evidence. The C0004 baseline, inventory, and
   111-path ledger SHA-256 values remain pinned at
   `D3F30A410903B1CA2858951CB26107B94B62630BC424723A0EC9EDF484AEDDDF`,
   `08FA3E41DA0C72E7F5D4ECFD315F0CC6C73EB0F45089CF1DAC6AB04A81A1E326`,
   and `E5F12E1834F848C7A2FAAD674BBDEEC0B3760B44BE17D073460E87F3E437F378`;
   the accepted C0005 baseline and inventory supersede them at
   `2FC0C95FFECF114A2EDB8C14DB8C2874BDBB85FCEBA722C345AA084B3E97C02A` and
   `7C383B1AF57F65F9559C81402013412172CC93B623F7ED2E26968B9C7AFB4172`.
   Bounded-phase completion is recorded complete at C0008; repository-wide
   completion remains incomplete. After the R09/R10 integration and the
   subsequent R0014/R0015 landing, the live tree measures 0 unclassified
   modules, 0 noncanonical names, and 0 declaration-bearing umbrellas. Dated worker packets do not override the
   active phase contract.

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
