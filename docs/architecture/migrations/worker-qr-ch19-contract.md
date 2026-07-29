# QR / Chapter 19 frozen ownership contract

This contract freezes the QR lane before any declaration move.  The working
base is published `main` commit
`420e4f93e2a5d31b2bf5b73740ca4146de7b0921`; the external packet's immutable
semantic stream was produced at
`6487fc33088523b8f27ecde9ad613515b78f9977`.  The only QR source change between
those revisions is the accepted `Higham19WYApplicationClosure` import repair:
the current owner imports
`NumStability.Analysis.FirstOrder.AsymptoticFamilies`, and this contract rejects
reintroduction of the old `BlockLUFirstOrderFamilies` compatibility import.

## Reproducible baseline

- Lean toolchain: `leanprover/lean4:v4.29.0-rc3`.
- Mathlib revision: `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.
- Production source inventory: 1,173 modules, 1,470,227 physical lines,
  69,623,707 bytes, 3,740 direct internal import edges, and no import cycle.
- Pristine `lake build NumStability`: passed, 4,942 jobs.
- Frozen format-2 stream: 115,724,349 bytes, SHA-256
  `32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563`.
- Packet archive SHA-256:
  `1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED`.
- External pristine inputs are retained below
  `C:\Users\qed_s\higham-evidence\qr-householder-wave1-base`; the tracked
  frozen-owner manifest records the Git blob, source SHA-256, line counts,
  `.ilean` SHA-256, and `.ilean` byte count for every owner.

The contract selects exactly 3,991 declarations in all 59 packet owners.  It
routes them through 3,331 immutable source-command groups into 60 reviewed
destinations.  The destination DAG contains 374 typed destination edges
(163 signature and 211 body/proof pairs, representing 12,159 declaration-edge
instances) and is acyclic.  The frozen source-import graph contains 184 direct
imports.

Lean omits the two `alias` commands in
`Higham19Theorem6ActualSource.lean` from that module's `.ilean` declaration
map.  They are not silently exempted: the checker parses their exact two-line
source spans and pins both command hashes in
`qr-ch19-alias-commands.tsv`.  Neither alias belongs to Householder Wave 1.

## Householder Wave 1 selector

The first dependency-closed wave has exactly eleven historical owners, twelve
destinations, 1,040 declarations, and 821 immutable command groups.  It has 15
ordinary private declarations and no cross-destination private helper, hence
requires 15 explicit private-name rewrites and zero public promotions.  The
only source-tier command is
`NumStability.H19_Lemma19_1_construction2_backward_error`, routed to
`NumStability.Source.Higham.Chapter19.Lemma01.Construction2`; every other wave
command is source-neutral and remains in its matching reusable Householder
leaf.

## Tracked artifacts

| Artifact | SHA-256 |
| --- | --- |
| `qr-ch19-frozen-owners.tsv` | `FDDB8E5B2A82E9DC444EB6EFF5D487321A4C100AEF9EEEA0AA305997FBA24E97` |
| `qr-ch19-routes.tsv` | `C80E0E148B32E685F2FA6BB562A1E5BDD61A8CC57ED9407C679CF12312FE8049` |
| `qr-ch19-ownership.tsv` | `4B1478DBBE114E11AF60C324C51DF5CFAABDF496EEF5E82B4421F4C1860D7A88` |
| `qr-ch19-destination-dag.tsv` | `AEB775C6EA26883D693DCC4215D4843747F32FFE4B68EA061DE55A98002CD56F` |
| `qr-ch19-source-imports.tsv` | `DB728C58710A22A6AB4E0E82CE8767E0B1CA49120103AFE8EF73DFE5241B0E74` |
| `qr-ch19-alias-commands.tsv` | `F8369BE36422328DB1A2ABC1BBEAA2B79C6B5A7CD7A937F5D2FC760962E51944` |
| header-only `qr-ch19-private-rewrites.tsv` | `F0295F15DC97FA62F34C6460488B48FE0346D127B89364B3ADE0B938420DBBB9` |

`check_qr_ch19_ownership.py --self-test` passes its negative tests.  Two
independent pre-gate reads of the committed-style artifacts reproduce the
59 / 3,991 / 3,331 full-lane counts and the 1,040 / 821 / 15 / 0 Householder
counts.  The pre gate also re-hashes every pristine source, `.ilean`, command
span, direct import, ownership row, alias span, and typed destination edge.
