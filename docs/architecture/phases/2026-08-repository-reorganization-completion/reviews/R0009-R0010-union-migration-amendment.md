# R0009/R0010 union MIGRATION.md preimage amendment

Authority: `primary-human` (owner), who authorized completion of the
integration chain. Drafted by `claude-local`, which also performed the
integration; the owner is the independent reviewer of record.

## Defect

The reviewed R0009/R0010 common-base union
(`requests/R0009-R0010-union.patch`, SHA-256
`0D646D4658D0AEDBEDCDE397553B1AEF31662130545750DA27061299BD11545B`) pinned
every preimage to exact C0004 code
`783ae9a4951407ece046adb8631d5a8ff1795a18`. That anchor is correct for the 36
worker-facing paths, whose bytes at integration time equal their C0004 bytes.
It is wrong for `docs/architecture/MIGRATION.md`, a control-line document that
the C0004 acceptance commit (`131a0c6f333de0eb47a67698decf36ee82e01dab`) had
already rewritten before the union was frozen: the union pinned preimage blob
`80cbd5c4e635208cc7a7d058ae959d8745da8cf5`
(`1D9902DBC9C8AFB867DBDAD085F750E02E221A44CF5D8EBE090DF5FEEC780ABC`), but the
control line has carried a different blob from acceptance onward.

Applying the zero-context union at integration therefore placed the intended
nine-line "Planned Chapter 14 matrix-inversion compatibility completion"
section at a stale offset — inside the numbered migration-methodology list,
splitting item 4 from item 5 — and produced a document that matches neither
the frozen postimage
(`FEA9781677F28093430E34D6B45FB38EAA3A53552B457F620EB3B7FC11E62D21`) nor any
coherent reading. 36 of 37 union postimages verified byte-exact; only this row
failed.

## Change

Exactly one union row is re-anchored. The inserted section text is unchanged,
byte-for-byte, and every other union row is untouched:

* The section now sits between the R05/R06 retirement narrative and the
  numbered methodology list — the semantic position the frozen patch targeted
  in its stale coordinate system.
* `requests/R0009-R0010-union-postimages.tsv` row
  `docs/architecture/MIGRATION.md` is re-pinned to the control-line preimage
  blob `58a651b6528a5ce4048d163806e010e41290dc54`
  (`226D4E19DFDF28BBB29AEE8548A94D1AE7C613D586AFA717A6C306199FA4B1D4`) with
  postimage
  `CC990867A876342C255D093F5B32AA5D12E79F96A7CF4499FE6A877569D2198A`.
* The amended ledger hash
  `5863BBC2098493D221F3EF0DD50EA82874E50D1A2E7F720DDA4D340985FF67FE` replaces
  the frozen value in the B0008/B0009 `refresh.evidence` rows and is pinned in
  `check_completion_phase.py` as `C0005_UNION_AMENDED_LEDGER_SHA256`.
* `requests/R0009-R0010-union.patch` and its `patch_sha256` pin are NOT
  modified. The patch remains the historical as-reviewed artifact; the
  delivered-state ratchet still validates it by materializing all 37 paths
  from exact C0004 against the frozen postimages, and separately verifies the
  live tree against the amended row. The as-reviewed ledger likewise stays
  immutable in planned-control history, which the ratchet checks explicitly.

## Root cause and forward rule

This is the same failure class as the R05/R06 compatibility stop and the
B0009 import manifest: a frozen artifact anchored to the wrong baseline for
one member of its path set, undetected because the other members were correct.

Forward rule: a shared-request union must anchor control-line documents
(`README.md`, `docs/architecture/MIGRATION.md`, phase narratives) to the
control tip at freeze time rather than to the worker base checkpoint, or
exclude them from zero-context patches entirely in favour of an explicitly
anchored section append.
