# R04 delivery summary

Wave `R04` (Cholesky / Higham Chapter 10), branch record `B0008`,
lane `claude-lane`, operator `claude-local` (per the reviewed
`R04-operator-redesignation-amendment.md`, control commit
`8cbfbe984469024725b5ba8781d8fc3dab0935a4`, Lean CI run 32235392913),
base checkpoint `C0004` `783ae9a4951407ece046adb8631d5a8ff1795a18`.

## Scope realized

- 15 owned paths modified, 4 retained owners untouched; 31 canonical
  destinations added; 76 R04 test modules added.
- 289 declarations routed: 127 relocate_whole,
  64 relocate_split, 61 umbrella_extract,
  37 retain_document (in place).
- No public declaration renamed; no kind, signature or visibility changed.
- Private map realized in full: 115 rows, 101 nonidentity + 14 identity;
  names unchanged, only mangled module owners move.
- The two split wrappers re-state their original imports so their transitive
  surfaces are preserved; every aggregate reachability obligation from the
  frozen packet is realized through the 1,616-row import manifest, applied
  byte-for-byte with zero deviations.

## Verification

- Full `NumStability` + `NumStabilityTest` build exit 0; `lake test` exit 0.
- All 76 R04 tests built explicitly, exit 0 (the test root cannot reach them
  until the shared `NumStabilityTest.lean` gains the R04 aggregate import —
  an R0009 integrator path).
- `check_compatibility.py` exit 0; `check_provenance.py` exit 0.
- P0008 projection replay passed with zero mismatch: 289 selected / 252
  relocated declarations, 990 signature edges, 2239 body edges, 115 private
  map rows. See PROJECTION.md.

## Outstanding, by design (R0009 integrator)

`check_layout.py` exits 1 with 26 failure(s), all requiring
R0009 shared paths this worker must not edit (test-root reachability, the
declaration-bearing-umbrella baseline, chapter-umbrella coverage of the new
destinations, and tier registration of the 12 new compatibility wrappers in
`tiers.json`/`COMPATIBILITY.md`).

## Not performed

No merge, no update to `main`, no R0009/R0010 union application, no C0005,
no wave acceptance, and no self-audit of this delivery.
