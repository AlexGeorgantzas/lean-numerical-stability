# R08 delivery summary

Wave `R08` (matrix inversion, Higham Chapter 14), branch record `B0009`,
lane `claude-lane`, operator `claude-local`, base checkpoint `C0004`
`783ae9a4951407ece046adb8631d5a8ff1795a18`.

## Scope realized

- 45 owned paths modified; 21 canonical destinations added;
  79 R08 test modules added.
- 211 declarations relocated (163 public, 48 authored-private) by whole-owner
  routing into 21 new casefold-vacant destinations.
- No public declaration renamed; no kind, signature or visibility changed.
- 48 of 48 private normalizations realized, all non-identity; names unchanged,
  only the mangled module owner moves.
- 24 pre-existing empty shims: inert `open` lines removed, 121 import lines
  preserved byte-for-byte.
- Problem13, Problem14 and Problem15 are now declaration-free source aggregates.

## Import amendment

The frozen B0009 post-move import manifest
(`86CD1D9603A46D8789C164C99C5D032011C43919D899ECFC80B4E04E13F8D9AE`) was proven
insufficient for elaboration by a content-aware transitive reachability replay:
11 of 21 destinations had unreachable post-move content. The owner-approved
Variant A amendment adds 29 imports (11 destination DAG edges, 18 supply
imports) with zero removals; the operative manifest is recorded in
REALIZED_IMPORTS.tsv with per-line provenance. The corrected destination DAG is
24 edges and remains acyclic (21 singleton SCCs).

## Verification

- `lake build NumStability NumStabilityTest` exit 0 (763 s); all 21 destinations built.
- `lake test` exit 0 (25 s).
- All 79 R08 test modules built explicitly, exit 0, zero compiler errors. The
  private-normalization tests assert every approved private name present and
  every retired name absent, so the 48-row map is machine-verified.
- `check_compatibility.py` exit 0; `check_provenance.py` exit 0.
- P0009 projection replay **passed**, zero mismatch: 211 selected and 211
  relocated declarations, 1229 signature edges, 2886 body edges, 48 private
  normalizations, against a fresh format-2 candidate
  (`ED6C505EBC5651BEC7BE0602B0C722BFB16D8D357D2AAD268C5382BA1BC105BA`). See
  PROJECTION.md.

## Outstanding, by design (R0010 integrator)

`check_layout.py` exits 1 with exactly five failures, all of which require
R0010 shared paths this worker must not edit:

1. `NumStabilityTest` does not reach the 79 R08 test modules — needs
   `NumStabilityTest.lean`.
2. Stale declaration-bearing-umbrella baseline (debt fell from 8 to 4) — needs
   `docs/architecture/layout-exceptions.json`.
3-5. `NumStability.Source`, `NumStability.Source.Higham` and
   `NumStability.Source.Higham.Chapter14` each miss 18 canonical descendants —
   needs the Chapter 14 umbrella imports. 18 rather than 21 because the three
   destinations under Problem13/14/15 are already reachable through the
   aggregates this wave owns.

## Outstanding, required before acceptance

- Registration of the 42 shims as `compatibility` tier in `tiers.json` and
  `COMPATIBILITY.md` is R0010 integrator work.

## Not performed

No merge, no update to `main`, no R0009/R0010 union application, no C0005, no
wave acceptance, and no self-audit of this delivery.
