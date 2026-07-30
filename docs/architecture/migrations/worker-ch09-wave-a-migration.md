# Chapter 9 wave A migration

Wave A implements destination-DAG layers 6--7 from the frozen A/B/C contract
at `be850c4d`.  It moves exactly 66 format-2 declarations in 55
compiler-command groups:

| Destination | Layer | Declarations | Commands | Private | Frozen imports |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Chapter09.DoolittleClosure` | 6 | 31 | 20 | 1 | 31 |
| `Chapter09.Section08` | 6 | 23 | 23 | 0 | 28 |
| `Chapter09.Section10` | 7 | 12 | 12 | 0 | 28 |

Every destination is generated from hash-pinned packet command spans; command
text is unchanged.  The private `higham9_mulSubFold_source_identity` helper
remains private under its destination-qualified compiled name, and the frozen
graph has no cross-destination consumer of that helper.

`HighamChapter9DoolittleClosure` is now an exact import-only wrapper for the
canonical Doolittle destination.  The giant `HighamChapter9` owner remains a
deliberate partial compatibility owner: declarations for `Section11` and
`Problems` remain in place, while the removed `Section08` and `Section10`
commands are replaced by canonical imports.

Three canonical-only tests import one new destination each.  The new
Doolittle old-only test imports only its historical owner.  The existing
giant-owner old-only test now checks one public root from each of its eight
materialized destinations.  `NumStabilityTest.Worker.Ch09.WaveA` is lane-local
and intentionally not registered in the shared test root by this worker.

## Build-independent evidence

The following checks pass:

- full 4,420-row Chapter 9 proposal pre-check;
- A/B/C contract pre-check and deterministic wave-A materialized-text check;
- 3 destinations, 66 declarations, 55 command groups, and 1 private rewrite;
- normalized incident fingerprint
  `CE5209AEF0A587FBBED2DE1CF20F78B24A9A82A8AB22AB510C8E8B4D457445C5`;
- strict source/import graph generation, including cycles and
  reusable-to-source reachability;
- provenance contract: 207 Apache-marked production files and five evidenced
  upstream modules;
- compatibility checker, Python compilation, worker scope allowlist, and
  `git diff --check`.

The layout checker is expected to remain red in this worker tree until the
integrator registers the prior and wave-A source leaves and tests, applies the
reviewed `Theorem914Primitive` naming exception, and ratchets the now
documented Doolittle wrapper's module-docstring baseline.  No shared layout or
root file is owned here.

## Explicitly deferred compiler gates

No Lean command or build mutex was used.  A focused build, isolated canonical
and old import builds, fresh candidate format-2 extraction, stage comparison,
command re-hash through `.ilean`, axiom probes, and the global
`NumStability NumStabilityTest` build remain mandatory integrator gates.
