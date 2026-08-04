# W08 delivery report

Wave `W08`, branch `codex/reorg-2026-08-w08-matrix-inversion-ch14`, phase branch `B0007`, projection `P0008`,
base checkpoint `C0005` at `240c0d041781385a647fbec461d6863537e562cb`.

W08 reorganizes the 42 owned modules in `NumStability/Algorithms` into reusable
matrix-inversion and Gauss-Jordan APIs and exact Higham Chapter 14 source
correspondence, preserving every public declaration name, namespace, kind,
visibility, statement, proof and typed incident edge, and keeping all 42
historical import paths compiling.

## Result

| | |
| --- | --- |
| declarations selected by `W08.tsv` | 2179 |
| relocated | 1994 |
| retained at the historical owner | 185 |
| canonical destination modules | 73 |
| B0007 production destinations populated | 41 / 42 (see `ROUTING.md`) |
| compatibility modules | 42 (18 declaration-bearing, 24 pure import shims) |
| test modules | 125 |
| source lines at C0005 | 51,480 |

## Gates

| # | gate | result |
| --- | --- | --- |
| 1 | B0007 scope audit | passed — 42/42 owned paths, **0 forbidden**, 0 unowned, no tracked generated artifact |
| 2 | canonical-only builds | 73 modules, each importing exactly one canonical destination |
| 3 | old-path-only builds | 42 modules, one per owner, each importing only a historical path |
| 4 | focused builds | 10 modules across six boundaries |
| 5 | every W08 test module built explicitly | see step 3 below |
| 6 | `lake build NumStability` | `Build completed successfully (5483 jobs)`, exit 0 |
| 7 | `lake build NumStability NumStabilityTest` | exit 0, `7130 jobs` |
| 8 | all 125 W08 test modules | exit 0, `3356 jobs` |
| 9 | `lake test` | exit 0 |
| 10 | `check_compatibility.py` | passed — 337 forwarding modules, 685 canonical targets |
| 11 | `check_provenance.py` | passed — 196 Apache-marked production files, 5 evidenced upstream modules |
| 12 | `check_layout.py` | **integrator wiring required** — 10 errors, all recorded verbatim in `INTEGRATOR_REQUESTS.md`; none worked around |
| 13 | strict-source format-2 | **integrator wiring required** — exit 2: `68 classified reusable-to-source/mixed reachable pair(s)`. Zero import cycles and zero reusable-to-Source reachability *among W08's own destinations*; the pairs come from two pre-existing classified-reusable QR modules reaching the new Chapter 14 Source leaves through the W11 consumer. See request 9 |
| 14 | complete format-2 candidate | `benchmark-results/W08-candidate.tsv`, sha256 `A8875CFE94A1BAC6…` |
| 15 | `P0008` replay, recorded arguments | **`phase projection contract passed`**, exit 0 |

Every Lean operation ran under the phase build mutex
`lean-reorganization-2026-08`, acquired once per pass and released reliably.

Exit codes and job counts above come from the final worker tree. The substantive
cold timings were 8 minutes for the library, 71 minutes for library-plus-test,
6 minutes for the 125 test modules, and 2 minutes for candidate extraction; the
confirming re-run after the end-of-file newline normalisation was fully cached
and therefore reports 0 minutes per step with identical job counts.

## Static checks run before each build

| check | result |
| --- | --- |
| unit placement | every emit unit appears exactly once, byte-identical |
| namespace prefix | the reconstructed namespace is a prefix of each declaration's frozen name |
| namespace balance | no unclosed namespace or section |
| ambient context | no destination lost imports its owner transitively supplied |
| architecture inversion | no canonical module imports a compatibility facade |
| import cycles | 0 |
| reusable-to-Source reachability | 0, direct or transitive |
| intra-wave reference reachability | 16,518 references, all inside their module's import closure |
| canonical module names | all 73 validate against `check_layout.py`'s rules |

## Preservation

No axiom, `sorry`, `admit`, weakened statement, replacement proof, renamed
declaration or fabricated API was introduced. Declaration text is relocated
byte-identically. All **45** private declarations stay in their defining
module; the reverse closure is **185** declarations across
**18** owners, reproducing B0007's pinned payload hashes exactly.
See `PRIVATE_CLOSURE.md`.

## Accepted boundaries

The 16 direct W02 imports and the 3 accepted W03 canonical imports are
preserved unchanged; no historical W03 import was reintroduced. W11 is not
edited and its historical `MatrixInversion` surface still resolves.

## Integration

`INTEGRATOR_REQUESTS.md` records eight items with exact paths and rationale.
W08 is accepted as milestone `M08` only after that wiring and a rerun of the
acceptance gates.
