# W09 delivery: reusable test matrices and Chapter 28 source correspondence

Branch `codex/reorg-2026-08-w09-test-matrices-ch28`
Base commit `a32095e6e50189f7dcc39312bb4c6a36f421fab5`

## What changed

All and only the **72** `TestMatrices/Higham28*` owners were reorganized. **1295** of 1865 declarations moved into **93** canonical modules under B0009's authorized prefixes; **570** stayed at their historical owner because they provably cannot move. Every owner remains a compatibility module, so no consumer outside the wave and no integrator-owned file changed.

* reusable test-matrix analysis: `NumStability.Analysis.TestMatrices.*`
* exact Chapter 28 correspondence: `NumStability.Source.Higham.Chapter28.*`

## Static gates

| gate | result |
| --- | --- |
| `closure.py` reproduces all three per-kind floors and the union payload hash | PASS |
| `assign.py` invariants (tier, retention, privates, single-owner) | PASS |
| `verify.py` (unit placement, namespace prefix, balance, ambient, inversion) | PASS |
| `cycles.py` destination 2-cycles | 0 |
| `reach.py` no reusable module reaches Source; references inside import closure | PASS |
| `validate_names.py` canonical destination names | PASS |
| `apply.py` B0009 path authority | 0 unauthorized |

## Lean gates

| gate | result | evidence |
| --- | --- | --- |
| `lake build NumStability` | PASS | `exit=0, 1min, Build completed successfully (5881 jobs)` |
| `lake build NumStability NumStabilityTest` | PASS | `exit=0, 0min, Build completed successfully (7913 jobs)` |
| `lake build` all 191 W09 test modules | PASS | `exit=0, 0min, Build completed successfully (3725 jobs)` |
| `lake test` | PASS | `exit=0, 0min` |
| `generate_baseline.py --strict-source` | PASS | `exit=0, 2min` |

## Test matrix

**191** test modules under `NumStabilityTest/Reorganization/W09/`, each built explicitly so nothing is proved by a sibling import:

* 34 canonical-reusable
* 59 canonical-source
* 10 focused-chapter28
* 9 focused-family
* 3 focused-mixed
* 1 focused-private-closure
* 2 focused-protected
* 1 focused-reusable-tier
* 72 old-path

Old-path tests import only the historical module, so a lost re-export fails. Canonical-only tests import exactly one destination, so a destination that secretly needs a facade fails. Only authored public declarations are checked: generated members exist wherever their parent does, and private declarations are invisible outside their defining module -- which is precisely why they could not move.

## Findings

* **2 authorized destinations are unpopulated** (`S_GIN_PROJ`, `S_PERRON`), each because every declaration routed to it is independently pinned. `assign.py` proves this rather than asserting it. See `ROUTING.md`.
* **28 file-scoped `local` ambient declarations cannot move**, and neither can their consumers, which is why retention is 570 rather than the 423 floor. See `PRIVATE_CLOSURE.md`.
* **One genuine out-of-wave Source dependency** (`higham9_sineMatrix_isOrthogonal` -> Chapter 9) was found by the build, not by the frozen graph: P0010 contains exactly this wave's declarations, so it cannot express a reference into another chapter. Retained at its owner.

## Artifacts

| file | contents |
| --- | --- |
| `DELIVERY.md` | this summary |
| `ROUTING.md` | the 30 destinations, the mixed splits, every evidenced routing decision |
| `DECLARATION_ROUTES.tsv` | every declaration's owner, destination, tier and disposition |
| `PRIVATE_CLOSURE.md` | closure reproduction against B0009's pinned hashes |
| `PRIVATE_CLOSURE.tsv` | per-declaration closure membership |
| `RETENTION.tsv` | every retained declaration and why |
| `TEST_MATRIX.tsv` | every test module and what it covers |
| `CHANGED_PATHS.md` | changed paths and the authority check |
| `PROJECTION.md` | the P0010 replay |
| `INTEGRATOR_REQUESTS.md` | none needed, and the consumers that keep working |
