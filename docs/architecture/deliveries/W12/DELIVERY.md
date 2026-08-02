# W12 delivery report

Wave `W12`, branch `codex/reorg-2026-08-w12-ch01-ch02-ch05`, phase branch `B0003`,
base checkpoint `C0002` at `e6ef0107edb873f7a05ad8282df7efdf41a986d3`.

W12 splits 42 historical modules in `NumStability/Analysis` and
`NumStability/Algorithms` into the 63 canonical destination roots recorded in
`B0003.json`, preserving every declaration name, statement, proof and historical
import path.

## Result

| | |
| --- | --- |
| declarations selected by `W12.tsv` | 4197 |
| relocated to canonical modules | 2647 |
| retained in the historical module | 1550 |
| canonical modules written | 67 |
| destination roots covered | 63 / 63 |
| compatibility modules | 42 (23 declaration-bearing, 19 pure import shims) |
| focused test modules | 109 (67 canonical-only, 42 old-import) |

## Why 1550 declarations did not move

Lean mangles a private declaration to `_private.<defining module>.<n>.<name>`, so the
defining module is part of the name. Relocating a private renames it and every
incident edge is reported missing against the frozen graph. W12 selects **257**
private declarations, against 21 in W01.

Retention closes over them in two steps:

1. a same-module user of a private cannot see it from any other module, so it stays;
2. a different-owner user would force its canonical destination to import the owner's
   compatibility facade. That inverts the dependency direction the strict-source gate
   enforces, so it stays as well (58 declarations).

The closure fixes 1550 of 4197 declarations (36.9%).
Retention is inside the contract, not a workaround of it: `P0003` lists all 42 owners
under `--allow-module`, so a retained declaration keeps its name, kind, visibility and
every incident edge. The full assignment is in `ROUTING.md`.

## Gates

| gate | result |
| --- | --- |
| scope against `B0003.json` | passed — 42/42 owned paths, 65/65 destination prefixes, **0 forbidden paths touched** |
| 1. `lake build NumStability` | `Build completed successfully (5065 jobs)`, exit 0 |
| 2. focused test build, 109 modules | `Build completed successfully (3721 jobs)`, exit 0 |
| 3. `check_layout.py` | **requires integrator wiring** — see below and `INTEGRATOR_REQUESTS.md` |
| 3. `check_compatibility.py` | passed — 296 forwarding modules, 566 canonical targets |
| 3. `check_provenance.py` | passed — 204 Apache-marked production files, 5 evidenced upstream modules |
| 4. strict-source (`generate_baseline.py --strict-source`) | exit 0 |
| 5. `P0003` with recorded arguments | **`phase projection contract passed`**, exit 0 |
| 6. declarations / edges preserved | `selected_declarations: 4197`, `relocated_declarations: 2647`, signature 10175 + body 23388 |

All Lean work ran under the phase build mutex `lean-reorganization-2026-08`
recorded in `phase.json`; acquisition waited 30 minutes for the W02 worker.

### The layout gate cannot pass at a worker tip

`check_layout.py` reports 9 errors. Every one resolves only through a path `B0003`
forbids W12 from touching, so none is fixable here:

| error | file that would have to change | status |
| --- | --- | --- |
| `NumStabilityTest does not reach 109 test module(s)` | `NumStabilityTest.lean` | forbidden (exact) |
| `new unclassified modules` (3 reusable leaves) | `docs/architecture/tiers.json` | forbidden (exact) |
| `stale missing module docstrings baseline` (1) | `docs/architecture/layout-exceptions.json` | forbidden (exact) |
| `NumStability.Source misses 49 canonical descendant(s)` | `NumStability/Source.lean` | forbidden (exact) |
| `NumStability.Source.Higham misses 49` | `NumStability/Source/Higham.lean` | outside scope |
| `Chapter01` misses 5, `Chapter02` misses 24, `Chapter04` misses 3, `Chapter08` misses 4 | chapter aggregates | outside scope |

W01 delivered in the same state and recorded it as resolved by the acceptance
checkpoint. The stale docstring entry is an *improvement*: `HighamLemma88Entrywise`
had no module docstring at the base commit and its compatibility module now has one,
so the ratchet baseline needs `--write-baseline`, which writes a forbidden file.

## Defects found and fixed before the build

Static checks over the frozen graph caught four classes of defect that a green build
would not have revealed, or that would have cost a full build behind a contended
mutex to discover:

1. **Five destination import cycles**, each between two destinations carved from one
   owner. Three shared one root cause: a generated declaration routes by its own short
   name, so `PriestSourceStepLoopFacts.mk` routed on `mk`, missed every concept rule,
   and was separated from the structure it belongs to. Generated declarations now
   route by their parent.
2. **A reusable-to-source import.** `PolynomialEvaluation.RootProduct` imported
   `Chapter05.Section01.RelativeError`, the edge strict-source forbids, because one
   theorem straddles both concepts. The root-product error analysis is expressed
   through `relErrorCounter`, which is section 5.1 source material, so it is source
   too; only the evaluators are reusable. All three reusable leaves now have no direct
   source dependency.
3. **A dropped `set_option` modifier.** `set_option maxRecDepth 10000 in` sits above
   its theorem in `Problem2_3.lean` and is not part of the `.ilean` span; moving the
   theorem without it would exceed the recursion limit.
4. **A split `mutual` block.** `Horner.lean` defines `evenCoeffsAsc`/`oddCoeffsAsc` in
   one `mutual ... end`, which cannot be divided; it moves as a single unit.

## Residual debt

23 of the 42 compatibility modules still define declarations and are therefore
facades, not pure import shims. They cannot be classified as compatibility paths and
should remain reviewed unclassified debt until a later wave promotes or relocates the
257 privates.

The three reusable leaves reach `Chapter02.FloatingPointArithmetic.AdditiveUnderflowModel`
and `.Environment` transitively through `NumStability.Analysis.FloatingPointArithmetic`.
That module is W01's compatibility facade, is untouched by W12, and already imported
both at the base commit, so the reach is inherited rather than introduced here.

## Integration

W12 may finish before W02 but is accepted only after it. `INTEGRATOR_REQUESTS.md`
records the 17 direct W12-to-W02 imports for rewriting to accepted W02 canonical
leaves, the shared Chapter 8 umbrella update, and the manifest and aggregate changes
W12 is not authorized to make.

The delivery commit is the tip of `codex/reorg-2026-08-w12-ch01-ch02-ch05`. It is not named here because a
commit cannot contain its own hash; `B0003.json`'s `delivery.commit_sha` is an
integrator-owned field and W12 is not authorized to edit the phase records.
