# W11 delivery

W11 reorganizes all and only B0010's 18 RandNLA owners and their 103,723 base
source lines from checkpoint C0006 at
`a32095e6e50189f7dcc39312bb4c6a36f421fab5`.  It preserves all 3,354 selected
declarations and their typed incident edges while separating reusable
randomized-linear-algebra APIs from exact Drineas--Mahoney source endpoints.

The delivery branch is `codex/reorg-2026-08-w11-randnla`.  The immutable final
delivery SHA is the Git object reported in the handoff; a commit cannot embed
its own object name.  The worker fetched `origin` without merging, rebasing, or
cherry-picking `origin/main`.

## Scope and path inventory

The delivery inventory contains 146 paths:

| Class | Paths |
| --- | ---: |
| Historical W11 owners modified | 18 |
| Canonical production modules added | 37 |
| W11 tests added | 76 |
| W11 delivery/evidence files added | 15 |
| **Total** | **146** |

`CHECK_SCOPE.py` generates `CHANGED_PATHS.md` from
`a32095e6e50189f7dcc39312bb4c6a36f421fab5..DELIVERY_HEAD`.  It accounts for
all 18 owners and reports zero missing owners, forbidden paths, unowned paths,
out-of-scope destinations, or tracked generated artifacts.  No shared
aggregate, root test, tier manifest, layout exception, compatibility document,
consumer, CI/toolchain path, control, or another wave's owner is modified.

The historical umbrella `NumStability.Algorithms.RandNLA` remains import-only.
Its 17 physical owners are `ElementwiseSampling`, `ElementwiseSpectral`,
`ElementwiseTraceMGF`, `HitCountConcentration`, `LeastSquaresSketch`,
`LowRankApprox`, `Preconditioning`, `RowSampling`, `RowSamplingGram`,
`RowSamplingLeverage`, `RowSamplingLeverageComputedBasis`,
`RowSamplingLeverageMGF`, `RowSamplingTraceMGF`, `UniformRowSampling`,
`UniformRowSamplingComposition`, `UniformRowSamplingFP`, and
`UniformRowSamplingMGF`.

## Declaration routing

| Route | Declarations |
| --- | ---: |
| Relocated to 19 reusable API modules | 2,322 |
| Relocated to 18 exact source modules | 807 |
| **Relocated total** | **3,129** |
| Retained for private reverse closure | 225 |
| **Selected total** | **3,354** |

The selected kinds are 2,469 theorems, 813 definitions, and 24 each of
inductives, constructors, and recursors; visibility is 3,351 public and three
private.  `DECLARATION_ROUTES.tsv` records every exact declaration route, and
`ROUTING.md` records all 37 canonical destinations and the reviewed
declaration-level splits for `ElementwiseSpectral` and `LowRankApprox`.

Nine historical owners remain declaration-bearing and eight become pure
import shims.  Every facade directly imports every canonical module receiving
one of its declarations, so every historical import remains valid.

## Private reverse closure

The three private declarations remain unrenamed in their historical owners.
Reverse closure retains exactly 225 of 3,086 whole source commands:

- hit-count closure: 20 declarations across `HitCountConcentration` (3) and
  `ElementwiseSpectral` (17);
- row-Gram closure: 33 across `RowSamplingGram` (23),
  `RowSamplingLeverage` (2), and `LeastSquaresSketch` (8);
- uniform-row closure: 172 across `UniformRowSampling` (10),
  `UniformRowSamplingComposition` (1), `Preconditioning` (66), and
  `UniformRowSamplingFP` (95).

The ordered retained payload SHA-256 is
`FAD5DC5D7CD80112157031E012D32593FBF33ACED6C1B9F94D60DEC55D1EA7F9`.
`PRIVATE_CLOSURE.tsv` and `PRIVATE_CLOSURE.md` contain the exact private names,
spans, depths, and witness edges.

## Dependency handling

The source-specific Equation 08 endpoint retains its accepted Chapter 20
QRSolve dependency because no accepted canonical replacement exists for that
dependent closure.  No reusable W11 module imports or reaches Chapter 20 or
any `NumStability.Source` module.

The reusable low-rank modules, Equation 09 endpoint, and LowRank historical
facade import exactly the three C0006 MatrixInversion LU-factor/residual
modules.  The historical MatrixInversion umbrella is never restored.  Focused
tests protect the accepted W02 probability/Doolittle APIs, the W06 trace-MGF
API, Chapter 20, and the three MatrixInversion APIs.

The forbidden shared consumer
`Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` is untouched.
`INTEGRATOR_REQUESTS.md` gives its exact one-line retarget to
`LowRankApproximation.RankFactorizations.Core`, plus every other shared
retarget, classification, aggregate, and test-root edit needed for integration.

## Tests

| Test class | Count | Isolation |
| --- | ---: | --- |
| Canonical-only reusable | 19 | exactly one reusable destination import |
| Canonical-only source | 18 | exactly one source destination import |
| Old-path-only | 18 | exactly one historical owner import |
| Focused | 21 | semantic, private, protected, and retarget boundaries |
| **Total** | **76** | all below `NumStabilityTest/Reorganization/W11/` |

The focused set explicitly covers elementwise sampling; reusable and Equation
02 spectral results; trace-MGF/concentration; row, leverage, and uniform
sampling; preconditioning; reusable least-squares and its Chapter 20 closure;
reusable low rank and Equation 09; all three private closures; accepted W02,
W06, and Chapter 20 surfaces; MatrixInversion; the C0006 low-rank retarget; and
the shared-consumer destination.  `TEST_MATRIX.tsv` records every import and
representative `#check`.

## Gate ledger

Every Lean/Lake operation below held
`Local\lean-reorganization-2026-08`.

| Gate | Result, jobs, elapsed time |
| --- | --- |
| Initial acyclic build of all 37 canonical production targets | passed, exit 0, 4,328.925 s |
| 37 canonical-only tests explicitly | passed, exit 0, 3,185 jobs, 4.925 s |
| 18 old-path-only tests explicitly | passed, exit 0, 3,183 jobs, 4.548 s |
| 21 focused tests explicitly | passed, exit 0, 3,183 jobs, 4.600 s |
| `lake build NumStability NumStabilityTest` | passed, exit 0, 7,857 jobs, 1,011.569 s |
| `lake build NumStability` | passed, exit 0, 5,825 jobs, 6.135 s |
| `lake test` | passed, exit 0, job count not emitted, 6.829 s |
| Compatibility contract | passed, exit 0, 337 forwarding / 685 canonical, 23.855 s |
| Provenance contract | passed, exit 0, 197 Apache / 5 upstream, 0.867 s |
| W11 deterministic reconstruction | passed, exit 0, 3,086 commands / 3,354 declarations / 136 generated files, 5.052 s |
| W11 static graph/test/retention audit | passed, exit 0, 131 Lean paths, zero findings, 8.032 s |
| Exact B0010 scope | passed, exit 0, 146 paths / 18 owners / 128 destinations, zero findings, 0.454 s |
| Full format-2 candidate | passed, exit 0, 5,825-job build confirmation, 128.861 s |
| P0011 recorded-vector replay | passed, exit 0, 4.558 s |

The repository-wide layout checker exits 1 in 146.525 seconds only on
integration-owned state: the shared test root does not yet reach 76 W11 tests,
19 reusable modules need tier classification, ten source leaves need discovery
wiring, and the improved historical umbrella documentation makes one stale
missing-doc baseline entry disappear.  W11-owned docs, import order, naming,
case-fold uniqueness, placeholders, and canonical graph checks all pass.

The exact repository strict-source command exits 2 in 25.452 seconds on 32
classified paths caused by four accepted reusable consumers' stale imports of
the historical LowRank facade.  It reports zero direct forbidden edges, zero
mixed targets, zero unresolved imports, and zero cycles.  The W11 reusable
canonical graph itself has zero `Source` or facade reachability, and an
in-memory replay of the exact requested shared retargets reduces the 32 paths
to zero.  These integration-owned results are recorded rather than waived.

## Projection

The full candidate TSV SHA-256 is
`D893E204F8488FB8F686E5F3230C9610988106E600E01A6BF69B36C2191856BE`.
P0011 passes exactly with 3,354 selected declarations, 3,129 relocated, 225
retained, 19,096 signature rows, 26,201 body/proof rows, and 28,652 union
edges.  `PROJECTION.md` records every pinned control hash and the exact replay.

## Evidence artifacts

| File | Purpose |
| --- | --- |
| `DECLARATION_ROUTES.tsv` | one exact route for all 3,354 declarations |
| `PRIVATE_CLOSURE.tsv` / `PRIVATE_CLOSURE.md` | private seeds, reverse closures, and witnesses |
| `RETENTION.tsv` | per-owner relocation, retention, and facade type |
| `ROUTING.md` / `ROUTE_SUMMARY.json` | reviewed destinations and route totals |
| `TEST_MATRIX.tsv` | all 76 isolated and focused tests |
| `GENERATE_MIGRATION.py` | deterministic reconstruction and byte verification |
| `CHECK_STATIC.py` | graph, test, facade, private, MatrixInversion, and source-boundary audit |
| `CHECK_PROJECTION.py` / `PROJECTION.md` | hash-pinned exact P0011 replay |
| `CHECK_SCOPE.py` / `CHANGED_PATHS.md` | generated base-to-delivery scope proof |
| `INTEGRATOR_REQUESTS.md` | exact forbidden/shared integration changes |

No W04, W09, W10, W90, accepted owner, shared consumer, root test, aggregate,
tier, layout exception, compatibility document, phase control, CI/toolchain
file, or another worker branch is changed.
