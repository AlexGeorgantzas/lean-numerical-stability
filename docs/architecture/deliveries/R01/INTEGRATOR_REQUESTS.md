# R01 integrator requests

The worker does not edit shared consumers. The integrator should create the formal request
record from this exact five-path C0000 contract; this delivery intentionally does **not**
create or reserve an `Rxxxx` identifier.

Base: C0000 `b1b18772d80185ec08f49c818919558645c330a1`

Exact executable patch: `INTEGRATOR_REQUEST.patch`

- bytes: 7,033;
- SHA-256: `E5A8F2C07CFE899B3F6B9C486989A92FF94CE99E16EF104278D52BADD0B8FA8C`;
- paths: exactly five;
- no-change requested paths: **none** (all five require the minimal import rewrite below);
- forward and reverse replay: `python -B docs/architecture/deliveries/R01/CHECK_REQUEST_REPLAY.py`;
- disposable postimage gates: add `--full`.

The complete postimage of each file is represented minimally and without ambiguity by its
exact C0000 blob plus the path-specific zero-context hunk in
`INTEGRATOR_REQUEST.patch`. Every unmentioned byte is retained. The reconstructed
postimage SHA-256 values are pinned in `INTEGRATOR_POSTIMAGES.tsv`.

## Exact preimages and postimages

| path | C0000 blob OID | C0000 SHA-256 | postimage SHA-256 |
| --- | --- | --- | --- |
| `NumStability/Algorithms.lean` | `f59bed9a5a837256bc6b4822eb27116ebd9cc617` | `1CF1F10DFBC4CD1C4D2278A5187F72B49E85C60B70C2210D506B840177350338` | `E69DE1448B15197FBB5566A63AA03E40FBC3E45C1CFA878CA5A8494B8EF47EE1` |
| `NumStability/Algorithms/StationaryIterationSeries.lean` | `75e055fc909672d3d9d49f14c4db5c817c824f4b` | `1BAFD664CDE639D6634E2B424881B4308CF6EFBEE08196A196A9B73981076C9C` | `E437A3F78641D08EB418BFD54786CD1C1A54A3E87F2C4A1360FB2B4588AA1346` |
| `NumStability/Analysis.lean` | `dafee55fca91c338b759afda792b7d92a4a1b5da` | `10EC14BBB3C15FF813EE1EB2299C09525CD0E5F94976E1D42955858C55B3149F` | `67CE03FA396D21AA498961D331FB9AEC32DD95D7F2DA70C87BDE4093DD6F3A32` |
| `NumStability/Source/Higham/Chapter17.lean` | `796c9ee6659b36052ba6da675e343169b560c297` | `2D00F8577A51EEE27877A7DA49288FEAFCAD2021E1B618B7F7062BE9D21CFEE5` | `EB5D9DA0446935915BA3E845C4A642C11743E2E385D6E3C845B6E9623CF49660` |
| `NumStability/Source/Higham/Chapter17/Equation22.lean` | `79e1597764ab583db621ea6ffe58354f7b2046e1` | `4608828245B47DAF5E8A1DA5B150C804E44F71AEDB4F6B6BCC2EACCEE02D44DF` | `0D385CC461D22765487022894EA946C3E46031CC9969324283764AA6B3EF248A` |

## Path-specific minimal complete postimages

### `NumStability/Algorithms.lean`

Remove the five historical stationary-iteration imports and the five historical
semiconvergence-analysis imports. Add exactly:

```lean
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.All
import NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All
import NumStability.Source.Higham.Chapter17.Results.All
```

All other imports and bytes remain identical to the C0000 blob.

Rationale: canonical algorithm, analysis, and source discovery without making a reusable
leaf depend on a historical facade. Gate unblocked: root aggregate reachability and
canonical-to-historical closure. Protected by
`NumStabilityTest.Reorganization.R01.Focused.PublicNameRetention` and
`NumStabilityTest.Reorganization.R01.Focused.RootAggregates`.

### `NumStability/Algorithms/StationaryIterationSeries.lean`

Replace the six imports of historical Equation08/12/15/16/17/20 with exactly:

```lean
import NumStability.Source.Higham.Chapter17.Results.Series
```

Preserve `import NumStability.Source.Higham.Chapter17.Problem01` and the complete module
documentation unchanged.

Rationale: preserve the historical series consumer while routing its six numbered results
through a declaration-free canonical aggregate. Gate unblocked: protected-consumer
canonical import closure. Protected by
`NumStabilityTest.Reorganization.R01.Focused.StationaryIterationSeries`, which directly
imports both this protected consumer and the new canonical `Results.Series` target.

### `NumStability/Analysis.lean`

Add
`NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All` and remove
`NumStability.Analysis.SemiconvergentRealSpectrumComplete`. Retain every other byte.

Rationale: expose all five canonical analysis leaves while removing the historical facade.
Gate unblocked: analysis entry-point reachability. Protected by
`NumStabilityTest.Reorganization.R01.Focused.PublicNameRetention` and
`NumStabilityTest.Reorganization.R01.Focused.RootAggregates`.

### `NumStability/Source/Higham/Chapter17.lean`

Remove the six imports of historical Equation08/12/15/16/17/20 and add exactly
`NumStability.Source.Higham.Chapter17.Results.All`. Retain all existing per-equation
result imports, Equation22, Problem01, section results, and documentation.

Rationale: complete Chapter 17 discovery through the canonical R01 source aggregate.
Gate unblocked: source-root reachability and declaration-bearing-umbrella cleanup.
Protected by `NumStabilityTest.Reorganization.R01.Focused.PublicNameRetention` and
`NumStabilityTest.Reorganization.R01.Focused.RootAggregates`.

### `NumStability/Source/Higham/Chapter17/Equation22.lean`

Replace only:

```lean
import NumStability.Analysis.SemiconvergentLimitGeneral
```

with:

```lean
import NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.Limits.General
```

Rationale: both frozen Equation22 public declarations are typed full-graph reverse
dependents of R01 declarations and must consume the canonical general-limit module.
Gate unblocked: typed incident-edge preservation with zero historical reachability.
Protected by `NumStabilityTest.Reorganization.R01.Focused.Equation22TypedConsumers`.

## Replay contract

The checker performs all of the following in a temporary shared clone:

1. verifies all five C0000 blob OIDs and byte SHA-256 preimages;
2. verifies the exact patch size, hash, and path roster;
3. checks and applies the forward patch;
4. verifies every exact postimage hash;
5. checks and applies the reverse patch and requires a clean C0000 tree;
6. reapplies the patch, overlays only authorized worker production/tests, and checks
   resolved imports, zero canonical-to-historical reachability, and zero
   reusable-to-Source reachability;
7. with `--full`, applies the routine acceptance wiring below and then runs layout,
   compatibility, provenance, and strict-source checks in the disposable postimage.

## Disposable routine acceptance wiring

The frozen request above remains exactly five paths. Repository acceptance also requires
seven integrator-owned bookkeeping/wiring paths that are outside B0001 and therefore may
not be changed or requested by this worker. `CHECK_REQUEST_REPLAY.py --full` makes these
changes only inside its temporary C0000 clone, after verifying the exact five-path request:

| disposable path | exact acceptance mutation |
| --- | --- |
| `NumStability/Algorithms/LinearSystems.lean` | add the algorithm semiconvergence `All` import and preserve all other bytes/imports |
| `NumStability/Analysis/LinearOperators.lean` | add the analysis semiconvergence `All` import and preserve all other bytes/imports |
| `NumStabilityTest/Reorganization/R01.lean` | create a declaration-free aggregate containing the 41 exact `TEST_MATRIX.tsv` imports, sorted and unique |
| `NumStabilityTest.lean` | add the R01 test aggregate import and preserve all other bytes/imports |
| `docs/architecture/tiers.json` | classify the 16 historical owners as compatibility, the four new aggregates as aggregate, and the three frozen destination prefixes as reusable/reusable/source |
| `docs/architecture/layout-exceptions.json` | remove the 16 cleaned owners from applicable legacy arrays, including the six cleaned declaration-bearing umbrellas |
| `docs/architecture/COMPATIBILITY.md` | add exact import-order mappings for all 16 wrappers and retarget the existing `StationaryIterationSeries` row to `Problem01` plus `Results.Series` |

These seven paths are not included in `INTEGRATOR_REQUEST.patch`, are not listed in
`INTEGRATOR_POSTIMAGES.tsv`, and are not an `Rxxxx` request. They model the normal
integrator acceptance transaction so the worker-only layout red gate can be shown to have
no cause beyond forbidden shared wiring and registries. The full replay reports their
count explicitly before proving the disposable acceptance state green.
