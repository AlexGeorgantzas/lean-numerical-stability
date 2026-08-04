# W08 integrator requests

W08 touched no forbidden or shared path. Every item below is recorded rather
than applied, with the exact path, the change required, and the rationale.

## 1. Test aggregate import

**Path:** `NumStabilityTest.lean` (forbidden to W08).

**Change:** import all 125 W08 test modules listed in `TEST_MATRIX.tsv`, sorted, so the root test target
reaches them.

**Rationale:** `check_layout.py` reports `NumStabilityTest does not reach 125
test module(s)`. W08 built every one of them explicitly instead; see `DELIVERY.md`.

## 2. Tier classification

**Path:** `docs/architecture/tiers.json` (forbidden).

**Change:** classify the new canonical leaves. The nine D01-D09 roots under
`NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis`,
`NumStability.Algorithms.MatrixInversion.*` and `NumStability.Analysis.*` are
**reusable**; the D10-D42 leaves under `NumStability.Source.Higham.Chapter14.*`
are **source correspondence**.

## 3. Declaration-bearing umbrellas

**Paths:** `NumStability/Algorithms/MatrixInversion.lean`,
`NumStability/Source/Higham/Chapter14/Problem13.lean`, `.../Problem14.lean`,
`.../Problem15.lean`.

**Change:** record these four in `docs/architecture/layout-exceptions.json`, or
relocate their declarations.

**Rationale — structurally forced by B0007, not a worker choice:**

- `MatrixInversion.lean` is a W08 *owner* that must retain 13 declarations (its
  9 privates plus 4 transitively pinned public, exactly B0007's closure table),
  while B0007 authorizes destination prefixes *beneath that same file*
  (`MatrixInversion/LUFactors/`, `/Residuals/`, `/Triangular/`). A facade that
  cannot shed its privates therefore necessarily becomes a declaration-bearing
  umbrella.
- `Problem13/14/15.lean` are the sibling umbrellas B0007's own review names
  ("Existing Problem13.lean, Problem14.lean, and Problem15.lean are sibling
  umbrellas, not descendants"). They already hold declarations, are not W08
  owners, and are outside B0007's owned paths.

## 4. Aggregate reachability

**Paths:** `NumStability/Algorithms/LinearSystems.lean`,
`NumStability/Analysis.lean`, `NumStability/Analysis/FirstOrder.lean`,
`NumStability/Source.lean`, `NumStability/Source/Higham.lean`,
`NumStability/Source/Higham/Chapter14.lean` (all forbidden or outside scope).

**Change:** add the new canonical descendants so the aggregates reach them.
`check_layout.py` reports the exact missing lists, reproduced verbatim in
section 8 below.

## 5. Docstring ratchet

**Path:** `docs/architecture/layout-exceptions.json` (forbidden).

**Change:** run `check_layout.py --write-baseline`. This is an *improvement*:
the new canonical modules and rewritten facades carry module docstrings, so the
`missing module docstrings` baseline is stale.

## 6. The `Problem15` umbrella reaches a W08 owner

**Path:** `NumStability/Source/Higham/Chapter14/Problem15.lean` (outside scope).

**Preimage:** `Ch14GaussJordanSPDCorollary` imports `...Chapter14.Problem15`,
whose transitive closure reaches the historical `MatrixInversion` owner.

**Change:** retarget `Problem15.lean` onto the canonical leaves it needs, so no
canonical destination depends transitively on a compatibility facade. This does
not close a build cycle today — the full build confirms it — but it is the only
remaining transitive facade dependency from a canonical module.

## 7. W11 future retarget

**Change:** W11 consumes W08 through the historical `MatrixInversion` surface
across nineteen typed union edges. W08 does not edit W11 and preserves that
surface: `Focused/W11HistoricalCompatibility` pins both a relocated and a
retained declaration resolving from the historical path. When W11 is migrated,
retarget it onto the canonical `MatrixInversion.*` reusable leaves and the
Chapter 14 source leaves recorded in `DECLARATION_ROUTES.tsv`.

Direct non-owner importers of W08 owners measured in this tree:

- `NumStability.Algorithms`
- `NumStability.Algorithms.RandNLA.LowRankApprox`
- `NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth`
- `NumStability.Source.Higham.Chapter14.Discrepancies`
- `NumStability.Source.Higham.Chapter14.Problem13`
- `NumStability.Source.Higham.Chapter14.Problem14`
- `NumStability.Source.Higham.Chapter14.Problem15`
- `examples.LibraryLookup`

## 9. Strict-source: classified reusable-to-Source reachability

**Gate:** `generate_baseline.py --strict-source` exits non-zero with
`error: source graph check failed: 68 classified reusable-to-source/mixed
reachable pair(s)`. C0005 recorded zero, so W08 introduced the reachability —
but every link that would have to change is forbidden to W08.

**Exact chain** (shortest path, measured in the delivered tree):

```text
NumStability.Algorithms.LinearSystems.QR                    [tiers.json: reusable]
  -> NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar   [reusable]
    -> NumStability.Algorithms.RandNLA.LowRankApprox             [the W11 consumer]
      -> NumStability.Algorithms.MatrixInversion                 [W08 facade]
        -> NumStability.Source.Higham.Chapter14.*.MatrixInversion [new Source leaves]
```

**Why W08 cannot fix it.** `LinearSystems/QR.lean` and
`QR/GramSchmidtPolar.lean` are neither W08 owned paths nor inside a B0007
destination prefix. `RandNLA/LowRankApprox.lean` is the **W11** owner, and the
wave brief says explicitly not to edit W11 and to record any future canonical
retarget here. The `MatrixInversion` facade must keep importing its Source
destinations or the historical import path stops re-exporting the 223
declarations that moved, breaking the compatibility requirement. Retaining those
223 instead would defeat the wave and contradict B0007's routing table.

**Requested change, any one of:**

1. Retarget `NumStability/Algorithms/RandNLA/LowRankApprox.lean` onto the
   canonical reusable leaves it needs — `MatrixInversion.Residuals.*`,
   `MatrixInversion.Triangular.*`, `MatrixInversion.LUFactors.*` — instead of the
   historical `NumStability.Algorithms.MatrixInversion`. `DECLARATION_ROUTES.tsv`
   gives the declaration-to-leaf map needed to pick the exact imports. This is
   the W11 retarget already anticipated in request 7 and is the preferred fix.
2. Or retarget the two QR modules off `RandNLA.LowRankApprox`.
3. Or adjust the `tiers.json` classification of the QR prefix once the intended
   layering is settled.

Note the distinction the gate's wording hides: W08's own destinations are clean.
`reach.py` confirms **zero** reusable-to-Source reachability among the nine D01-D09
reusable roots, direct or transitive, and zero import cycles across all 3,230
modules. The 68 pairs are pre-existing reusable consumers inheriting reach through
a compatibility facade, which is the expected transitional state until W11 lands.

## 8. Verbatim `check_layout.py` errors

A direct run in the worker tree exits 1 with 10 errors. None is
worker-fixable: each resolves only through a path B0007 forbids to W08 or
places outside its scope.

```text
error: NumStabilityTest does not reach 125 test module(s): NumStabilityTest.Reorganization.W08.Canonical.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan, NumStabilityTest.Reorganization.W08.Canonical.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Algorithms.MatrixInversion.Residuals.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Analysis.Error.MatrixProducts.Contracts.MatrixInversion, NumStabilityTest.Reorganization.W08.Canonical.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation, NumStabilityTest.Reorganization.W08.Canonical.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies, NumStabilityTest.Reorganization.W08.Canonical.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge, NumStabilityTest.Reorganization.W08.Canonical.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation, NumStabilityTest.Reorganization.W08.Canonical.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter, NumStabilityTest.Reorganization.W08.Canonical.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure, NumStabilityTest.Reorganization.W08.Canonical.Chapter14.Algorithm04.Execution.GJEOperationalBridge, NumStabilityTest.Reorganization.W08.Canonic
error: new unclassified modules: NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan, NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion, NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion, NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion, NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion, NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion, NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion, NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation, NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
error: stale missing module docstrings baseline; review the improvement and run --write-baseline: NumStability.Algorithms.Ch14BlockTriInverse, NumStability.Algorithms.Ch14Cor147SourceDomainConstructor, NumStability.Algorithms.Ch14GJEActualDoolittleAdapter, NumStability.Algorithms.Ch14GJESourceAccumulationBridge, NumStability.Algorithms.Ch14GaussJordanAccumulation, NumStability.Algorithms.Ch14GaussJordanStep, NumStability.Algorithms.Ch14Method1BWhole, NumStability.Algorithms.Ch14Method2C, NumStability.Algorithms.Ch14Method2CWhole, NumStability.Algorithms.Ch14Method2Loop, NumStability.Algorithms.Ch14MethodDLeftResidual, NumStability.Algorithms.Ch14MethodDProductDischarge, NumStability.Algorithms.Ch14MethodDUpperCertificate, NumStability.Algorithms.GaussJordan, NumStability.Algorithms.GaussJordanPivoting
error: new declaration bearing umbrellas: NumStability.Algorithms.MatrixInversion, NumStability.Source.Higham.Chapter14.Problem13, NumStability.Source.Higham.Chapter14.Problem14, NumStability.Source.Higham.Chapter14.Problem15
error: NumStability.Algorithms.LinearSystems misses 1 canonical descendant(s): NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
error: NumStability.Analysis misses 2 canonical descendant(s): NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation, NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
error: NumStability.Analysis.FirstOrder misses 1 canonical descendant(s): NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
error: NumStability.Source misses 41 canonical descendant(s): NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete, NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary, NumStability.Source.Higham.Chapter14.Corollary06.SPD.SourceClosure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.UniformInverseBridge, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Concrete, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.FinalDivisionFamilyClosure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceClosure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceDomainConstructor, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Families, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Method2B, NumStability.Source.Higham.Chapter14.Pro
error: NumStability.Source.Higham misses 41 canonical descendant(s): NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete, NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary, NumStability.Source.Higham.Chapter14.Corollary06.SPD.SourceClosure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.UniformInverseBridge, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Concrete, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.FinalDivisionFamilyClosure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceClosure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceDomainConstructor, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Families, NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Method2B, NumStability.Source.Higham.Chapte
error: NumStability.Source.Higham.Chapter14 misses 47 canonical descendant(s): NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge, NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure, NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting, NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction, NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanStep, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete, NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary, NumStability.Source.Higham.Chapter14.Corollary06.SPD.SourceClosure, NumStability.Source.Higham.Chapter14.Corollary06.SPD.UniformInverseBridge, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Basic, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Closure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Concrete, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.FinalDivisionFamilyClosure, NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceClosure, NumStability.Source.
```
