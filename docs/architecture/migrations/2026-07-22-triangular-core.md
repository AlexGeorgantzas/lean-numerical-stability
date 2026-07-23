# Triangular linear-system family migration

## Scope

This batch moves five reusable triangular-system modules out of the flat
Algorithms directory and completes the existing triangular family. Declaration
names and namespaces are unchanged.

## Path map

| Historical module | Canonical module |
| --- | --- |
| `NumStability.Algorithms.TriangularSolve` | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` |
| `NumStability.Algorithms.ForwardSub` | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` |
| `NumStability.Algorithms.TriangularForwardBound` | `NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance` |
| `NumStability.Algorithms.InverseBounds` | `NumStability.Algorithms.LinearSystems.Triangular.InverseBounds` |
| `NumStability.Algorithms.TriangularForwardComparison` | `NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds` |

`NumStability.Algorithms.LinearSystems.Triangular.Combined` was already at its
canonical path. Each historical path is now an import-only compatibility
wrapper.

## Boundary rationale

The six canonical leaves contain source-independent algorithms and reusable
error analysis. The public umbrella deliberately excludes
`TriangularArbitraryOrder`, `TriangularNoGuard`, `HighamChapter8`, and
`MMatrix`: those modules either contain explicit source correspondence or
belong to a separate mathematical family.

`BackSubstitution` previously imported `NumStability.Analysis.Summation`
without using any of its declarations. That edge reached mixed Chapter 4
material, so it was removed and the leaf was built independently before the
family was classified reusable. The canonical triangular closure now contains
only reviewed reusable modules.

## Import and classification changes

Production consumers now import the narrow canonical leaf they use. The
historical Algorithms aggregate and `HighamChapter8` import the family umbrella
instead of six leaves. At this triangular checkpoint, that reduced the
Algorithms aggregate from 495 to 490 direct imports. The later Sylvester
aggregate reduces the final count further to 463.

The batch also classifies the reviewed analysis dependencies `ForwardError`,
`MatrixAlgebra`, `PerturbationTheory`, `Rounding`, and `SubtractionFold` as
reusable. At this checkpoint, `Analysis.Summation` was explicitly classified
`mixed`, recording pre-existing Chapter 4 debt rather than hiding it. A later
batch made `Analysis.Summation` an aggregate, extracted the reusable
`Summation.Signs` leaf, and assigned the remaining mixed declarations to
`Summation.ErrorBounds`.

## Entry points and tests

`NumStability.Algorithms.LinearSystems.Triangular` is a documented,
declaration-free complete aggregate. A canonical smoke test checks every leaf.
Six isolated historical tests cover the five new wrappers and the pre-existing
combined-solve wrapper.

## Evidence

- Starting revision: `11a5241c7496851a8653080f30d39182c4eeb4d4`.
- `BackSubstitution` built successfully without the stale mixed Summation
  dependency (1,471 jobs).
- At this triangular checkpoint, `check_compatibility.py` passed with 42
  wrappers and 43 canonical targets.
- At this triangular checkpoint, `check_layout.py` reported 767 modules, 652
  unclassified modules, 9 mixed modules, 228 missing module docs, and no
  legacy-debt increase.
- Final family, public-entry-point, strict-source, and full-suite evidence is
  recorded in [`2026-07-22-organization.md`](2026-07-22-organization.md).
