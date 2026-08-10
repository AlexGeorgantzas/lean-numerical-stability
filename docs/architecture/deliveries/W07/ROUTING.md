# W07 declaration routing

W07 routes exactly the 252 declarations selected by `B0011`, `W07.tsv`, and
`P0012`.  `DECLARATION_ROUTES.tsv` is the declaration-level authority for this
delivery; this document summarizes that ledger without broadening the owned
scope.

## Exact totals

| Disposition | Reusable | Chapter 17 Source | Historical retention | Total |
| --- | ---: | ---: | ---: | ---: |
| Relocated | 47 | 89 | 0 | 136 |
| Retained | 0 | 0 | 116 | 116 |
| **Total** | **47** | **89** | **116** | **252** |

The selected declarations comprise 192 theorems, 48 definitions, four
inductives, four constructors, and four recursors.  Visibility is 244 public
and eight private.  The generator copies all 228 complete C0007 source
commands at declaration-family boundaries; it does not reconstruct
statements or proofs.  Names, namespaces, kinds, visibility, attributes,
ambient options, local instances, section context, and every typed incident
edge therefore remain unchanged.

## Historical owners

| Historical owner | Selected | Retained | Reusable | Source |
| --- | ---: | ---: | ---: | ---: |
| `StationaryIteration` | 165 | 29 | 47 | 89 |
| `StationaryIterationDrazin` | 41 | 41 | 0 | 0 |
| `StationaryIterationRounded` | 16 | 16 | 0 | 0 |
| `StationaryIterationSemiconvergent` | 20 | 20 | 0 | 0 |
| `StationaryIterationSemiconvergentExistence` | 10 | 10 | 0 | 0 |
| **Total** | **252** | **116** | **47** | **89** |

`StationaryIteration` is physically split declaration-by-declaration.  Its
historical module remains an honest declaration-bearing historical facade:
it directly imports all 34 canonical leaves and retains exactly the 29
declarations required by the private reverse closure.

B0011 gives the other four owners only `classify;document` authority.  Their
87 declarations therefore remain physically and semantically unchanged.
Module documentation now describes their Drazin, rounded-execution,
semiconvergence/projector, and block-form-existence surfaces.  Their final tier
classification remains an explicit integrator request; W07 does not use a
destination prefix as authority to relocate them.

## Reusable destinations

The 47 source-independent declarations are routed to nine reviewed reusable
leaves:

| Canonical module | Declarations |
| --- | ---: |
| `Convergence.Singular.FixedSubspaces` | 3 |
| `ErrorAnalysis.Forward.ComplementDecomposition` | 1 |
| `ErrorAnalysis.Local.OneStep` | 1 |
| `ErrorAnalysis.Residual.Identities` | 2 |
| `Execution.Computed.Model` | 6 |
| `Projectors.Drazin.Algebra` | 15 |
| `Recurrences.Affine.Unrolling` | 3 |
| `Splittings.Core.Definitions` | 12 |
| `Splittings.Scaling.Diagonal` | 4 |
| **Total** | **47** |

Every module above is below
`NumStability.Algorithms.LinearSystems.Iterative.Stationary`.  The reusable
graph has zero direct or transitive imports of `NumStability.Source` and zero
paths to a W07 historical facade.

## Chapter 17 destinations

The 89 numbered equations, printed conclusions, source aliases, examples,
corrections, and source-specific endpoints are routed to 25 exact Source
leaves:

| Chapter 17 endpoint | Declarations |
| --- | ---: |
| `Equation01.ComputedIteration.Results` | 8 |
| `Equation02.LocalError.Results` | 1 |
| `Equation03.ComputedRecurrence.Results` | 1 |
| `Equation04.FixedPoint.Results` | 2 |
| `Equation05.ErrorExpansion.Results` | 3 |
| `Equation06.ComponentwiseForward.Results` | 1 |
| `Equation07.NormwiseGrowth.Results` | 5 |
| `Equation08.NormwiseForward.Results` | 1 |
| `Equation09.ComponentwiseGrowth.Results` | 5 |
| `Equation10.LocalErrorSimplification.Results` | 2 |
| `Equation12.PartialSumBound.Results` | 1 |
| `Equation13.ComponentwiseForward.Results` | 7 |
| `Equation15.NormwiseForward.Results` | 1 |
| `Equation16.Jacobi.Results` | 5 |
| `Equation17.SOR.Results` | 8 |
| `Equation18.ResidualRecurrence.Results` | 2 |
| `Equation19.ResidualBound.Results` | 2 |
| `Equation20.ResidualSigma.Results` | 15 |
| `Equation21.SingularIteration.Results` | 2 |
| `Equation27.SingularErrorSplit.Results` | 1 |
| `Equation28.SingularErrorSplit.Results` | 1 |
| `Equation29.SingularSource.Results` | 3 |
| `Equation33.StoppingTests.Results` | 6 |
| `Section02.ScaleIndependence.Results` | 3 |
| `Section04.PrintedConclusions.Results` | 3 |
| **Total** | **89** |

The 34-leaf canonical import graph is acyclic, has no unresolved W07 import,
and has zero canonical-to-historical reachability.  Old-path-only tests prove
that every historical import still exposes its original public declarations;
canonical-only tests prove each emitted destination in isolation.
