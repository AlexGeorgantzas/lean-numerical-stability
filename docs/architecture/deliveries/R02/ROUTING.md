# R02 routing

All 142 declarations of the 28 residual owners are routed to the 14
canonical destinations frozen by P0002. The mapping was **not derived** by this worker: it
is B0002's reviewed sheet, executed verbatim and then verified against the graph.

| quantity | value |
| --- | ---: |
| declarations | 142 |
| relocated | 142 |
| retained at owners | 0 |
| private | 76 |
| public | 66 |
| canonical destinations | 14 |
| owners | 28 (14 declaration-bearing, 14 declaration-free) |
| owner fan-out | 0 -- every bearing owner routes to exactly one destination |

Because each bearing owner routes its **whole block** to a single destination
(`normalization_decision = approved_owner_block_route` for all 142), the destination
takes the owner's body **verbatim**. Namespaces, `variable`/`open` ambient context,
`noncomputable section`, attributes and proof text move untouched, so no signature or proof
can drift. That is a stronger preservation guarantee than span-slicing can offer.

## Declarations per destination

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.InfinityCounterexample.Trace` | 45 |
| `NumStability.Source.Higham.Chapter15.Section06.TridiagonalLUConditionBounds.ExactBounds` | 21 |
| `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.FactorizationAndNorm` | 17 |
| `NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ScalarCase.Iteration` | 9 |
| `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square` | 8 |
| `NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.InverseNormBound.TriangularSolve` | 7 |
| `NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular` | 6 |
| `NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.ConstrainedLagrangian.Differentiation` | 6 |
| `NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.ConditionEstimate.Bounds` | 5 |
| `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.EntryFormulas` | 5 |
| `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.SecondDerivative.Rowwise` | 4 |
| `NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.StrongLocalMaximum.Convergence` | 4 |
| `NumStability.Source.Higham.Chapter15.Problem06.TridiagonalInverseNorm.Recurrences.ArrayExecution` | 3 |
| `NumStability.Source.Higham.Chapter15.Theorem09.Ikebe.IrreducibleRightInverse.RankOneStructure` | 2 |

## Verified invariants

| invariant | result |
| --- | --- |
| route map covers the frozen 142 exactly | yes |
| route agrees with graph on kind/visibility/owner | 142/142 |
| owner wrappers containing a declaration | 0 |
| import cycles among staged modules | 0 SCCs, 0 two-cycles |
| destinations importing a historical owner | 0 |
| reusable destinations reaching Source | 0 |
| canonical destinations reaching a historical owner | 5 on the worker branch, **0** under the integrator postimage |

The last row is the wave's only unmet invariant, and it is carried exclusively by five
integrator-owned modules R02 may not edit. See `INTEGRATOR_REQUESTS.md`.
