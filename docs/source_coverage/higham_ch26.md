# Higham Chapter 26 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 26, printed pp. 471-487. Mode: core.

| Source group | Status | Lean evidence |
|---|---|---|
| (26.1) optimization problem | VERIFIED | `IsGlobalMax`; `DirectSearchSpec` remains only an unused optional global postcondition |
| (26.2) AD stopping test | VERIFIED | `adConverged` |
| Section 26.2 MDS algorithm | VERIFIED | `MDSSimplex`, exact `reflect`/`expand`/`contract` maps, `reorderBest`, fuel-observed `iteration`, unbounded `IterationSpec`, and repeat-until-stopped `SearchTrace`; no optimizer-correctness or termination assumption |
| (26.3) MDS stopping test | VERIFIED | `mdsRelativeSize`, `mdsConverged` |
| (26.4) inverse residual measure | VERIFIED | `inverseResidualStabilityMeasure` |
| (26.5) cubic branches | VERIFIED | `cubicWCubePlus_quadratic`, `cubicWCubeMinus_quadratic` |
| (26.6) stable cubic branch | VERIFIED | `stableCubicWCube_quadratic` |
| (26.7) residual objective | PRESENT | `cubicRootResidualMeasure`; no stronger empirical claim |
| Section 26.4 interval arithmetic | VERIFIED | endpoint definitions; `add_contains`, `sub_contains`, `mul_contains`, `reciprocal_contains`, `div_contains`; and the exact dependency-widening examples `dependency_sub_example` and `dependency_div_example` |
| Section 26.4 computed directed-rounding enclosure | VERIFIED | concrete finite-range `outwardAdd/Sub/Mul/Div` producers and containment theorems use repository directed selectors |
| (26.8) first-order survey formula | EXCLUDED | deferred: no precise remainder/asymptotic semantics |
| Problems / Appendix | EXCLUDED | optional rows not selected; see inventory |

Aggregate selected-scope status: **CORE VERIFIED (PASS)**. Empirical outputs and
underspecified first-order prose remain correctly excluded.

Verification: target and Algorithms-umbrella builds PASS; forbidden-token hygiene PASS; representative
axiom audit (`stableCubicWCube_quadratic`, `RealInterval.div_contains`) contains
only `propext`, `Classical.choice`, and `Quot.sound`.
