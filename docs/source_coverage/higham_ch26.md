# Higham Chapter 26 Source Coverage Ledger

> **Canonical source migration and operational closure (2026-07-24).**
> `Source.Higham.Chapter26.AlternatingDirections.CrudeLineSearch` records the
> literal crude alternating-directions producer from pp. 475–476: the
> `10⁻⁴ x_i` trial with zero-coordinate fallback, sign reversal, and at most
> 25 doublings, together with coordinate/sweep monotonicity. The
> `MultidirectionalSearch` family constructs both printed initial simplexes
> and proves their Euclidean edge-length and orthogonality/equi-edge claims.
> The complete canonical import is `NumStability.Source.Higham.Chapter26`;
> the two former `Algorithms.AutomaticErrorAnalysis` paths are compatibility
> wrappers.

Source: Higham, 2nd ed., Chapter 26, printed pp. 471–487. Mode: core.

| Source group | Status | Lean evidence |
|---|---|---|
| (26.1) optimization problem | VERIFIED | `IsGlobalMax`; `DirectSearchSpec` remains only an unused optional global postcondition |
| (26.2) AD stopping test | VERIFIED | `adConverged` |
| Section 26.2 alternating-directions search | VERIFIED | Exact coordinate execution and the finite crude line-search producer, including its sign reversal, doubling bound, and coordinate/sweep monotonicity |
| Section 26.2 MDS algorithm | VERIFIED | `MDSSimplex`, exact `reflect`/`expand`/`contract` maps, `reorderBest`, fuel-observed `iteration`, unbounded `IterationSpec`, and repeat-until-stopped `SearchTrace`; no optimizer-correctness or termination assumption |
| (26.3) MDS stopping test | VERIFIED | `mdsRelativeSize`, `mdsConverged` |
| (26.4) inverse residual measure | VERIFIED | `inverseResidualStabilityMeasure` |
| (26.5) cubic branches | VERIFIED | Real and complex branch identities, Cardano root endpoints, and the documented zero-branch discrepancy |
| (26.6) stable cubic branch | VERIFIED | `stableCubicWCube_quadratic` and `stableCubicWCubeComplex_quadratic` |
| (26.7) residual objective | PRESENT | `cubicRootResidualMeasure`; no stronger empirical claim |
| Section 26.4 interval arithmetic | VERIFIED | Exact endpoint definitions; `add_contains`, `sub_contains`, `mul_contains`, `reciprocal_contains`, `div_contains`; and both dependency-widening examples |
| Section 26.4 computed directed-rounding enclosure | VERIFIED | Concrete finite-range `outwardAdd/Sub/Mul/Div` producers and containment theorems use repository directed selectors |
| (26.8) first-order survey formula | PRESENT-AS-PRECISE-INTERPRETATION | `linearizedForwardError26_8_eq` proves the coordinate decomposition of a continuous linear functional; `eq26_8_linearized_forward_error` supplies an explicit Fréchet-derivative/little-o interpretation, and `eq26_8_exact_of_affine_increment` handles affine evaluation exactly. The printed display omits the remainder, limiting family, and hypotheses needed to determine this semantics uniquely |
| Problems / Appendix | EXCLUDED | Optional rows not selected; see the inventory |

Aggregate selected-scope status: **CORE VERIFIED (PASS)**. Empirical outputs
remain excluded. Equation (26.8) is counted only as the explicit
Fréchet-derivative interpretation above, not as a claim that the underspecified
printed prose determines those added semantics uniquely.

Verification: the canonical chapter aggregate, both compatibility wrappers,
23 canonical leaf smokes, six aggregate smokes, and two old-only compatibility
smokes build successfully. The representative axiom audit
(`stableCubicWCube_quadratic`, `RealInterval.div_contains`) contains only
`propext`, `Classical.choice`, and `Quot.sound`.
