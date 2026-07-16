# Higham Chapter 26 Source Inventory

## Audit basis

- Source: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed. (SIAM, 2002), Chapter 26, "Automatic Error Analysis".
- Local source: `References/1.9780898718027.ch26.pdf`, printed pp. 471-487.
- Mode: core; parallel owner: Split 4.
- Source inspection: all 17 PDF pages were extracted, rendered, and visually
  checked; equations (26.1)-(26.8) and Problems 26.1-26.4 were checked against
  the rendered pages. Appendix A solution 26.2 was checked on printed p. 570.
- Primary named labels: none.

## Inventory

| ID | Source location | Kind | Statement summary | Precision / generality | Source proof | Dependencies | Decision | Reason code | Lean artifact / status |
|---|---|---|---|---|---|---|---|---|---|
| 26-D1 | p. 472, Sec. 26.1 | definition | Direct-search problem `max f(x)` using values only | precise / general | definition | real order | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `IsGlobalMax`, `DirectSearchSpec` / PASS |
| 26.1 | p. 472 | equation | Unconstrained maximization `max_{x in R^n} f(x)` | precise / general | definition | 26-D1 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `IsGlobalMax` / PASS |
| 26-E1 | pp. 472-474 | experiment | GE growth-factor searches and printed matrices/outputs | empirical runs | none | Chapter 9 `growthFactor` | SKIP | SKIP-EMPIRICAL | not encoded; source does not specify a unique execution |
| 26-A1 | pp. 474-475 | algorithm | Alternating-directions heuristic and line-search choices | partly precise / software heuristic | none | objective comparisons | BENCHMARK_CANDIDATE | BENCHMARK-COMPARISON | stopping contract only; heuristic not encoded |
| 26.2 | p. 475 | equation | Relative-increase AD stopping test | precise / general | definition | real absolute value | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `adConverged` / PASS |
| 26-A2 | pp. 475-476 | algorithm | MDS reflection, expansion, and contraction of a simplex | precise algorithm sketch / general | citation-only | simplex geometry | BENCHMARK_CANDIDATE | BENCHMARK-COMPARISON | no executable heuristic; exact stopping contract encoded |
| 26.3 | p. 476 | equation | Relative 1-norm simplex-size stopping test | precise / general | definition | finite 1- and max-norms | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `vecOneNorm`, `mdsRelativeSize`, `mdsConverged` / PASS |
| 26-C1 | p. 476 | cited convergence prose | Pattern-search limit points are stationary under compactness, smoothness, and further technical conditions | partly precise | citation-only | omitted Torczon conditions | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded; exact hypotheses are not printed |
| 26-E2 | pp. 477-478, Sec. 26.3.1 | experiment | `rcond`/`condest` counterexample searches and decimal matrices | empirical runs | none | Chapter 15 estimators | SKIP | SKIP-EMPIRICAL | not encoded |
| 26-E3 | pp. 478-479, Sec. 26.3.2 | algorithm/example | Strassen inversion formulas and direct-search stability experiment | exact formula plus empirical output | Chapter 23 reference / none for output | matrix inverse and fast multiplication | BENCHMARK_CANDIDATE | BENCHMARK-COMPARISON | formula reused conceptually; experiment not encoded |
| 26.4 | p. 478 | equation | Normalized minimum of left and right inverse residuals | precise / general | definition | repository `infNorm`, `matMul`, `idMatrix` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `inverseResidualStabilityMeasure` / PASS |
| 26-D2 | p. 479 | exact identity | Depressing a monic cubic by `x=y-a/3` | precise / symbolic family | derivation | field algebra | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `depressedCubic_identity` / PASS |
| 26.5 | p. 479 | equation | Two quadratic-formula branches for `w^3` | precise / symbolic family | derivation | real square root | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `cubicWCubePlus_quadratic`, `cubicWCubeMinus_quadratic` / PASS |
| 26.6 | p. 480 | equation | Cancellation-avoiding branch selected by the sign of `q` | precise formula / symbolic family | explanation | (26.5) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `stableSign`, `stableCubicWCube_eq_branch`, `stableCubicWCube_quadratic` / PASS |
| 26-E4 | pp. 480-481 | experiment | Cubic-root decimal searches and claims of observed instability | empirical run | none | historical MATLAB routines | SKIP | SKIP-EMPIRICAL | not encoded |
| 26.7 | p. 481 | equation | Normalized maximum cubic residual objective | precise definition / symbolic family | definition | complex norm, finite maximum | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `monicCubic`, `cubicRootResidualMeasure` / PASS; no invented meaning for "of order u" |
| 26-D3 | pp. 481-482, Sec. 26.4 | definitions | Closed intervals, width, and exact `+,-,*,/` endpoint formulas | precise / general | direct | ordered-field arithmetic | FORMALIZE_CORE | CORE-PRECISE-PROSE | `RealInterval`, `add`, `sub`, `mul`, `reciprocal`, `div`; soundness theorems / PASS |
| 26-D4 | p. 481, Sec. 26.4 | computed FP claim | Rounding left endpoints toward `-infinity` and right endpoints toward `+infinity` makes the computed interval operation contain `fl([x] op [y])` | precise implementation-facing enclosure claim / finite real endpoints | explanatory prose | repository IEEE directed rounding and exact endpoint hulls | FORMALIZE_CORE | CORE-PRECISE-PROSE | `outwardRounded`, `outwardAdd/Sub/Mul/Div` and containment theorems / PASS on the finite-real range; IEEE overflow belongs to the infinity-valued result layer |
| 26-P1 | p. 482 | symbolic example | `[1,2]-[1,2]=[-1,1]` dependency widening | precise / fixed exact witness | direct | interval subtraction | FORMALIZE_CORE | CORE-SYMBOLIC-EXAMPLE | `dependency_sub_example` / PASS |
| 26-Q1 | pp. 482-484 | qualitative analysis | Wrapping, exponential width growth, and condition-number product discussion | approximate/qualitative | citations and heuristic | interval algorithms | SKIP | SKIP-QUALITATIVE | not encoded |
| 26.8 | p. 484 | equation | Linearized forward-error expression "to first order" | partly precise / general | survey/citation | a formal first-order remainder model | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded; no remainder or asymptotic semantics is stated |
| 26-L1 | pp. 484-486 | literature/software survey | CENA, Miller, CESTAC, PRECISE, and other tools | editorial/empirical | literature review | external software | SKIP | SKIP-LITERATURE-REVIEW | not encoded |
| 26.1P | p. 487 | problem | Direct-search CGS/MGS orthogonality objectives | precise objective but experiment-oriented | none | Chapter 19 QR | BENCHMARK_CANDIDATE | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 26.2P | p. 487; App. A p. 570 | problem/solution | Sherman-Morrison solve stability search; Appendix reports order-one backward error and an open bound | empirical plus research question | empirical/open | rank-one update analysis | BENCHMARK_CANDIDATE | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded; Appendix explicitly leaves theory open |
| 26.3P | p. 487 | research problem | Stability of cubic-root formulas | research problem | none | complete floating-point cubic model | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 26.4P | p. 487 | research problem | Direct search on research problems from earlier chapters | open-ended research | none | multiple chapters | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |

## Computed-object classification

| Source algorithm | Inputs | Computed objects | Analysis-only objects | Core disposition |
|---|---|---|---|---|
| AD/MDS/Nelder-Mead | objective, start point/simplex, tolerance | heuristic iterates and function values | hypothetical global/local maximizer | Stopping predicates only; benchmark candidate |
| Cubic formulas | real coefficients | rounded roots in the experiment | exact depressed cubic and exact `w^3` branches | Exact algebra and residual objective formalized; historical output skipped |
| Interval arithmetic | endpoint intervals and directed rounding mode | exact endpoint operations; computed outward-rounded endpoints | represented real values and rounded operation results | Exact-real soundness and concrete finite-range outward-rounded producers formalized |
