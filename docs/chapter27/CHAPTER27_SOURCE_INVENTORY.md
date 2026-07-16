# Higham Chapter 27 Source Inventory

## Audit basis

- Source: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed. (SIAM, 2002), Chapter 27, "Software Issues in Floating Point Arithmetic".
- Local source: `References/1.9780898718027.ch27.pdf`, printed pp. 489-509.
- Mode: core; parallel owner: Split 4.
- Source inspection: all 21 PDF pages were extracted, rendered, and visually
  checked. Appendix A solutions 27.1, 27.3, 27.5, 27.7, and 27.8 were checked on
  printed pp. 570-571.
- Primary named labels: none. Numbered equation ledger: (27.1).

## Inventory

| ID | Source location | Kind | Statement summary | Precision / generality | Source proof | Dependencies | Decision | Reason code | Lean artifact / status |
|---|---|---|---|---|---|---|---|---|---|
| 27-D1 | pp. 490-492, Sec. 27.1 | software model | IEEE exception kinds and sticky flags | precise specification / general | standards description | finite sets | FORMALIZE_CORE | CORE-PRECISE-PROSE | `FPException`, `ExceptionFlags`, `raiseException_mono`, `clearException` / PASS |
| 27-E1 | pp. 490-491 | examples | Dual norm, maximum scan, and continued-fraction behavior on IEEE values | mixed exact and machine behavior | explanatory | IEEE semantics | SKIP | SKIP-MACHINE-SPECIFIC | no machine execution encoded |
| 27-E2 | pp. 491-492 | software experiment | Exception-handling LAPACK estimator speedups/slowdowns | empirical timing | none | historical machines | SKIP | SKIP-EMPIRICAL | not encoded |
| 27-S2 | p. 493, Sec. 27.2 | advice | Equality testing and gradual-underflow observations | partly precise / implementation-specific | cross-reference | Chapter 2 FP model | SKIP | SKIP-QUALITATIVE | no arbitrary tolerance theorem invented |
| 27-S3 | pp. 493-494, Sec. 27.3 | historical case | Cray subtraction bias and Cholesky output table | empirical/hardware-specific | post-hoc explanation | Cray arithmetic | SKIP | SKIP-MACHINE-SPECIFIC | not encoded |
| 27-S4 | p. 494, Sec. 27.4 | compiler guidance | Parentheses and reassociation warning | language/compiler-specific | example | compiler semantics | SKIP | SKIP-PROGRAMMING-LANGUAGE | not encoded |
| 27-D2 | pp. 494-497, Secs. 27.5-27.7.1 | definition/spec | Base, precision, exponent limits, and portable arithmetic-model predicates | precise reusable vocabulary | survey | Chapter 2 model | FORMALIZE_CORE | DEP-REQUIRED | `ArithmeticParameters`, `PortableArithmeticModel` / PASS |
| 27-E3 | pp. 494-496 | algorithms/software | `machar`, paranoia, `xLAMCH`, FPV, FPTST, ELEFUNT | software descriptions and empirical testing | literature survey | compiler/runtime behavior | SKIP | SKIP-LITERATURE-REVIEW | not encoded |
| 27-S7 | pp. 496-499, Sec. 27.7 | software design | Portability, 2x2 LAPACK solvers, constants, Brown/LIA models | editorial/model survey | literature review | external standards | SKIP | SKIP-LITERATURE-REVIEW | only reusable parameter/model vocabulary encoded |
| 27-A1 | p. 499, Sec. 27.8 | algorithm | Printed two-pass norm: `t=‖x‖∞; s=Σ(xᵢ/t)²; output=t√s` | precise exact algorithm / general | direct explanation | finite norms, real division and square root | FORMALIZE_CORE | CORE-PRECISE-PROSE | exact correctness plus concrete finite round-to-even trace / PASS |
| 27-A2 | pp. 499-500, Sec. 27.8 | algorithm | Later Hammarling/LAPACK one-pass scaled sum-of-squares algorithm | exact arithmetic algorithm; FP safety separately stated | Appendix proof for Problem 27.5 | real algebra, square root | FORMALIZE_CORE | CORE-PRECISE-PROSE | `scaledSumSqStep`, fold invariants, `higham27_problem27_5_scaled_norm_correct_sq` / exact-arithmetic PASS |
| 27-D3 | p. 500, Sec. 27.8 | definitions | True complex-vector one-norm `Σ sqrt(re²+im²)` and BLAS `xCASUM` pseudo-one-norm `Σ(|re|+|im|)` | precise mathematical definitions / general | direct | complex modulus | REUSE_EXISTING (true norm), FORMALIZE_CORE (pseudo-norm/comparison) | REUSE-REPOSITORY / CORE-PRECISE-PROSE | repository `complexVecOneNorm`; `higham27BlasComplexPseudoOneNorm`; `higham27_complexVecOneNorm_le_blasComplexPseudoOneNorm` / PASS |
| 27-Q1a | p. 499 | implementation claim | The printed two-pass scaling algorithm avoids overflow | precise desired FP behavior / implementation-facing | explanatory prose | concrete overflow and rounded-operation semantics | FORMALIZE_CORE | CORE-PRECISE-PROSE | `twoPassRoundedScaledSum_bounds_and_safe` verifies a concrete round-to-even quotient/square/accumulation/final-product trace under explicit representability and capacity conditions / PASS |
| 27-Q1b | pp. 499-500 | cited algorithm summary | Blue's three-accumulator one-pass algorithm avoids both overflow and underflow and has an accuracy analysis | desired behavior is clear, but the chapter supplies no executor, thresholds, rounding order, or error-bound statement | qualitative plus citation | Blue [143, 1978] | DEFER | DEFER-MISSING-PRECISE-STATEMENT | no theorem invented from the prose summary; the separately printed Hammarling/Problem 27.5 exact invariant is verified |
| 27-D4 | p. 500 | displayed exact identity | Conventional complex quotient components `(ac+bd)/(c²+d²)` and `(bc-ad)/(c²+d²)` | precise / general away from zero denominator | direct algebra | Mathlib complex division | REUSE_EXISTING / FORMALIZE_DEPENDENCY | REUSE-MATHLIB | `Complex.div_re`, `Complex.div_im`; specialized in both local Smith-branch theorems / PASS |
| 27.1 | p. 500 | equation | Smith scaled complex-division formula for the `|c| >= |d|` branch | precise / general | direct algebra | complex division | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `smithDivReal_eq`, `smithDivImag_eq`, `higham27_eq27_1_smith_complex_division` / PASS |
| 27-A3 | p. 500, after (27.1) | algorithm identity | Analogous Smith branch using `c/d` when `|d| >= |c|` | precise / general | stated by symmetry | complex division | FORMALIZE_CORE | CORE-PRECISE-PROSE | `smithDivRealSymmetric_eq`, `smithDivImagSymmetric_eq`, `higham27_smith_complex_division_symmetric` / PASS |
| 27-Q2 | p. 500 | implementation claim | Smith's scaled branching is suggested as a simple way to avoid overflow, while underflow remains possible | informal unrestricted wording; false at the largest finite denominator endpoints | explanatory prose | branch selection, fixed-format rounding/range semantics | FORMALIZE_CORE | CORE-PRECISE-PROSE | scoped concrete traces `smith_first_branch_preDivision_safe` and `smith_symmetric_branch_preDivision_safe` PASS; unconditional reading REFUTED by `smith_scaledDenominator_overflows_at_maxFiniteMagnitude` |
| 27-S9 | pp. 501-503, Secs. 27.9-27.10 | software survey | Multiple, double-double, quad-double, MPFUN/MPFR, mixed-precision BLAS | software/history | literature review | external libraries | SKIP | SKIP-LITERATURE-REVIEW | not encoded |
| 27-S11 | pp. 503-504, Sec. 27.11 | historical incident | Patriot missile clock conversion and Table 27.2 | historical machine output | report | unavailable full machine model | SKIP | SKIP-MACHINE-SPECIFIC | not encoded |
| 27-P1 | pp. 505-506; App. A p. 570 | problem/solution | Machine epsilon discovery and compiler failure modes | machine/compiler-specific | Appendix prose | exact compiler and rounding semantics | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 27-P2 | p. 506 | problem | Derive Smith formula from 2x2 GEPP | precise optional exercise | none in Appendix A | Gaussian elimination | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | equation (27.1) itself is proved directly |
| 27-P3 | p. 506; App. A p. 570 | problem/solution | Malcolm base/precision discovery algorithm | software-specific | Appendix explanation | compiler/register semantics | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 27-P4 | pp. 506-507; App. A p. 571 | problem/solution | Defective random generator and underflow trace | empirical machine run | Appendix diagnosis | historical Fortran/RNG | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 27-P5 | p. 507; App. A p. 571 | problem/solution | Prove scaled `xNRM2` invariant and correctness | precise / general | complete Appendix proof | exact real algebra | FORMALIZE_CORE | CORE-PRECISE-PROSE | `scaledSumSqStep_invariant`, `scaledSumSqFold_invariant`, `higham27_problem27_5_scaled_norm_correct_sq` / PASS |
| 27-P6 | pp. 507-509 | problem | Moler-Morrison/Halley Pythagorean iteration | precise optional exercise plus FP claims | exercise | nonlinear iteration | BENCHMARK_CANDIDATE | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 27-P7 | p. 509; App. A p. 571 | problem/solution | Skew-symmetric square root and matrix Pythagorean iteration | precise optional exercise; research part | Appendix solves only part (a) | matrix square roots | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 27-P8 | p. 509; App. A p. 571 | problem/solution | Prefer `sqrt(|x|)/sqrt(3)` to `sqrt(|x|/3)` for robustness | implementation-facing optional observation | short Appendix answer | underflow model | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |

## Computed-object classification

| Path | Computed objects | Analysis-only objects | Status |
|---|---|---|---|
| Sticky flags | flag set after each operation | exception classification | reusable exact software spec encoded |
| Two-pass scaled norm | `t=‖x‖∞`, rounded normalized quotients/squares/accumulator, final `t*sqrt(s)` | exact sum of input squares and trace bounds | exact correctness plus concrete conditional no-overflow trace encoded |
| One-pass scaled norm | `scale`, `sumsq`, final `scale*sqrt(sumsq)` | represented exact sum `scale^2*sumsq` | exact path and invariant encoded; no quantified concrete FP range theorem is printed/selected, so range safety is not claimed |
| Complex one-norms | true complex moduli or separate absolute real/imaginary parts | comparison between the two sums | both printed definitions and `true ≤ xCASUM` encoded |
| Smith division | rounded `d/c`, products, scaled denominator, two components | conventional quotient components | exact identity and scoped pre-division rounded trace encoded; unconditional wording refuted at max-finite endpoints |
| Symmetric Smith division | rounded `c/d`, swapped products/denominator, two components | conventional quotient components | exact identity and scoped pre-division rounded trace encoded |
