# Chapter 8 Formalization Report

Date: 2026-06-20.
Source: `References/1.9780898718027.ch8.pdf`.
Appendix source read: `References/1.9780898718027.appa.pdf`.
Split contract: Split 2, Chapter 8.
Mode: proof-completion pass for Split 2.

`PREVIOUS_SPLITS = 1` in this pass.  Every `WAIT-PREVIOUS-SPLIT`
row below refers to Split 1 only, not to earlier chapters in Split 2.

## Summary

This pass kept the existing Chapter 8 module organization:

- source-facing wrappers in `LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`;
- triangular solve proofs in `TriangularSolve.lean` and `ForwardSub.lean`;
- comparison-matrix, inverse-bound, and M-matrix proofs in
  `TriangularForwardComparison.lean`, `InverseBounds.lean`, and `MMatrix.lean`.

Newly closed proof-facing work in this pass:

- `compMatrix_inv_upper_row_eq_ones`: exact algebraic recurrence behind
  Algorithm 8.13, `|u_ii| y_i = 1 + sum_{j>i} |u_ij| y_j`.
- `higham8_13_y` and `higham8_13_comparison_inverse_row_recurrence`: source
  Chapter 8 wrappers for that recurrence.
- `higham8_14_infNorm_lowerBound`: source-facing lower-bound part of (8.9) for
  the infinity norm, using the existing row-sum lower-bound theorem.
- `higham8_8_rankOne_singular_update`: constructive "possible" branch of
  Problem 8.8(a), proving that the displayed rank-one perturbation is singular
  when the corresponding inverse entry is nonzero.

No source theorem is claimed complete unless its row is classified `CLOSED`.
Rows with a closed specialization keep the full source-general row visible when
the full theorem is still blocked by Split 1 or deferred by the split plan.

## Primary Label Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations | Notes |
| --- | --- | --- | --- | --- |
| Algorithm 8.1, back substitution | `CLOSED` | Uses available Split 1 rounding model through `FPModel`; no unresolved previous-split dependency | `fl_backSub`, `higham8_1_backSub` | Concrete repository algorithm. |
| Lemma 8.2, ordered scalar row error | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `BackSubRowSpec`, `backSub_row_tight`, `higham8_2_backSub_row_spec`, `higham8_2_backSub_row_tight` | Row-tight proof chain for the repository evaluation order. |
| Theorem 8.3, Algorithm 8.1 backward error | `CLOSED` | Uses available Split 1 `H02.rounding_model` and `H03.gamma_theta`; no unresolved previous-split dependency | `backSub_backward_error_algorithm_8_1`, `higham8_3_backSub_backward_error` | Row-specific constants match the zero-based Lean translation of the source constants. |
| Lemma 8.4, arbitrary evaluation-order scalar error | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Split 1 owns the general gamma/theta and expression-tree/product rounding infrastructure. It should not be reproved locally because Chapter 8 should consume the shared Split 1 evaluation-order contract rather than defining a parallel rounding algebra. |
| Theorem 8.5, substitution in any ordering | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | Closed fixed-order specializations: `backSub_backward_error`, `forwardSub_backward_error`, `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error` | The full source theorem quantifies over arbitrary evaluation ordering. The fixed forward/back substitution orders are proved, but the arbitrary-order wrapper waits for Split 1 `H03.gamma_theta`/expression-order infrastructure. |
| Lemma 8.6, condition (8.5) implies the triangular inverse product bound | `CLOSED` | No previous-split dependency | `IsDiagDominantUpper`, `inv_abs_mul_bound_diagDom`, `higham8_6_inv_abs_mul_bound_diagDom` | Genuine triangular inverse recurrence/geometric proof. |
| Theorem 8.7, componentwise forward error under (8.5) | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `backSub_forward_error_diagDom`, `higham8_7_backSub_forward_error_diagDom` | Proof reuses the backward-error theorem and Lemma 8.6. |
| Lemma 8.8, row-dominant upper-triangular bound and `cond(U) <= 2n-1` | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | Source condition recorded as `higham8_rowDominantUpperSource` | The PDF condition is faithfully recorded with the printed inequality direction `|u_ii| <= sum_{j>i} |u_ij|`. The full lemma needs Split 1 `H06.norms`/condition-number interfaces; local row-dominant inverse algebra remains a current-split subgoal once that interface is fixed. |
| Lemma 8.9, comparison-matrix condition-number identity | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | `comparisonMatrix`, `higham8_7_comparisonMatrix` | The missing result is the exact `cond(M(T),x)` API over Split 1 norm/condition-number foundations. It should not be redeclared locally with a Chapter 8-only condition-number definition. |
| Theorem 8.10, comparison-matrix forward error | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Formalized in exact `mu`-recurrence form instead of an informal `O(u^2)` abbreviation. |
| Corollary 8.11, M-matrix high relative accuracy | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `mmatrix_forwardSub_relative_error`, `higham8_11_mmatrix_forwardSub_relative_error` | Closed for lower triangular M-matrices and `b >= 0` in exact `mu` form. |
| Theorem 8.12, inverse comparison chain | `WAIT-PREVIOUS-SPLIT` | Yes, direct and indirect previous-split dependency | Closed first inequality: `abs_inv_le_compMatrix_inv`, `abs_inv_le_compMatrix_inv_lowerTri`, `higham8_12_abs_inv_le_comparison_inv` | The full source chain quantifies over vector norms and the `W(U)`/`Z(U)` minorants. Direct Split 1 gate: `H06.norms`; indirect gate: current-split `W/Z` interfaces should use that norm API rather than local stand-ins. |
| Algorithm 8.13, compute `mu = ||M(U)^-1||_inf >= ||U^-1||_inf` | `CLOSED` | No previous-split dependency | `higham8_13_y`, `compMatrix_inv_upper_row_eq_ones`, `higham8_13_comparison_inverse_row_recurrence`, `higham8_13_mu`, `higham8_13_inverse_bound_from_comparison` | Closed as an exact semantic computation and certified upper-bound theorem. The `O(n^2)` flop count is treated as an expository cost statement, not a Lean theorem. |
| Theorem 8.14, norm bounds under (8.5) | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | Closed infinity-norm pieces: `triInv_row_sum_lowerBound`, `triInv_row_sum_upperBound`, `triInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound` | The full source theorem covers 1-, 2-, and infinity-norm chains through `M/W/Z`; direct gate is Split 1 `H06.norms`, with local `W/Z` minorant work still to integrate after that API is fixed. |

## Numbered Equation Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| (8.1), rowwise backward-error identity | `CLOSED` | Uses available Split 1 gamma infrastructure | `backSub_row_tight`, `higham8_2_backSub_row_tight` | Source equation appears as the row-tight theorem. |
| (8.2), forward-error condition-number bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 `H06.norms`/condition-number API; should not be locally redefined. |
| (8.3), stress matrix `U(alpha)` | `CLOSED` | No previous-split dependency | `higham8_3_stressUpper` | Displayed definition. |
| (8.4), displayed inverse-entry formula | `CLOSED` | No previous-split dependency | `higham8_4_stressUpperInvFormula` | Displayed formula is encoded. A separate inverse-identity theorem is not claimed. |
| (8.5), diagonal-dominant upper triangular condition | `CLOSED` | No previous-split dependency | `IsDiagDominantUpper` | Existing predicate. |
| (8.6), lower-triangular analogue | `CLOSED` | No previous-split dependency | `higham8_6_diagDominantLower` | Source-facing predicate. |
| (8.7), comparison matrix | `CLOSED` | No previous-split dependency | `comparisonMatrix`, `higham8_7_comparisonMatrix` | Existing definition plus source wrapper. |
| (8.8), `mu` recurrence | `CLOSED` | Uses available Split 1 gamma infrastructure | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Encoded as the exact recurrence driving Theorem 8.10. |
| (8.9), Theorem 8.14 norm chain | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound` close the infinity-norm endpoints | Full 1-/2-/infinity chain waits for Split 1 norm infrastructure and current-split `W/Z` integration. |
| (8.10), QR column-pivoting inequality | `DEFER-LATER-SPLIT` | No direct previous-split dependency; later deferred block also uses norm infrastructure | none | Belongs with the later QR/factorization split/chapter material referenced by Problem 19.5. |
| (8.11), Kahan matrix family | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | related unscaled base: `higham8_3_stressUpper` | Exact singular-value claims need Split 1 `H06.svd`. |
| (8.12), fan-in factorization `L=L_1...L_n` | `WAIT-PREVIOUS-SPLIT` | Yes, indirect previous-split dependency | none | The fan-in proof depends on matrix-product/fan-in rounding infrastructure gated by Split 1 `H03.gamma_theta`. |
| (8.13), fan-in product formula | `WAIT-PREVIOUS-SPLIT` | Yes, indirect previous-split dependency | none | Same fan-in matrix-product blocker as (8.12). |
| (8.14), rounded fan-in product expansion | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 matrix/product rounding model. |
| (8.15), fan-in componentwise residual bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 gamma/product bounds plus the current-split fan-in algorithm. |
| (8.16), fan-in norm residual bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 `H06.norms` and `H03.gamma_theta`. |
| (8.17), Sameh-Brent backward bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 product rounding and norm infrastructure. |
| (8.18), fan-in forward comparison bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 product rounding and comparison/norm interfaces. |
| (8.19), weakened fan-in forward bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Same blocker family as (8.18). |
| (8.20), condition-cubing fan-in bound | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 `H06.condition_distance`/norm APIs plus current fan-in infrastructure. |

## Problems And Appendix A Inventory

Appendix A contains printed solutions for Problems 8.1, 8.2, 8.3, 8.4, 8.5,
8.7, 8.8, 8.9, and 8.10. No printed Appendix A solution for 8.6 was present in
the extracted text.

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| Problem 8.1, no guard-digit backward error | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs the Split 1 `H02.rounding_model` no-guard-digit variant connected to triangular row proofs. |
| Problem 8.2, arbitrarily large `||M(T)^-1||/||T^-1||` example | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | The symbolic 3-by-3 matrices are local, but the source ratio/asymptotic claim needs Split 1 norm/asymptotic interfaces. |
| Problem 8.3, explicit bound from Theorem 8.10 | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Depends on Theorem 8.10 plus Split 1 norm/asymptotic simplification interfaces. |
| Problem 8.4, M-matrix `cond(T,x) <= 2n-1` for `x >= 0` | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs the shared condition-number API over Split 1 norm foundations; local nilpotent/M-matrix monotonicity should be proved against that API, not a local duplicate. |
| Problem 8.5, closed form for `||Z(T)^-1||` | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs Split 1 1-/infinity-norm APIs and current-split `Z(T)` definition. |
| Problem 8.6, efficient computation of `||M(U)^-1 |z|||_inf` and `||W(U)^-1 |z|||_inf` | `WAIT-PREVIOUS-SPLIT` | Yes, indirect previous-split dependency | none | The cost/algorithm statement depends on the same `M/W` norm interfaces as Theorem 8.12. |
| Problem 8.7, strictly row diagonally dominant inverse norm theorem | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Needs general matrix infinity-norm/inverse API from Split 1 norm foundations. |
| Problem 8.8(a), constructive singular rank-one perturbation when `(A^-1)_{ji} != 0` | `CLOSED` | No previous-split dependency | `higham8_8_rankOne_singular_update` | This is the positive branch of the source iff statement. |
| Problem 8.8(a), converse/no-update branch and best perturbation location | `WAIT-PREVIOUS-SPLIT` | Yes, indirect previous-split dependency | none | Needs a reusable determinant/rank-one update API and finite max-entry/norm conventions aligned with Split 1 norm foundations. The positive branch above is closed. |
| Problem 8.8(b), `T_n + alpha e_n e_1^T` singular example | `WAIT-PREVIOUS-SPLIT` | Yes, indirect previous-split dependency | none | Depends on the full Problem 8.8(a) rank-one API and the stress-matrix inverse identity around (8.4). |
| Problem 8.9, Kahan singular-value formula | `WAIT-PREVIOUS-SPLIT` | Yes, direct previous-split dependency | none | Exact source statement needs Split 1 `H06.svd` and singular-value interlacing. |
| Problem 8.10, rational-function triangular solver theorem/counterexample | `SKIP` | No previous-split dependency | none | The problem describes a broad algorithm family plus a counterexample without a fixed executable solver model in the Split 2 contract. It is recorded as underspecified for this pass. |

## Source-Level Side Conditions And Prose Claims

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| Nonsingular upper/lower triangular diagonal hypotheses | `CLOSED` | No previous-split dependency | `hU : forall i, U i i != 0`, `hUT`, `hLT`, `IsInverse`, `IsRightInverse` across wrappers | Represented explicitly as theorem hypotheses. |
| Gamma-valid small-unit-roundoff side conditions | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved dependency | `gammaValid fp n`, `gammaValid fp (n+1)`, `gammaValid fp (2*n)` | No orphan typeclass hypotheses are used to hide these assumptions. |
| Condition (8.5) and lower analogue (8.6) | `CLOSED` | No previous-split dependency | `IsDiagDominantUpper`, `higham8_6_diagDominantLower` | The upper condition uses `|u_ij| <= |u_ii|` for `j>i`. |
| Printed row-dominant condition before Lemma 8.8 | `CLOSED` as a source condition | No previous-split dependency | `higham8_rowDominantUpperSource` | PDF audit confirms the source prints `|u_ii| <= sum_{j>i} |u_ij|`; no theorem is claimed from this condition. |
| `b >= 0` and M-matrix sign hypotheses in Corollary 8.11 | `CLOSED` | No previous-split dependency beyond available gamma results | `higham8_11_mmatrix_forwardSub_relative_error` hypotheses | Nonnegativity conclusions are proved, not assumed as theorem-equivalent fields. |
| Cost claims such as `O(n^2)`, `O(n)`, and `O(1)` flops | `SKIP` | No previous-split dependency | none | Pure complexity prose is outside the current Lean cost model. |
| Informal `O(u^2)` abbreviations | `SKIP` | Later exact asymptotic APIs may use Split 1, but no theorem is claimed here | exact `mu` forms instead | The formal statements use exact recurrence bounds rather than informal Big-O text. |

## Dependency Details For `WAIT-PREVIOUS-SPLIT`

| Row family | Previous split | Contract family or missing result | Direct or indirect | Why not local |
| --- | --- | --- | --- | --- |
| Arbitrary evaluation order: Lemma 8.4 and full Theorem 8.5 | Split 1 | `H03.gamma_theta` plus expression-tree/product rounding interfaces | Direct | Reproving would duplicate the shared rounding algebra owned by Split 1. |
| No-guard variant: Problem 8.1 | Split 1 | `H02.rounding_model` / no-guard subtraction variant | Direct | The rounding model variant must be global, not a Chapter 8-only assumption. |
| Condition numbers and norm-general statements: (8.2), Lemmas 8.8/8.9, Theorems 8.12/8.14, Problems 8.2-8.7 | Split 1 | `H06.norms`, `H06.condition_distance`, and condition-number APIs | Direct | Local definitions would produce incompatible condition-number statements for later chapters. |
| Singular-value/Kahan rows: (8.11), Problem 8.9 | Split 1 | `H06.svd` and singular-value interlacing/factorization lemmas | Direct | These are shared spectral foundations, not Chapter 8-specific facts. |
| Fan-in equations (8.12)-(8.20) | Split 1 | `H03.gamma_theta` matrix-product/fan-in rounding; `H06.norms` for norm forms | Direct for rounding/norm bounds; indirect through the current fan-in algorithm interface | The fan-in algorithm should consume the Split 1 product and norm contracts rather than reintroducing product-error models. |

## Verification Ledger

Focused commands run after this pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.InverseBounds LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean`

Repository health commands run after this pass:

- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/InverseBounds.lean examples/LibraryLookup.lean`
- `git diff --check`
- `#print axioms` for:
  - `LeanFpAnalysis.FP.compMatrix_inv_upper_row_eq_ones`
  - `LeanFpAnalysis.FP.higham8_13_comparison_inverse_row_recurrence`
  - `LeanFpAnalysis.FP.higham8_14_infNorm_lowerBound`
  - `LeanFpAnalysis.FP.higham8_14_infNorm_upperBound`
  - `LeanFpAnalysis.FP.higham8_8_rankOne_singular_update`

Results:

- Focused Chapter 8/InverseBounds build passed:
  `Build completed successfully (2426 jobs).`
- `examples/LibraryLookup.lean` passed.
- Code scan over the touched Chapter 8 Lean files and lookup example found no
  `sorry`, `admit`, `axiom`, or `unsafe`.
- Repository-wide Lean/example scan for `sorry`, `admit`, `axiom`, and `unsafe`
  found no matches.
- Chapter 8 TODO/FIXME scan found no matches.
- A broader local placeholder scan found no Chapter 8 `placeholder`, `vacuous`,
  or `theorem-equivalent` markers.  Existing `certificate` lookup entries were
  pre-existing outside this Chapter 8 pass and are not theorem-equivalent
  assumptions introduced here.
- `git diff --check` passed.
- `#print axioms` for the five new final-facing declarations reported only
  standard Lean/mathlib foundations: `propext`, `Classical.choice`, and
  `Quot.sound`.
- Full `lake build` passed: `Build completed successfully (3476 jobs).`
  Remaining warnings are pre-existing QR/FastMatMul linter warnings outside
  Chapter 8.

The Lean files contain no new `sorry`, `admit`, `axiom`, or `unsafe`; no orphan
classes are used as theorem hypotheses; and the new definitions are not vacuous
theorem-equivalent assumptions.
