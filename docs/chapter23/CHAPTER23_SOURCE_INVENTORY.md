# Higham Chapter 23 Source Inventory

## Source and scope

- Edition: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
- Chapter: 23, "Fast Matrix Multiplication", printed pp. 433--449.
- Source: `References/1.9780898718027.ch23.pdf` (17 PDF pages), visually checked against rendered pages.
- Mode: core; Split 4.
- Planning corrections: the PDF has 25 equation labels, not 26 (the extra plain `(23.7)` was a cross-reference to `(23.7a)--(23.7b)`), and ten Problems including omitted Problem 23.5.

## Body inventory in source order

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| 23.1 | p. 434 | equation | Conventional matrix-product entry | precise | general | definition | finite sums | REUSE_EXISTING | REUSE-REPOSITORY | `rectMatMul` / Mathlib matrix multiplication -- REUSED |
| 23.2 | p. 434 | equation | Winograd adjacent-pair inner-product identity | precise | general, even length | complete algebra | finite sums | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23_eq23_2_winograd_identity` -- PROVED |
| 23.3 | p. 434 | equation | `2 x 2` block product partition | precise | general | definition | block matrices | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `Higham23Block2`, `higham23BlockMul` -- PROVED exact model |
| 23.4 | p. 435 | equation/algorithm | Strassen seven-product formulas | precise | noncommutative blocks | complete algebra | distributivity | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23Strassen2`; correctness theorem -- PROVED |
| 23.5 | p. 435 | equation | Exact multiplication/addition counts at recursion threshold | precise | powers of two | stated | finite recurrences | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23StrassenCosts`, recurrence solutions, and `higham23_eq23_5_strassen_costs` -- PROVED from executable count semantics |
| 23.6 | p. 436 | equation/algorithm | Winograd's 15-addition Strassen variant | precise | noncommutative blocks | complete algebra | distributivity | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23WinogradStrassen2`; correctness theorem -- PROVED |
| Emp. 23.E1 | p. 436 | empirical outputs | historical speedups and crossover dimensions | underspecified | empirical runs | none | machines/libraries | SKIP | SKIP-EMPIRICAL | not encoded |
| Figure 23.1 | p. 437 | figure | exponent versus publication time | editorial | literature summary | not applicable | publications | SKIP | SKIP-FIGURE-TABLE | not encoded |
| 23.7a | p. 436 | equation | Bilinear reconstruction from products `P_k` | precise | general | definition | coefficient tensors | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23BilinearEvaluate`, `higham23_eq23_7a`, and exact correctness predicate -- PROVED evaluator surface |
| 23.7b | p. 436 | equation | Bilinear products from coefficient-weighted inputs | precise | general | definition | coefficient tensors | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23BilinearProduct`, `higham23_eq23_7b` -- PROVED evaluator surface |
| 23.8 | p. 437 | equation | Three-real-multiplication complex scalar identity | precise | noncommutative blocks | complete algebra | distributivity | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23ThreeM`; correctness theorem -- PROVED jointly with (23.9) |
| 23.9 | p. 438 | equation/algorithm | 3M real/imaginary matrix-product formulas | precise | noncommutative blocks | complete algebra | (23.8) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23ThreeM`; `higham23_eq23_9_threeM_correct` -- PROVED |
| 23.10 | p. 438 | equation | Conventional componentwise first-order error bound plus `O(u²)` | precise asymptotic (`u -> 0`, fixed `n`) | general | Chapter 3 | FP matrix multiply, asymptotics | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23FlMatrixMul`, exact-gamma componentwise theorem, explicit quadratic remainder, and `higham23_gammaRemainder_isBigO_u_sq` -- PROVED |
| 23.11 | p. 438 | equation | Generic polynomial-algorithm norm bound for some dimension constant `f_n` | precise existential asymptotic | general | citation/no proof | Miller result | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `Higham23FirstOrderExpansion`, constructive producer/nonzero witness, and `higham23_eq23_11_miller_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| Thm. 23.1 | p. 439 | theorem | Winograd computed inner product error `n gamma_(n/2+4)(||x||+||y||)^2` | precise | even dimension | complete | computed Winograd path, gamma calculus | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham23FlWinogradInnerProduct`, factor expansion, `higham23_theorem23_1_winograd_error` -- PROVED on actual rounded path |
| 23.12 | p. 439 | equation | Theorem 23.1 bound | precise | even dimension | complete | theorem path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23_theorem23_1_winograd_error` -- PROVED |
| 23.13 | p. 439 | equation | Conventional inner-product gamma bound | precise | general | Chapter 3 | existing dot-product result | REUSE_EXISTING | REUSE-REPOSITORY | repository dot-product bounds; no new wrapper |
| 23.B1 | pp. 439--440 | precise prose | balanced scaling gives displayed Winograd matrix norm bound | precise except informal choice of power-of-base scale | general | derivation | Thm. 23.1 | FORMALIZE_CORE | CORE-PRECISE-PROSE | `higham23_balanced_sum_sq_le`, `higham23_balanced_winograd_error` -- PROVED uniformly for the computed inner products underlying the max-entry matrix bound |
| Thm. 23.2 | p. 440 | theorem | Strassen forward error with coefficient and second-order remainder | precise asymptotic (`u -> 0`, fixed dimensions/depth) | powers of two | complete first-order proof | recursive rounded blocks, asymptotics | FORMALIZE_CORE | CORE-NAMED-RESULT | canonical recurrence and `higham23_theorem23_2_strassen_explicitDomain`, with constructive domain producer -- PASS (EXPLICIT-DOMAIN) |
| 23.14 | p. 440 | equation | Theorem 23.2 asymptotic bound | precise asymptotic | general | complete | theorem path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23StrassenClosedCoefficient` and named explicit-domain theorem -- PASS (EXPLICIT-DOMAIN) |
| 23.15 | p. 440 | equation/model | Inductive error form with second-order remainder | precise asymptotic | general | proof-local | recursive error semantics | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `Higham23FirstOrderExpansion` records the linear coefficient and bounded quadratic remainder locally -- PROVED dependency |
| 23.16 | p. 441 | equation | Exact recurrence `c_k=12c_(k-1)+46*2^(k-1)` | precise | natural recursion depth | complete | arithmetic | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | canonical `higham23StrassenErrorCoefficient`, actual recurrence equation, and source closed-coefficient upper bound -- PROVED arithmetic |
| 23.17 | p. 442 | equation | Conventional normwise first-order bound plus second-order remainder | precise asymptotic | general | derived from (23.10) | max norm, asymptotics | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `Higham23MaxEntryNormLe`, `higham23_eq23_17_conventional_normwise`; printed `n²u` plus explicit `O(u²)` remainder -- PROVED |
| Emp. 23.E2 | p. 442 | symbolic plus machine example | small-entry Strassen cancellation example and Pascal MATLAB output | mixed | symbolic/empirical | explanatory | exact Strassen formulas | FORMALIZE_DEPENDENCY / SKIP | CORE-SYMBOLIC-EXAMPLE / SKIP-EMPIRICAL | exact formula available from (23.4); machine output not encoded |
| Thm. 23.3 | pp. 442--443 | theorem | Winograd--Strassen forward error with coefficient and second-order remainder | precise asymptotic | powers of two | sketch | rounded recursive blocks, asymptotics | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham23_theorem23_3_winogradStrassen_explicitDomain` plus constructive producer -- PASS (EXPLICIT-DOMAIN) |
| 23.18 | p. 442 | equation | Theorem 23.3 asymptotic bound | precise asymptotic | general | sketch | theorem path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | canonical recurrence, `higham23WinogradStrassenClosedCoefficient`, and named domain theorem -- PASS (EXPLICIT-DOMAIN) |
| Figure 23.2 | p. 444 | empirical output | random-matrix error curves | underspecified | empirical run | none | compiler/machine/RNG details | SKIP | SKIP-EMPIRICAL | not encoded |
| Thm. 23.4 | p. 443 | theorem | Bini--Lotti recursive bilinear forward error for constants determined by algorithm tensors | precise existential asymptotic; exact formulas external | general | citation-only | external `alpha`,`beta`, rounded evaluator | FORMALIZE_CORE | CORE-NAMED-RESULT | tensor support count, explicit positive constants, first-order domain theorem, and nonvacuity producer -- PASS (EXPLICIT-DOMAIN) |
| 23.19 | p. 443 | equation | Theorem 23.4 asymptotic bound | precise existential asymptotic | general | citation-only | external paper | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23BiniLottiCoefficient`, `higham23_theorem23_4_biniLotti_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| 23.20 | p. 445 | equation | Conventional real-part componentwise first-order 3M comparison | precise asymptotic | general | straightforward | FP matmul/add | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | actual two-dot subtraction, exact `gamma_(n+1)` bound, explicit quadratic remainder, and `O(u²)` remainder theorem -- PROVED |
| 23.21 | p. 445 | equation | Conventional imaginary-part componentwise first-order bound | precise asymptotic | general | straightforward | FP matmul/add | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | actual two-dot addition, exact `gamma_(n+1)` bound, explicit quadratic remainder, and `O(u²)` remainder theorem -- PROVED |
| 23.22 | p. 445 | equation | 3M imaginary-part componentwise first-order bound | precise asymptotic | general | stated | computed 3M path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | actual rounded 3M path, exact `gamma_(n+4)` bound, explicit quadratic remainder, and `O(u²)` remainder theorem -- PROVED |
| 23.B2 | p. 445 | precise prose | Bounds (23.20)--(23.22), including their remainder families, are invariant under diagonal scaling | precise asymptotic | general | stated | computed path and scaling | FORMALIZE_CORE | CORE-PRECISE-PROSE | `higham23_abs_product_diagonal_scaling`, `higham23_threeM_budget_diagonal_scaling`; the explicit remainder multiplies the same budget -- PROVED |
| 23.23 | p. 445 | equation | Conventional imaginary-part normwise asymptotic bound | precise asymptotic | general | derived | norms | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23_eq23_23_conventional_imaginary_normwise`, actual rounded matrix path and induced infinity norm -- PROVED |
| 23.24 | p. 445 | equation | 3M imaginary-part normwise asymptotic bound | precise asymptotic | general | derived | norms | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham23_eq23_24_threeM_imaginary_normwise`, including sharp `sqrt 2` weakening -- PROVED |
| 23.B3 | p. 446 | precise prose | 3M plus Strassen has modified (23.14) coefficient | precise asymptotic | general | no proof; Problem 23.6 | combined rounded path | FORMALIZE_CORE | CORE-PRECISE-PROSE | `higham23ThreeMStrassenCoefficient`, Problem 23.6 explicit-domain theorem and producer -- PASS (EXPLICIT-DOMAIN) |
| 23.N | pp. 446--448 | notes/references | history, implementations, and literature survey | editorial | editorial | not applicable | external literature | SKIP | SKIP-LITERATURE-REVIEW | inventoried; not encoded |

## Algorithms and computed quantities

| Algorithm/source | Inputs | Outputs | Exact object | Computed object | Computed quantities | Analysis-only objects | Target claims |
|---|---|---|---|---|---|---|---|
| Winograd inner product, (23.2) | even-length `x,y` | scalar inner product | pair identity | rounded sums/products | pair sums/products and three accumulations | exact dot product | Thm. 23.1 |
| Strassen, (23.4) | block matrices `A,B` | block product | seven-product expression | recursively rounded blocks | block sums, seven products, output recombinations | exact `AB` | Thm. 23.2 |
| Winograd--Strassen, (23.6) | block matrices `A,B` | block product | seven-product expression | recursively rounded blocks | eight `S`, seven `M`, two `T`, output sums | exact `AB` | Thm. 23.3 |
| bilinear algorithm, (23.7) | tensors `U,V,W`, matrices | product | coefficient reconstruction | recursive rounded evaluator | weighted sums/products at every level | exact bilinear map | Thm. 23.4 |
| 3M, (23.9) | real/imaginary matrix parts | complex product | three-real-product identity | rounded real products/sums | `T1,T2`, combined product, subtractions | exact complex product | (23.20)--(23.24) |

## Problems and owned Appendix A solutions

| Source | Summary | Appendix A | Decision | Reason/status |
|---|---|---|---|---|
| 23.1 | rectangular complexity from square exponent | solution present | BENCHMARK_CANDIDATE | exact optional complexity theorem |
| 23.2 | Winograd operation count | solution present | BENCHMARK_CANDIDATE | exact optional count |
| 23.3 | Strassen count ratios | solution present | SKIP | asymptotic estimate optional |
| 23.4 | rectangular Strassen count | none | BENCHMARK_CANDIDATE | exact optional count |
| 23.5 | compare two scalar formulas | solution present | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED |
| 23.6 | 3M plus Strassen error bound | none | FORMALIZE_DEPENDENCY | `higham23_problem23_6_threeM_strassen_explicitDomain` and nonvacuity producer -- PASS (EXPLICIT-DOMAIN) |
| 23.7 | compare two fast complex approaches | brief Appendix reference | SKIP | qualitative speed/storage exercise |
| 23.8 | recursive Strassen inversion | none | BENCHMARK_CANDIDATE | exact algorithm; cross-chapter dependency |
| 23.9 | block upper-triangular inverse reduces multiplication to inversion | solution present | BENCHMARK_CANDIDATE | exact optional theorem |
| 23.10 | extensive numerical experiments | none | SKIP | SKIP-EMPIRICAL |

## Gate summary

The inventory and all Problems/Appendix rows are complete. The selected-scope gate is **PASS**. Actual rounded evaluators close Theorem 23.1, (23.10), (23.17), and (23.20)--(23.24). The citation-dependent generic and recursive rows (23.11), Theorems 23.2--23.4, and 23.B3/Problem 23.6 are terminal **PASS (EXPLICIT-DOMAIN)** results over a local first-order polynomial expansion; that domain has a constructive producer and concrete nonzero/nonempty witnesses and does not assume the final norm bound. Standard `O(u²)` is represented by an explicit bounded quadratic coefficient, with the gamma remainder additionally proved `IsBigO` at `u -> 0`.
