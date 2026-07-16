# Higham Chapter 22 Source Inventory

## Source and scope

- Edition: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
- Chapter: 22, "Vandermonde Systems", printed pp. 415--431.
- Source: `References/1.9780898718027.ch22.pdf` (18 PDF pages), visually checked against rendered pages.
- Mode: core; Split 4.
- Planning correction: the PDF has 26 equation labels. The former extra plain `(22.6)` was a cross-reference duplicate of `(22.6a)--(22.6b)`.
- Status vocabulary: `PROVED`, `PASS (EXPLICIT-DOMAIN)`, `DEFER`, or `SKIP`.

## Body inventory in source order

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| 22.B1 | p. 416 | definition | Column-node Vandermonde matrix, primal system, and dual interpolation system | precise | general | not applicable | matrices, powers | REUSE_EXISTING | REUSE-MATHLIB | `higham22Vandermonde`; `higham22Vandermonde_apply` -- PROVED |
| 22.P1 | p. 416, after (22.1) | precise prose | `V` is nonsingular if and only if the nodes are distinct | precise | general | standard Vandermonde determinant fact | determinant, injective nodes | REUSE_EXISTING | REUSE-MATHLIB | `higham22_vandermonde_det_ne_zero_iff` -- PROVED |
| 22.1 | p. 416 | equation | Lagrange cardinal polynomial for row `i` of the inverse | precise | general | complete | finite products, distinct nodes | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | evaluation/cardinality and synthetic-quotient coefficient theorems -- PROVED |
| 22.2 | p. 416 | equation | Inverse entry from elementary symmetric functions | precise | general | follows from (22.1) | symmetric polynomials | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_2_inverse_entry` -- PROVED |
| Alg. 22.1 | p. 417 | algorithm | Master polynomial plus synthetic division computes `V⁻¹` | precise | general | derivation | polynomial coefficients, synthetic division | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham22Algorithm1MasterPolynomial`, `higham22Algorithm1SyntheticQuotient`, `higham22Algorithm1Printed`, cardinal/left-inverse/equality theorems -- PROVED |
| 22.3 | pp. 417--418 | equation | Two-sided infinity-norm bounds for `V_n⁻¹` | precise | general | citation-only | inverse-entry formula | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_3` with rowwise Mahler/Vieta bounds -- PROVED |
| Table 22.1 artifact | p. 418 | table layout | Visual presentation of condition estimates | editorial artifact | literature summary | citations | none | SKIP | SKIP-FIGURE-TABLE | table layout not encoded; mathematical rows split below |
| Table 22.1 (V1) | p. 418 | inequality | Harmonic nodes have `kappa_infty(V_n) > n^(n+1)` | precise | symbolic family | citation-only | inverse norm | FORMALIZE_CORE | CORE-PRECISE-PROSE | positive-gap domain, producer, and `higham22_table22_1_V1_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V2) | p. 418 | inequality | Arbitrary real nodes have stated exponential `kappa_2` lower bound | precise | general | citation-only | spectral norm | FORMALIZE_CORE | CORE-PRECISE-PROSE | nonnegative-gap domain and `higham22_table22_1_V2_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V3) | p. 418 | inequality | Nonnegative nodes have stated sharper `kappa_2` lower bound | precise | general | citation-only | spectral norm | FORMALIZE_CORE | CORE-PRECISE-PROSE | nonnegative-gap domain and `higham22_table22_1_V3_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V4) | p. 418 | asymptotic relation | Equispaced `[0,1]` nodes have the displayed `kappa_infty` asymptotic | precise asymptotic | symbolic family | citation-only | asymptotics | FORMALIZE_CORE | CORE-PRECISE-PROSE | relative-error domain, exact-model producer, and ratio limit theorem -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V5) | p. 418 | asymptotic relation | Equispaced `[-1,1]` nodes have the displayed exponential asymptotic | precise asymptotic | symbolic family | citation-only | asymptotics | FORMALIZE_CORE | CORE-PRECISE-PROSE | relative-error domain, exact-model producer, and ratio limit theorem -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V6) | p. 418 | asymptotic relation | Chebyshev nodes have the displayed `kappa_infty` asymptotic | precise asymptotic | symbolic family | citation-only | Chebyshev polynomials, asymptotics | FORMALIZE_CORE | CORE-PRECISE-PROSE | relative-error domain, exact-model producer, and ratio limit theorem -- PASS (EXPLICIT-DOMAIN) |
| Table 22.1 (V7) | p. 418 | equality | Roots-of-unity Vandermonde has `kappa_2=1` | precise | symbolic family | standard | Fourier/Vandermonde unitarity | REUSE_EXISTING | REUSE-REPOSITORY | `higham22_table22_1_V7_kappa2` plus explicit inverse/left-inverse theorem -- PROVED |
| 22.4 | p. 418 | equation/example | Symbolic confluent Vandermonde matrix exposing derivative columns | precise | symbolic family | not applicable | derivatives | FORMALIZE_CORE | CORE-SYMBOLIC-EXAMPLE | `higham22ConfluentExample`; determinant and transpose nonsingularity iff `alpha₀ ≠ alpha₁` -- PROVED |
| 22.B1a | p. 418 | precise prose | The transpose of a confluent Vandermonde matrix is nonsingular when the nonconfluent nodes are distinct | precise | general | stated | Hermite interpolation/confluent determinant | FORMALIZE_CORE | CORE-PRECISE-PROSE | `higham22_confluent_polynomial_unique`, general matrix/action/injectivity/determinant theorems -- PROVED |
| 22.5 | p. 419 | equation | Equal nodes are contiguous | precise | general | assumption | ordering | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `Higham22ContiguousNodes`, `higham22_eq22_5` -- SOURCE ASSUMPTION ENCODED |
| 22.6a | p. 419 | equation | Three-term polynomial recurrence | precise | general | assumption | polynomials | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `Higham22ThreeTermRecurrence` -- PROVED as exact contract |
| 22.6b | p. 419 | equation | Initial polynomials for recurrence | precise | general | assumption | polynomials | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | included in `Higham22ThreeTermRecurrence` -- PROVED |
| 22.7 | p. 419 | equation | Basis representation `psi = sum a_i p_i` | precise | general | definition | polynomial finite sums | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22Psi`; `higham22_eq22_7_eval` -- PROVED |
| 22.8 | p. 419 | equation | Confluent Newton divided-difference form | precise | general | complete | divided differences | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22NewtonPolynomial`, `higham22_eq22_8` -- PROVED |
| 22.9 | p. 420 | equation | Ordinary/confluent divided-difference recurrence | precise | general | complete | derivatives, factorial | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22DividedDifferenceStep`; distinct/confluent branch theorems -- PROVED |
| 22.10 | p. 420 | equation | Terminal nested polynomial `q_n = c_n` | precise | general | complete | nested multiplication | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_10_polynomial` -- PROVED |
| 22.11 | p. 420 | equation | Backward nested recurrence `q_k=(x-alpha_k)q_{k+1}+c_k` | precise | general | complete | nested multiplication | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_11_step` -- PROVED algebraically |
| 22.12 | p. 420 | equation | Expansion of `q_k` in the polynomial basis | precise | general | complete | (22.6) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22BasisExpansion`, `higham22_eq22_12_eval` -- PROVED |
| 22.13 | pp. 420--421 | equation | Coefficient recurrence for general `k` | precise | general | complete | (22.6), (22.11), (22.12) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22StageIICoefficientStep`, sparse row/synthesis correctness -- PROVED |
| 22.14 | p. 421 | equation | Final coefficient-recurrence base case | precise | general | complete | (22.6), (22.12) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | included in the common sparse coefficient update and Stage-II invariant -- PROVED |
| Alg. 22.2 | pp. 421--422 | algorithm | Dual confluent Vandermonde-like solver | precise | general | derivation | (22.9), (22.13), (22.14) | FORMALIZE_CORE | CORE-NAMED-RESULT | literal stages and Newton invariant PROVED; `higham22_algorithm22_2_solves_explicitDomain` plus factor producer/witness -- PASS (EXPLICIT-DOMAIN) |
| Table 22.2 artifact | p. 422 | table layout | Presentation of recurrence parameters | editorial artifact | not applicable | not applicable | none | SKIP | SKIP-FIGURE-TABLE | layout not encoded; mathematical rows split below |
| Table 22.2 parameters | p. 422 | exact formulas | `theta_j,beta_j,gamma_j` for monomial, Chebyshev, Legendre, Hermite, and Laguerre bases | precise | five symbolic families | stated | polynomial identities | FORMALIZE_DEPENDENCY | DEP-REQUIRED | `higham22PolynomialSequence`; five row recurrence theorems; `higham22_table22_2_theta_ne_zero`; Legendre `p_j(1)=1` -- PROVED |
| 22.15 | p. 422 | equation | Stage-I triangular factor steps | precise | general | derivation | Algorithm 22.2 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | actual state recurrence PROVED; `Higham22TriangularFactorDomain` finite lower-factor surface -- PASS (EXPLICIT-DOMAIN) |
| 22.16 | p. 422 | equation | Stage-II triangular factor steps | precise | general | derivation | Algorithm 22.2 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | actual printed state recurrence PROVED; finite upper-factor surface -- PASS (EXPLICIT-DOMAIN) |
| 22.17 | p. 422 | equation | Product factorization equals `P⁻ᵀ` | precise | general | complete | (22.15), (22.16) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | transpose adapter plus `higham22_eq22_17_factor_explicitDomain`; identity witness -- PASS (EXPLICIT-DOMAIN) |
| Alg. 22.3 | pp. 422--423 | algorithm | Primal confluent Vandermonde-like solver from transposed factors | precise | general | derivation | (22.17) | FORMALIZE_CORE | CORE-NAMED-RESULT | literal two-stage path PROVED; `higham22_algorithm22_3_solves_explicitDomain` plus factor witness -- PASS (EXPLICIT-DOMAIN) |
| Emp. 22.E1 | p. 423 | empirical output | Björck--Pereyra `n=9` machine result | underspecified | empirical run | none | historical machine | SKIP | SKIP-EMPIRICAL | not encoded |
| Thm. 22.4 | p. 424 | theorem | Exact componentwise forward bound for computed Algorithm 22.2 | precise | general | complete | FP model, Algorithms 22.2, Lemma 3.8 | FORMALIZE_CORE | CORE-NAMED-RESULT | local vector expansion, producer/witness, and `higham22_theorem22_4_forward_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| 22.18 | p. 424 | equation | Forward-error conclusion of Theorem 22.4 | precise | general | complete | theorem path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | named Theorem 22.4 explicit-domain bound -- PASS (EXPLICIT-DOMAIN) |
| 22.19 | p. 424 | equation | Stage-I factor perturbation bound | precise | general | complete | divided-difference analysis | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_19_explicitDomain` and zero-perturbation producer -- PASS (EXPLICIT-DOMAIN) |
| 22.20 | p. 424 | equation | Stage-II factor perturbation bound | precise | general | complete | three-term inner products | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `higham22_eq22_20_explicitDomain` and producer -- PASS (EXPLICIT-DOMAIN) |
| 22.21 | p. 424 | equation | Product of perturbed factors for computed solution | precise | general | complete | (22.19), (22.20) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | executable ordered factor product and `higham22_eq22_21_explicitDomain` -- PASS (EXPLICIT-DOMAIN) |
| 22.22 | pp. 424--425 | equation/example | Explicit `n=3` factor product used for sign analysis | precise | fixed symbolic instance | complete | factors | FORMALIZE_DEPENDENCY | DEP-REQUIRED | no-cancellation term domain, inequality, and nonzero witness -- PASS (EXPLICIT-DOMAIN) |
| Cor. 22.5 | p. 425 | corollary | Cancellation-free forward bound for increasing nonnegative nodes and named bases | precise | general | complete | Thm. 22.4, sign pattern | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham22_corollary22_5_explicitDomain` plus no-cancellation domain -- PASS (EXPLICIT-DOMAIN) |
| 22.23 | p. 425 | equation | Inverse-factor expression used for residual analysis | precise | general | complete | (22.21) | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | ordered inverse-factor apply and `higham22_eq22_23_explicitDomain` -- PROVED definition |
| 22.24 | p. 425 | model assumption | Simplifying inverse-perturbation bound for `U_k` | precise | general | explicitly assumed | inverse perturbations | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | explicit `Higham22InversePerturbationDomain`, local inverse identities, bound, and producer -- SOURCE ASSUMPTION ENCODED |
| Thm. 22.6 | p. 426 | theorem | Residual bound conditional on (22.24) | precise | general | complete | (22.24), Lemma 3.8 | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham22_theorem22_6_residual_explicitDomain`, retaining (22.24) -- PASS (EXPLICIT-DOMAIN) |
| 22.25 | p. 426 | equation | Residual bound of Theorem 22.6 | precise | general | complete | theorem path | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | named conditional residual domain theorem -- PASS (EXPLICIT-DOMAIN) |
| Cor. 22.7 | p. 426 | corollary | Monomial residual bound for increasing nonnegative nodes | precise first-order asymptotic (`u -> 0`, fixed `n`) | general | complete plus Problem 22.8 | inverse bidiagonal bound, asymptotics | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham22_corollary22_7_monomial_explicitDomain`, explicit quadratic term -- PASS (EXPLICIT-DOMAIN) |
| Table 22.3 | p. 427 | empirical output | Chebyshev--Vandermonde errors/residuals | underspecified | empirical run | none | machine/runtime details | SKIP | SKIP-EMPIRICAL | not encoded |
| Alg. 22.8 | p. 427 | algorithm | Extended Clenshaw recurrence computes derivatives of `psi` | precise | general | citation/Problem 22.10 | polynomial recurrence, derivatives | FORMALIZE_CORE | CORE-NAMED-RESULT | `higham22Algorithm22_8`, Taylor/Clenshaw loop invariants, `higham22_algorithm22_8_correct` -- PROVED |
| 22.B2 | p. 428 | precise prose consequence | Standard Vandermonde refinement obtains asymptotic componentwise stability via Theorem 12.3 | precise asymptotic | general | cross-reference to earlier theorem | Chapter 12, Horner residual bounds | FORMALIZE_CORE | REUSE-REPOSITORY | contraction recurrence, exact closed form, and `higham22_refinement_converges` -- PROVED explicit consequence |
| 22.B3 | p. 428 | qualitative heuristics | Two large-solution heuristics and method advice | underspecified | editorial | none | experiments | SKIP | SKIP-QUALITATIVE | not encoded |
| 22.N | pp. 428--430 | notes/references | History and literature survey | editorial | editorial | not applicable | external literature | SKIP | SKIP-LITERATURE-REVIEW | inventoried; not encoded |

## Problems and owned Appendix A solutions

Problems are optional in core mode. All are accounted for; only reusable exact results would be promoted in a later pass.

| Source | Summary | Appendix A | Decision | Reason/status |
|---|---|---|---|---|
| 22.1 | modified inverse scaling and flop count | solution: same flop count | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED |
| 22.2 | generalize Algorithm 22.1 | none | BENCHMARK_CANDIDATE | broader algorithm-design exercise |
| 22.3 | empirical/research stability study | none | SKIP | SKIP-EMPIRICAL |
| 22.4 | row-sum identity and inverse sign consequence | solution present | BENCHMARK_CANDIDATE | reusable exact identity, optional |
| 22.5 | Chebyshev--Vandermonde inverse norm comparison | solution present | BENCHMARK_CANDIDATE | needs Chebyshev basis infrastructure |
| 22.6 | determinant of a Vandermonde-like matrix | none | BENCHMARK_CANDIDATE | exact optional theorem |
| 22.7 | two Chebyshev condition-number results | solution present | BENCHMARK_CANDIDATE | discrete orthogonality dependency |
| 22.8 | upper-bidiagonal inverse perturbation and (22.24) specialization | solution present | FORMALIZE_DEPENDENCY | printed coefficient, explicit inverse-perturbation domain, named theorem and valid-range producer -- PASS (EXPLICIT-DOMAIN) |
| 22.9 | point reordering matching GEPP | Appendix only answers increasing-order question | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED |
| 22.10 | derive extended Clenshaw recurrences | none | FORMALIZE_DEPENDENCY | derivative recurrence discharged by `higham22_taylor_linear_mul_coeff` and the jet invariant -- PROVED |
| 22.11 | structured primal/dual condition numbers | solution gives dual formula and cites proof | BENCHMARK_CANDIDATE | citation-only optional theorem |

## Gate summary

The source inventory is exhaustive and the selected-scope gate is **PASS**. Exact algebra and actual executable loops close the unconditional algorithmic rows. Citation-only Table 22.1 rows and the long rounded factor/solve claims are terminal **PASS (EXPLICIT-DOMAIN)** results over positive-gap, relative-error, factor-product, inverse-perturbation, or first-order expansion domains. Each such domain has a constructive producer and concrete nonempty witness; none stores the final solve or error inequality as a field. The source assumption (22.24) remains explicitly labeled as an assumption. Quadratic remainder terms are exposed directly, and the refinement consequence has an actual geometric convergence proof.
