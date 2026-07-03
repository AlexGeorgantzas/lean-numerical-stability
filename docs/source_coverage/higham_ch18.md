# Higham Chapter 18 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 18, "Matrix Powers" (book pp. 339–352).
- Source file: `References/1.9780898718027.ch18.pdf` (14 PDF pages).
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 18 rows of `chapter_splitting/chapter_index.md`.
- Main Lean files: `LeanFpAnalysis/FP/Algorithms/MatrixPowers.lean` (§18.2 finite-precision engine), `LeanFpAnalysis/FP/Algorithms/MatrixPowersJordan.lean` (real-Jordan δ-scaling construction).
- Selected-scope gate: BLOCKED. Every selected row that is provable with the
  repository's ℝ matrix layer and Mathlib v4.29 is source-closed end-to-end
  (see the inventory below); the remaining open rows are each blocked on a
  named foundation verified absent from Mathlib v4.29 (classical Jordan
  Normal Form over ℂ, Schur triangulation, pseudospectra, field of values,
  Perron–Frobenius) and/or on the repository having no complex matrix layer.
  Resolving them is a multi-session foundational route choice recorded in the
  not-proved ledger.

## Numbering History

`MatrixPowers.lean` predates the four-way split and carried stale first-edition-style "Chapter 17" labels (§17.2, Theorem 17.1, eqs (17.10)–(17.15), pp. 354–355). All labels were renumbered to the 2nd-edition Chapter 18 rows (§18.2, Theorem 18.1, eqs (18.10)–(18.15), pp. 346–348) and `higham_knight_17_1` was renamed `higham_knight_18_1`. Rendered-page extraction confirmed the mapping is exact.

## Hidden-Hypothesis Record

`JordanFormSpec.similarity_absorbs` is an ASSUMED structure field packaging the
entire non-trivial content of Theorem 18.1's proof (the `S = X·P(ε)`
Jordan-block δ-scaling construction of pp. 347–348). It was confirmed as a
target-equivalent hypothesis by a two-lens adversarial audit. Consequences:

- `higham_knight_18_1` (and its `_fl_tendsto` / `18_2_diagonalizable` forms)
  are **conditional reductions**, not closures of Theorems 18.1/18.2.
- The field is explicitly flagged in-code as an axiom/open obligation.
- The construction is **discharged** (proved, no assumption) for real-spectrum
  data: `JordanFormSpec.ofRealDiagonal` (diagonal `J`, `t = 1`) and the
  real-Jordan bidiagonal case in `MatrixPowersJordan.lean` (`t ≥ 2`).
- The complex-spectrum/defective general case is blocked: Mathlib provides no
  classical Jordan Normal Form over ℂ (only Jordan–Chevalley), and the
  repository has no complex matrix-algebra layer (`matMul`/`infNorm` are ℝ-only).

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch18 | core | 100 | 92 | 92 | 80 | 98 | 84 | 6 | All remaining open selected rows are blocked on foundations verified ABSENT from Mathlib v4.29 (classical JNF over ℂ, Schur triangulation, pseudospectra, field of values, Perron–Frobenius) plus the repo's ℝ-only matrix layer; every locally-provable rendering is closed end-to-end (Theorem 18.1 full real-spectrum Jordan class incl. the concrete fl iteration; Theorem 18.2 t = 1 algebraic reduction; (18.4) both directions; (18.5) alternative form; (18.10)/(18.11) concrete; (18.12) certificate form) | medium-high |

## Index- and Extracted-Text Source Inventory

Rendered-page extraction (poppler/pdfjs) was used for all of pp. 339–352;
Greek-letter reconstruction in the text layer was cross-checked against
rendered page images. Sections: 18.1 Matrix Powers in Exact Arithmetic,
18.2 Bounds for Finite Precision Arithmetic, 18.3 Application to Stationary
Iteration, 18.4 Notes and References, Problems.

### Primary Labels

| Source item | Indexed section | Current Lean mapping | Disposition |
|---|---|---|---|
| Theorem 18.1 (Higham–Knight) | 18.2 Bounds for Finite Precision Arithmetic (p. 9; book pp. 347–348) | Conditional reduction `higham_knight_18_1` (+ `higham_knight_18_1_fl_tendsto` end-to-end limit form); crux `similarity_absorbs` PROVED for all real-spectrum Jordan data: t = 1 via `JordanFormSpec.ofRealDiagonal` (`higham_18_1_real_diagonalizable_tendsto`, `..._fl_tendsto`) and any t ≥ 1 with block-size bound via `JordanFormSpec.ofRealJordan` + `exists_jordan_scaling_vector` (`higham_18_1_real_jordan_tendsto`, `..._fl_tendsto` in `MatrixPowersJordan.lean`) — printed condition (18.13), printed limit conclusion, concrete `fl_matVec` iteration, standard axioms only. | real-spectrum case source-closed end-to-end; complex/defective-over-ℂ case OPEN, blocked on JNF over ℂ + complex matrix infrastructure |
| Theorem 18.2 (Higham–Knight) | 18.2 Bounds for Finite Precision Arithmetic (p. 11; book pp. 349–350) | Algebraic t = 1 reduction target `higham_knight_18_2_diagonalizable` (limit conclusion). Pseudospectral packaging (ρ_ε(A) < 1 at ε = cₙu‖A‖₂, unique dominant eigenvalue, norm normalizations, O(ε²) proviso) NOT formalized. | reduction target closed (conditional); printed pseudospectral statement OPEN, deferred on pseudospectra (absent from Mathlib/repo) |

### Numbered Equations

| Equation row | Current accounting | Disposition |
|---|---|---|
| (18.1a) | Jordan form A = XJX⁻¹ as similarity DATA: `JordanFormSpec` (X, X_inv, ρ, t fields) plus explicit conjugation hypotheses `matMul n X_inv (matMul n A X) = J` in the discharged constructors. Existence of the Jordan form for arbitrary A is NOT formalized (Mathlib lacks JNF). | data-level accounted; existence deferred (Mathlib gap) |
| (18.1b) | Block-bidiagonal structure of J encoded hypothesis-level (diagonal/superdiagonal shape + run-length ≤ t−1) in `MatrixPowersJordan.lean`. | data-level accounted |
| (18.2) | Scaled 2×2 Jordan block example (hump illustration). Precise symbolic example; not required by any selected proof. | DEFER (EXAMPLE-LOCAL; reusable phenomenon already captured by the general bounds) |
| (18.3) | Norm-ratio identity for powers of (18.2) with large-k asymptotic. | DEFER (EXAMPLE-LOCAL) |
| (18.4) | Diagonalizable exact-arithmetic bound ‖Aᵏ‖_p ≤ κ_p(X)ρ(A)ᵏ with lower bound ρ(A)ᵏ ≤ ‖Aᵏ‖_p: `higham_eq_18_4_upper_real_diagonalizable` and `higham_eq_18_4_lower_real_diagonalizable` (via `matPow_diagonal`, `matPow_similarity`) close the p = ∞, real-spectrum subcase both directions. | real-∞ subcase source-closed; general p / complex case OPEN (needs complex layer) |
| (18.5) | Ostrowski defective bound ‖Aᵏ‖_p ≤ κ_p(X)(ρ(A)+δ)ᵏ and its alternative form κ_p(X)κ_p(D)(ρ+δ)ᵏ (p. 344): `higham_eq_18_5_alt_real_jordan` closes the alternative form at p = ∞ for real bidiagonal Jordan data (`‖Aᵏ‖∞ ≤ κ∞(X)·(βˢ)⁻¹·(ρ+β)ᵏ`). The primary form's κ_p(X) refers to the Jordan transform of δ⁻¹A (different X); accounted, not separately formalized. | alternative form real-∞ subcase source-closed; primary form + complex/all-p OPEN |
| (18.6) | Gautschi bound ‖Aᵏ‖_F ≤ c·k^{p−1}ρ(A)ᵏ; the constant c is not specified in the source. | SKIP (UNDERSPECIFIED-CONSTANT; inventory-accounted) |
| (18.7) | Henrici departure-from-normality bounds. Requires Schur triangularization, absent from Mathlib v4.29.0 (verified: no `schurTriangulation` in the pinned package). | DEFER (MISSING-FOUNDATION: Schur decomposition) |
| (18.8) | Trefethen pseudospectral bound ‖Aᵏ‖₂ ≤ ε⁻¹ρ_ε(A)^{k+1}. | DEFER (MISSING-FOUNDATION: pseudospectra absent from Mathlib/repo) |
| (18.9) | Definition of the ε-pseudospectral radius ρ_ε(A). | DEFER (MISSING-FOUNDATION: pseudospectra) |
| (18.10) | Error recurrence fl(Aᵐeⱼ) = ∏(A+ΔAᵢ)eⱼ: abstract model `ComputedMatPowVec`; CONCRETE realization `fl_matPowVecSeq` + `computedMatPowVec_fl_matVec` (constant γ_n via `matVec_backward_error`). | source-closed (column/matVec form) |
| (18.11) | Perturbation bound |ΔAᵢ| ≤ γ_{n+2}|A|: `computedMatPowVec_fl_matVec_gamma_add_two` (γ_n ≤ γ_{n+2} monotonicity; the printed constant is stated verbatim). | source-closed |
| unnumbered (p. 8) | Componentwise chain |fl(Aᵐeⱼ)| ≤ (1+γ_{n+2})ᵐ(|A|ᵐeⱼ): `matPow_componentwise_bound` (+ matrix form `matPow_matrix_bound`). | source-closed |
| (18.12) | Sufficient condition ρ(|A|) < 1/(1+γ_{n+2}). Three renderings: (a) `matPow_convergence_bound` — ‖A‖∞ surrogate (weakest); (b) `matPow_abs_weighted_bound` / `matPow_convergence_weighted` / `matPow_convergence_weighted_fl` — Collatz–Wielandt certificate form: a weight `w` with |A|·w ≤ θ·w and (1+γ_{n+2})θ < 1 gives ‖fl(Aᵐv₀)‖∞ → 0; such certificates exist for every θ > ρ(|A|), so this renders the printed row up to the certificate/spectral-radius equivalence; (c) the literal ρ(|A|) statement needs Perron–Frobenius / nonneg-matrix spectral-radius theory — verified ABSENT from Mathlib v4.29. | certificate form source-closed; literal ρ(|A|) form OPEN (Mathlib gap) |
| (18.13) | Theorem 18.1's sufficient condition 4tγ_{n+2}κ(X)‖A‖ < (1−ρ)ᵗ: stated verbatim in `higham_knight_18_1` (conditional) and proved end-to-end in the real-spectrum constructors. | see Theorem 18.1 row |
| (18.14) | Proof-internal telescoping inequality: `similarity_product_bound` / `similarity_normwise_bound` (genuinely proved engine). | source-closed (as dependency) |
| (18.15) | Proof-internal scaling bound ‖S⁻¹AS‖ ≤ 1−ε, κ(S) ≤ (1−ρ−ε)^{1−t}κ(X): proved for real Jordan data in `MatrixPowersJordan.lean` (`infNorm_jordan_conj_le` gives ‖D⁻¹JD‖∞ ≤ ρ+β = 1−ε; `infNorm_diagMatrix_le` + `exists_jordan_scaling_vector` give κ∞(D) ≤ β^{1−t}; `higham_scaling_margin` + `pow_self_le_four_mul` give the (1+1/m)^m < e < 4 optimisation behind the 4t factor); assumed (flagged) only in the general complex-case `similarity_absorbs` field. | real case source-closed; complex case OPEN (JNF over ℂ) |

### Section 18.3 (Application to Stationary Iteration)

Prose + SOR numerical example connecting fl((M⁻¹N)ᵏ) to stationary-iteration
behaviour; the error recurrence e_k = (M⁻¹N)ᵏe₀ is Chapter 17 material
(`StationaryIteration.lean` owns the splitting/iteration-matrix objects).
No numbered theorem or equation rows are introduced in 18.3 beyond citations
of (18.12); the MATLAB experiments and pseudospectrum figures are empirical.
Disposition: SKIP (EMPIRICAL/QUALITATIVE) with the (18.12) citation covered
by the (18.12) row above.

### Section 18.4 (Notes and References) and unnumbered §18.1 items

Historical notes, attributions (Higham & Knight, Stewart, Friedland &
Schneider, Moler & Van Loan), the numerical radius r(A) remarks, Gelfand
limit ρ(A) = lim‖Aᵏ‖^{1/k}, normal-matrix identity ‖Aᵏ‖₂ = ρ(A)ᵏ, and
departure-from-normality definitions. Disposition: SKIP (EDITORIAL /
qualitative) except: Gelfand limit — REUSE_EXISTING candidate (Mathlib
`pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`) if the (18.12) full
closure is attempted; numerical radius — DEFER (MISSING-FOUNDATION, no field
of values in Mathlib/repo).

### Problems (benchmark-reserved)

| Row | Location | Status |
|---|---|---|
| Problem 18.1 | book p. 352 | benchmark-reserved; identifier/location only |
| Problem 18.2 | book p. 352 | benchmark-reserved; identifier/location only |
| Problem 18.3 | book p. 352 (research problem) | benchmark-reserved; identifier/location only |
| Problem 18.4 | book p. 352 (research problem) | benchmark-reserved; identifier/location only |
| Appendix A solution 18.1 | `References/1.9780898718027.appa.pdf` | benchmark-reserved; identifier/location only |
| Appendix A solution 18.2 | `References/1.9780898718027.appa.pdf` | benchmark-reserved; identifier/location only |

## Main Lean Declarations (source-facing)

- `ComputedMatPowVec`, `ComputedMatPowVec.mono` — (18.10) model + budget weakening.
- `fl_matPowVecSeq`, `computedMatPowVec_fl_matVec`, `computedMatPowVec_fl_matVec_gamma_add_two` — concrete (18.10)/(18.11) realization.
- `one_step_matpow_bound`, `matPow_componentwise_bound`, `matPow_matrix_bound`, `matPow_nonneg_componentwise_bound` — componentwise chain (p. 8).
- `matPow_normwise_bound`, `matPow_convergence_bound` — normwise chain / (18.12) surrogate.
- `similarity_product_bound`, `similarity_normwise_bound` — (18.14) telescoping engine.
- `JordanFormSpec` (crux field flagged), `higham_knight_18_1`, `higham_knight_18_1_fl_tendsto`, `higham_knight_18_2_diagonalizable` — conditional reductions of Theorems 18.1/18.2.
- `computedMatPow_tendsto_zero_of_geometric` — geometric bound ⇒ limit fl(Aᵐ) → 0.
- `infNorm_add_le`, `infNorm_le_mul_of_abs_le_mul_abs`, `infNorm_diagonal_le` — norm helpers.
- `JordanFormSpec.ofRealDiagonal`, `higham_18_1_real_diagonalizable_tendsto`, `higham_18_1_real_diagonalizable_fl_tendsto` — axiom-free t = 1 real case.
- `MatrixPowersJordan.lean` — axiom-free real-Jordan case, any t ≥ 1: `jordanBeta`, `one_add_one_div_pow_lt_four`, `pow_self_le_four_mul`, `higham_scaling_margin` (scalar 4t-factor core), `diagMatrix_isRightInverse`/`diagMatrix_conj_entry`/`infNorm_diagMatrix_le`, `jordan_conj_row_sum_le`/`infNorm_jordan_conj_le`, `jordanRunLength`, `exists_jordan_scaling_vector`, `JordanFormSpec.ofRealJordan`, `higham_18_1_real_jordan_tendsto`, `higham_18_1_real_jordan_fl_tendsto`.
- `matPow_diagonal`, `matPow_similarity`, `higham_eq_18_4_upper_real_diagonalizable`, `higham_eq_18_4_lower_real_diagonalizable` — eq (18.4) real-∞ case, both directions.

## Open Selected Rows (not-proved ledger)

| Selected row | Missing foundation | Smallest next Lean theorem | Current blocker | Status |
|---|---|---|---|---|
| Theorem 18.1, complex-spectrum/defective-over-ℂ case | complex matrix algebra layer (ℂ `matMul`/`infNorm`) + classical JNF over ℂ | complex analogue of `infNorm`/`matMul`, then transport `ofRealJordan`'s construction (the scalar core `higham_scaling_margin` and run-length scaling are field-agnostic) | Mathlib has no classical Jordan Normal Form (only Jordan–Chevalley); repo matrix layer is ℝ-only | BLOCKED (route choice: build complex layer — multi-session foundation — or accept the real-spectrum end-to-end closure + flagged conditional for ℂ) |
| Theorem 18.2, printed pseudospectral form | pseudospectra Λ_ε, ρ_ε; eigenvalue perturbation input from [620, 1995] | definition of Λ_ε(A)/ρ_ε(A) over the repo matrix layer | pseudospectra absent from Mathlib and repo | DEFERRED |
| (18.5) primary printed form (κ of the δ⁻¹A Jordan transform) and all-p/complex forms | complex layer for the general case; the primary form needs the δ⁻¹A Jordan-transform bookkeeping | restatement of `higham_eq_18_5_alt_real_jordan` with the rescaled transform | low value beyond the closed alternative form | OPEN (low priority) |
| (18.7) | Schur triangularization | — | absent from Mathlib v4.29.0 | DEFERRED |
| (18.8)/(18.9) | pseudospectra | — | absent from Mathlib/repo | DEFERRED |
| (18.12) literal ρ(|A|) form | Perron–Frobenius / nonneg-matrix spectral radius (verified absent from Mathlib v4.29; "perron" hits are box-integral false positives) | derive the Collatz–Wielandt certificate from ρ(|A|) < θ, feeding `matPow_convergence_weighted` | Mathlib gap; the certificate form is closed and is the standard equivalent | OPEN (Mathlib gap; certificate form closed) |
| numerical radius bound (p. 343, unnumbered) | field of values | — | absent from Mathlib/repo | DEFERRED |
| Gelfand limit citation (p. 342, unnumbered) | matPow ↔ Mathlib `Matrix ^` bridge | `matPow n A k = (Matrix.of A ^ k)` transport | small; only needed by the (18.12) closure | OPEN (dependency) |

## Verification Log

| Command | Result | Notes |
|---|---|---|
| `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixPowers.lean` | PASS | after each increment |
| `#print axioms` on all new source-facing theorems | `[propext, Classical.choice, Quot.sound]` | no sorry/new axiom |
| hygiene scan (`sorry\|admit\|axiom\|unsafe\|opaque`) | clean | comment mentions of "axiom" are prose flags on `similarity_absorbs` |
