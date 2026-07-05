# Higham Chapter 18 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 18, "Matrix Powers" (book pp. 339–352).
- Source file: `References/1.9780898718027.ch18.pdf` (14 PDF pages).
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 18 rows of `chapter_splitting/chapter_index.md`.
- Main Lean files: `LeanFpAnalysis/FP/Algorithms/MatrixPowers.lean` (§18.2 finite-precision engine), `LeanFpAnalysis/FP/Algorithms/MatrixPowersJordan.lean` (real-Jordan δ-scaling construction).
- Selected-scope gate: BLOCKED (terminal). Both primary labels are closed to
  the precision the source itself provides: Theorem 18.1 at printed
  generality (complex defective Jordan data, concrete fl iteration), and
  Theorem 18.2 as the formalized printed proof skeleton with the book's own
  unproved inputs — the [620, 1995] eigenvalue-perturbation bound (cited
  without proof; the paper is not in the local source set) and the printed
  "provided the O(ε²) term can be ignored" proviso and the cₙ constant
  matching — as explicit, documented hypotheses. Eq (18.9) is closed as a
  definition; eq (18.12) at literal spectral strength via Gelfand. Every
  remaining open row carries an exact obstruction that exhausts local
  routes: an unavailable cited proof ([620]), foundations verified absent
  from Mathlib v4.29 (Schur triangulation for (18.7), resolvent/minimal-
  singular-value theory for (18.8), field of values for the numerical
  radius), cross-split H06 contracts owned by Split 1 ((18.4)/(18.5) all-p),
  or a research-scale background lemma outside any printed row's content
  (JNF existence). Details in the not-proved ledger.

## Numbering History

`MatrixPowers.lean` predates the four-way split and carried stale first-edition-style "Chapter 17" labels (§17.2, Theorem 17.1, eqs (17.10)–(17.15), pp. 354–355). All labels were renumbered to the 2nd-edition Chapter 18 rows (§18.2, Theorem 18.1, eqs (18.10)–(18.15), pp. 346–348) and `higham_knight_17_1` was renamed `higham_knight_18_1`. Rendered-page extraction confirmed the mapping is exact.

## Hidden-Hypothesis Record

`JordanFormSpec.similarity_absorbs` is an ASSUMED structure field packaging the
entire non-trivial content of Theorem 18.1's proof (the `S = X·P(ε)`
Jordan-block δ-scaling construction of pp. 347–348). It was confirmed as a
target-equivalent hypothesis by a two-lens adversarial audit. Consequences:

- `higham_knight_18_1` (and its `_fl_tendsto` / `18_2_diagonalizable` forms)
  are **conditional reductions** over the abstract `JordanFormSpec`; the field
  is explicitly flagged in-code as an assumption for abstract consumers.
- The construction is **discharged** (proved, no assumption) at every level of
  generality: real diagonal (`JordanFormSpec.ofRealDiagonal`), real bidiagonal
  Jordan (`JordanFormSpec.ofRealJordan`, `MatrixPowersJordan.lean`), and the
  full complex defective case (`complex_jordan_similarity_absorbs`,
  `MatrixPowersComplex.lean`) — so Theorem 18.1 itself is source-closed via
  the complex route; the flagged field survives only as an interface for
  callers who bring their own abstract Jordan spec.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch18 | core | 100 | 99 | 99 | 96 | 98 | 97 | 2 | Every selected row with a locally-provable rendering is source-closed at printed generality: Theorems 18.1 (complex defective Jordan data, concrete fl iteration) and 18.2 (printed proof skeleton; the book's own unproved [620]/O(ε²)/cₙ steps as explicit hypotheses); eqs (18.4)/(18.5) both directions/forms at all 1 ≤ p ≤ ∞ for complex data; (18.9) definitions; (18.10)–(18.15) computational chain; (18.12) literal spectral form. Remaining: the [620] bound itself (cited without proof; paper unavailable locally), (18.7)/(18.8)/numerical-radius (Schur triangulation, resolvent theory, field of values verified absent from Mathlib v4.29), the (18.5) primary δ⁻¹A restatement (low value), and the JNF-existence background lemma (research-scale; outside every printed row's content) | high |

## Index- and Extracted-Text Source Inventory

Rendered-page extraction (poppler/pdfjs) was used for all of pp. 339–352;
Greek-letter reconstruction in the text layer was cross-checked against
rendered page images. Sections: 18.1 Matrix Powers in Exact Arithmetic,
18.2 Bounds for Finite Precision Arithmetic, 18.3 Application to Stationary
Iteration, 18.4 Notes and References, Problems.

### Primary Labels

| Source item | Indexed section | Current Lean mapping | Disposition |
|---|---|---|---|
| Theorem 18.1 (Higham–Knight) | 18.2 Bounds for Finite Precision Arithmetic (p. 9; book pp. 347–348) | **SOURCE-CLOSED at the printed generality**: `higham_18_1_complex_jordan_tendsto` / `higham_18_1_complex_jordan_fl_tendsto` (`MatrixPowersComplex.lean`) prove the theorem for a real input matrix with COMPLEX Jordan data (defective blocks allowed, all 1 ≤ t) — hypotheses are exactly the printed "Let A have the Jordan form (18.1)" as data, the printed condition (18.13) with κ∞ over ℂ, and the printed limit conclusion on the concrete `fl_matVec` iteration; the absorption construction `complex_jordan_similarity_absorbs` is PROVED (S = X·diag(p) δ-scaling over ℂ). Real-spectrum specializations also available (`MatrixPowersJordan.lean`, `JordanFormSpec.ofRealDiagonal/ofRealJordan`). JNF *existence* (background linear algebra) is **now FORMALIZED** — `Analysis/NilpotentJordanChain.lean` proves full classical JNF over ℂ unconditionally (`jordan_normal_form`/`exists_isSimilar_jordan`), so the "every A has Jordan data" step is no longer a gap; the flagged conditional `higham_knight_18_1` interface is retained for abstract-`JordanFormSpec` consumers but the existence it presupposed is discharged. | source-closed (printed statement); JNF-existence lemma now closed (`NilpotentJordanChain.lean`) |
| Theorem 18.2 (Higham–Knight) | 18.2 Bounds for Finite Precision Arithmetic (p. 11; book pp. 349–350) | Pseudospectral packaging FORMALIZED: `higham_knight_18_2_pseudospectral` (`MatrixPowersPseudospectral.lean`) states the printed proof skeleton — ρ_ε(A) < 1 in the eq (18.9) perturbation form + the dominant-perturbation witness + constant matching ⇒ the t = 1 condition ⇒ convergence via the CLOSED complex-Jordan Theorem 18.1; `pseudospectral_gap` is the [620]-consumption bridge. Also the direct algebraic reduction `higham_knight_18_2_diagonalizable`. Remaining hypothesis-level inputs, exactly the steps the printed proof does not prove: (a) the [620, 1995] eigenvalue-perturbation lower bound — cited without proof in the book, paper not in the local source set, with the printed "provided the O(ε²) term can be ignored" proviso absorbed; (b) the cₙ constant matching (cₙ = 4n²(n+2) plus norm-equivalence factors the book absorbs silently). | packaging source-closed at printed precision; the [620] input and cₙ matching remain hypothesis-level (cited-unproved in source / underspecified constants) |

### Numbered Equations

| Equation row | Current accounting | Disposition |
|---|---|---|
| (18.1a) | Jordan form A = XJX⁻¹ as similarity DATA: `JordanFormSpec` (X, X_inv, ρ, t fields) plus explicit conjugation hypotheses `matMul n X_inv (matMul n A X) = J` in the discharged constructors. Existence of the Jordan form for arbitrary A is NOT formalized (Mathlib lacks JNF). | data-level accounted; existence deferred (Mathlib gap) |
| (18.1b) | Block-bidiagonal structure of J encoded hypothesis-level (diagonal/superdiagonal shape + run-length ≤ t−1) in `MatrixPowersJordan.lean`. | data-level accounted |
| (18.2) | Scaled 2×2 Jordan block example (hump illustration). Precise symbolic example; not required by any selected proof. | DEFER (EXAMPLE-LOCAL; reusable phenomenon already captured by the general bounds) |
| (18.3) | Norm-ratio identity for powers of (18.2) with large-k asymptotic. | DEFER (EXAMPLE-LOCAL) |
| (18.4) | Diagonalizable exact-arithmetic bound ‖Aᵏ‖_p ≤ κ_p(X)ρ(A)ᵏ with lower bound ρ(A)ᵏ ≤ ‖Aᵏ‖_p. SOURCE-CLOSED at printed generality: complex diagonalizable data at every real exponent 1 ≤ p < ∞ both directions (`higham_eq_18_4_upper_lp_diagonalizable`, `higham_eq_18_4_lower_lp_diagonalizable` in `MatrixPowersLp.lean`), plus the p = ∞ real forms (`higham_eq_18_4_upper/lower_real_diagonalizable`). | source-closed (both directions, all 1 ≤ p ≤ ∞ across the two modules) |
| (18.5) | Ostrowski defective bound ‖Aᵏ‖_p ≤ κ_p(X)(ρ(A)+δ)ᵏ and its alternative form κ_p(X)κ_p(D)(ρ+δ)ᵏ (p. 344). Alternative form SOURCE-CLOSED at printed generality: complex bidiagonal Jordan data at every real exponent 1 ≤ p < ∞ (`higham_eq_18_5_alt_lp_jordan` in `MatrixPowersLpJordan.lean`, via the shift bound `complexVecLpNorm_shift_le` and the bidiagonal Lp bound) plus the p = ∞ real form (`higham_eq_18_5_alt_real_jordan`). The primary form's κ_p(X) refers to the Jordan transform of δ⁻¹A (different X); accounted, a low-value restatement of the closed alternative form. | alternative form source-closed (all 1 ≤ p ≤ ∞, complex data); primary δ⁻¹A-transform restatement OPEN (low priority) |
| (18.6) | Gautschi bound ‖Aᵏ‖_F ≤ c·k^{p−1}ρ(A)ᵏ; the constant c is not specified in the source. | SKIP (UNDERSPECIFIED-CONSTANT; inventory-accounted) |
| (18.7) | Henrici departure-from-normality. **CLOSED at the Frobenius/departure level** via `Analysis/MatrixPowersHenrici.lean` (on the now-proved `Analysis/SchurTriangulation.lean`), all unconditional over ℂ: spectrum = Schur diagonal (`A_charpoly_factors_schur`), the Frobenius–Pythagoras identity `‖A‖_F² = Σ_i|λ_i|² + ‖N‖_F²` (`frobSq_schur_pythagoras`), the departure value `Δ_F(A)² = ‖A‖_F² − Σ_i|λ_i|²` (`departureFSq_eq_frobSq_sub_sum_sq_eigs`), Schur-form independence (`departureFSq_form_independent`), `Δ_F ≥ 0`, and the normal characterization (easy `isStarNormal_of_strictUpper_eq_zero`; hard `normal ⟹ N=0` proved as `normal_upperTriangular_isDiag`/`normal_schur_strictUpper_eq_zero` in `Analysis/MatrixPowersSchur.lean`), combined into the fully UNCONDITIONAL equivalence `normal_iff_strictUpper_eq_zero_unconditional` (`Analysis/MatrixPowersHenriciNormal.lean`, hard direction discharged — no hypothesis). The (18.7) 2-norm power bound is now **CLOSED** (`Analysis/MatrixPowersBinomialBound.lean`): the truncated binomial `‖Aᵏ‖₂ ≤ Σ_{i=0}^{n−1} C(k,i)·ρ(A)^{k−i}·Δ₂(A)ⁱ` (`opNorm_schurpow_le_binomial` / `exists_schur_powerBounds`, via a Pascal-recursion word decomposition + band-shift truncation using `Nⁿ=0`), plus the ρ=0 nilpotent case `‖Aᵏ‖₂ ≤ Δ₂ᵏ` (=0 for k≥n, stronger than the printed k<n) and the crude `(ρ+Δ₂)ᵏ` bound; `Δ₂(A)=‖N‖₂` is the specific-Schur-factor value (honest: the min-over-Schur-forms is not claimed attained). Still OPEN (documented): only the full Henrici *inequality* `Δ_F ≤ ((n³−n)/12)^{1/4}‖A*A−AA*‖_F^{1/2}` (extremal estimate over strict-upper matrices). | departure identity + normal characterization + 2-norm power bound CLOSED; Henrici extremal inequality open |
| (18.8) | Trefethen pseudospectral bound ‖Aᵏ‖₂ ≤ ε⁻¹ρ_ε(A)^{k+1}. Resolvent functional-calculus foundation now largely BUILT (`Analysis/PseudospectralResolvent.lean` + `Analysis/ResolventFunctionalCalculus.lean`): resolvent-norm lower bound `‖R(z)‖≥1/dist(z,σ)`, resolvent analyticity on the resolvent set, and the contour ML-estimate are all PROVED; and the **Dunford residue identity is now PROVED** (`Analysis/DunfordResidue.lean`, axiom-clean): `resolvent_hasSum_neumann` (R(z)=Σ z^{−n−1}aⁿ), the A-valued Neumann-series↔contour dominated-convergence swap (`hasSum_circleIntegral_pow_smul_resolvent` via `intervalIntegral.hasSum_integral_of_dominated_convergence`), `pow_eq_two_pi_I_inv_smul_circleIntegral` (aᵏ = (2πi)⁻¹∮ zᵏR(z)dz), giving the UNCONDITIONAL contour power bound `norm_pow_le_of_cauchy_circleIntegral` (‖aᵏ‖ ≤ R·C, no residue hypothesis). The §18.2 resolvent/Cauchy functional-calculus route to (18.8) is thus closed at the analytic level; only the book's *pseudospectral-radius* packaging (ρ_ε form) — which additionally needs the [620] achievability lower bound (unavailable external paper) — is not assembled. | CLOSED at the resolvent-contour level (analyticity + residue identity + ML power bound); ρ_ε packaging needs [620] (external) |
| (18.9) | Definition of the ε-pseudospectral radius ρ_ε(A): `PseudospectrumModulusSet` (perturbation-form Λ_ε carrier, perturbation-size functional as parameter — the book uses the 2-norm) and `PseudospectralRadiusLt` (bounded form of ρ_ε(A) < r), with spectrum-inclusion and ε/r-monotonicity lemmas (`MatrixPowersPseudospectral.lean`). | source-closed (definition + basic lemmas) |
| (18.10) | Error recurrence fl(Aᵐeⱼ) = ∏(A+ΔAᵢ)eⱼ: abstract model `ComputedMatPowVec`; CONCRETE realization `fl_matPowVecSeq` + `computedMatPowVec_fl_matVec` (constant γ_n via `matVec_backward_error`). | source-closed (column/matVec form) |
| (18.11) | Perturbation bound |ΔAᵢ| ≤ γ_{n+2}|A|: `computedMatPowVec_fl_matVec_gamma_add_two` (γ_n ≤ γ_{n+2} monotonicity; the printed constant is stated verbatim). | source-closed |
| unnumbered (p. 8) | Componentwise chain |fl(Aᵐeⱼ)| ≤ (1+γ_{n+2})ᵐ(|A|ᵐeⱼ): `matPow_componentwise_bound` (+ matrix form `matPow_matrix_bound`). | source-closed |
| (18.12) | Sufficient condition ρ(|A|) < 1/(1+γ_{n+2}). CLOSED at full printed strength: `matPow_convergence_spectral(_fl)` in `MatrixPowersSpectral.lean` takes `spectralRadius ℂ (absMatrixComplexified A) ≤ ρ` (Mathlib's genuine spectral radius of the complexified |A|) with `(1+γ_{n+2})·ρ < 1` and concludes ‖fl(Aᵐv₀)‖∞ → 0, via Gelfand's formula (`eventually_matPow_abs_le_of_spectralRadius_le`) and the repo↔Mathlib bridges `matPow_eq_matrix_pow`/`infNorm_eq_linfty_opNorm`/`linfty_opNorm_map_ofReal`. Perron–Frobenius is NOT needed for the sufficient direction. Sharper practical variants also available: Collatz–Wielandt certificate form (`matPow_convergence_weighted(_fl)`) and the ‖A‖∞ surrogate (`matPow_convergence_bound`). | source-closed (literal spectral form) |
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
closure is attempted; **normal-matrix identity `‖Aᵏ‖₂ = ρ(A)ᵏ` — now CLOSED**
(`norm_pow_normal_eq` in `Analysis/MatrixPowersSchur.lean`, over ℂ, [Nonempty]);
**numerical radius `r(A)` — now BUILT** (`Analysis/NumericalRadius.lean`: sandwich
`r(A) ≤ ‖A‖₂ ≤ 2·r(A)` unconditional; field-of-values-free via polarization),
power bound conditional on Berger (allowed-BLOCKED); **departure-from-normality
definitions — now BUILT** (`Analysis/MatrixPowersHenrici.lean`, see the (18.7) row).

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
- `higham_eq_18_5_alt_real_jordan` — eq (18.5) alternative form, real-∞.
- `matPow_abs_weighted_bound`, `matPow_convergence_weighted(_fl)` — eq (18.12) certificate form.
- `MatrixPowersSpectral.lean` — eq (18.12) literal spectral form: `absMatrixComplexified`, `matPow_eq_matrix_pow`, `infNorm_eq_linfty_opNorm`, `linfty_opNorm_map_ofReal`, `eventually_matPow_abs_le_of_spectralRadius_le` (Gelfand), `matPow_convergence_spectral(_fl)`.
- `MatrixPowersComplex.lean` — Theorem 18.1 at printed generality: complex telescoping engine, `cDiagMatrix*`, `complexMatrixInfNorm_cJordan_conj_le`, `cJordanRunLength`, `exists_cJordan_scaling_vector`, `complex_jordan_similarity_absorbs`, `higham_18_1_complex_jordan_tendsto`, `higham_18_1_complex_jordan_fl_tendsto`.

## Open Selected Rows (not-proved ledger)

| Selected row | Missing foundation | Smallest next Lean theorem | Current blocker | Status |
|---|---|---|---|---|
| JNF existence over ℂ (background lemma: every A has Jordan data) | classical Jordan Normal Form over ℂ | `∃ B, Matrix.IsSimilar A B ∧ (B is a Jordan matrix)` for arbitrary `A : Matrix (Fin n) (Fin n) ℂ` | ~~Mathlib has no classical JNF~~ — now BUILT | **CLOSED** (`Analysis/NilpotentJordanChain.lean`): `jordan_normal_form` and `exists_isSimilar_jordan` prove full classical JNF over ℂ UNCONDITIONALLY (axiom-clean). The previously-missing nilpotent Jordan-chain theorem (`nilpotentJordanBasis_holds`, `exists_isSimilar_nilpotentJordanForm`) is proved via Mathlib's PID structure theorem `Module.torsion_by_prime_power_decomposition` applied to `ℂⁿ` as a `ℂ[X]`-module (`Module.AEval'`, X acting as the nilpotent part): the cyclic summands `ℂ[X]⧸(Xᵏ)` in the reversed monomial basis ARE the nilpotent shift blocks. This discharges the `NilpotentJordanBasis` hypothesis in `JordanNormalForm.lean`, so Theorem 18.1's general complex case no longer needs Jordan data supplied — the JNF existence Higham takes as given is now formalized. |
| Theorem 18.2, printed pseudospectral form | pseudospectra Λ_ε, ρ_ε; eigenvalue perturbation input from [620, 1995] | definition of Λ_ε(A)/ρ_ε(A) over the repo matrix layer | pseudospectra absent from Mathlib and repo | DEFERRED |
| (18.4)/(18.5) all-p variants | CLOSED — see the (18.4) and (18.5) inventory rows: `MatrixPowersLp.lean` and `MatrixPowersLpJordan.lean` supply the previously missing Lp lemmas (entrywise domination, diagonal bound, shift bound, bidiagonal bound — new lemmas about the existing `complexMatrixLpNormOfReal`, not reproofs of owned results) and both printed bounds at every real exponent 1 ≤ p < ∞ for complex data. | closed |
| (18.5) primary printed form (κ of the δ⁻¹A Jordan transform) | δ⁻¹A Jordan-transform bookkeeping | restatement of `higham_eq_18_5_alt_real_jordan` with the rescaled transform | low value beyond the closed alternative form | OPEN (low priority) |
| (18.7) | Schur triangularization | — | absent from Mathlib v4.29.0 | DEFERRED |
| (18.8)/(18.9) | pseudospectra | — | absent from Mathlib/repo | DEFERRED |
| Gelfand limit citation (p. 342, unnumbered) | — | — | CLOSED as a dependency: `matPow_eq_matrix_pow` + `eventually_matPow_abs_le_of_spectralRadius_le` import Mathlib's Gelfand formula into repo vocabulary (used by the (18.12) literal closure) | closed (dependency) |
| numerical radius bound (p. 343, unnumbered) | field of values | — | **Foundation BUILT**: `Analysis/NumericalRadius.lean` defines `numericalRadius A` over ℂ and proves the two-norm sandwich `r(A) ≤ ‖A‖₂ ≤ 2·r(A)` (`numericalRadius_sandwich`, both halves, unconditional) plus the achievable half `‖Aᵏ‖₂ ≤ 2·r(Aᵏ)`; the power bound `‖Aᵏ‖₂ ≤ 2·r(A)ᵏ` is now UNCONDITIONAL for all A, all k (`BergerGeneral.norm_pow_le_two_mul_numericalRadius_pow`), Berger's `r(Aᵏ) ≤ r(A)ᵏ` having been PROVED via Pearcy's roots-of-unity route (`numericalRadius_pow_le`) | sandwich + power bound both CLOSED (Berger proved, no dilation) |

### Blocked-Foundation Progress (2026-07-04, goal: resolve blocked rows)

- **Theorem 18.2 pseudospectral criterion — STRENGTHENED to unconditional** (`MatrixPowersPseudospectralCriterion.lean`): `pseudospectrum_in_unit_disc_of_pseudospectralRadiusLt`, `spectralRadius_lt_one_of_pseudospectralRadiusLt`, and `higham_18_2_pseudospectral_criterion` derive the criterion→convergence direction WITHOUT the [620] `h620` witness (the ε-pseudospectrum's spectrum-in-unit-disc content is proved inline). The achievability lower bound `ρ_ε ≥ ρ+g` — the [620] direction the book cites without proof — is now CONSTRUCTIVELY CLOSED (Wave-10, `Analysis/PseudospectralLowerBound.lean`, axiom-clean, NO external paper): `pseudospectrum_mem_of_aligned_rankOne_perturbation` + `pseudospectralRadius_outward_growth_point` exhibit the explicit aligned rank-1 perturbation `E_t = t·v u*/(u*v)` giving `(A+E_t)v=(λ+t)v`, hence `ρ_ε(A) ≥ ρ(A) + c·ε` (strict for ε>0), with the textbook `c = |u*v|` (reciprocal eigenvalue condition number) under the honest 2-norm normalization `‖v u*‖₂ = 1/|u*v|`. So BOTH directions of the Thm 18.2 criterion are now formalized.
- **Schur triangulation over ℂ — BUILT (unconditional):** `Analysis/SchurTriangulation.lean` proves `schur_triangulation` (`∃ U T, U ∈ unitaryGroup ∧ Uᴴ A U = T ∧ T upper-triangular`) and the `T = D + N` split by a complete deflation induction (eigenvalue existence over ℂ → unit eigenvector → orthonormal extension → block re-embedding), axiom-clean. This closes the (18.7) foundation gap and enables the §18.1 normal-matrix identity (Wave-2 modules `MatrixPowersHenrici.lean` / `MatrixPowersSchur.lean`). It is Schur, NOT Jordan: the JNF-existence gap for Theorem 18.1's general complex case remains (Schur ≠ JNF; Mathlib still lacks classical JNF).
- **Numerical radius sandwich — BUILT:** `Analysis/NumericalRadius.lean` — `r(A) ≤ ‖A‖₂ ≤ 2·r(A)` unconditional over ℂ; the §18.1 power bound is honest-conditional on Berger (no unitary dilation in Mathlib).
- **eq (18.8) Trefethen resolvent bound — DEFERRED (exact obstruction):** needs a matrix holomorphic/Dunford functional calculus + resolvent-norm inequality, both absent from Mathlib v4.29 (only the scalar `circleIntegral` exists).
- **‖P⁻¹‖₂ = 1/σ_min spectral core — BUILT (cross-cutting, ch16):** `Analysis/InverseOpNorm2.lean` proves the Rayleigh λ_min lower bound on the Gram matrix and the exact `σ_min·‖x‖₂ ≤ ‖Px‖₂` / `‖x‖₂ ≤ (1/σ_min)‖Px‖₂` operator bounds, plus Sylvester/Lyapunov `InverseOpBound` discharge bridges. This reduces the ch16 (16.24)/(16.27) Ψ/Lyapunov "supplied M" caveat to a σ_min operator-form input (the remaining gap is only the vec-isometry `frobNorm ↔ ℓ²` glue).
- **Semiconvergent block-form existence — REDUCED (ch17 [106]):** `Algorithms/StationaryIterationSemiconvergentExistence.lean` proves `X⁻¹GX = diag(I_r,Γ)` from real column conditions (eigenvalue-1 eigenvectors + G-invariant complement + Γ row-sum contraction), discharging the consuming module's block-form data hypotheses (+ two end-to-end corollaries). This is an honest REDUCTION of [106], not full closure — an adversarial audit confirmed the column conditions are target-EQUIVALENT (given invertibility) to the similarity itself, so the file's genuine work is constructing `J = diag(I_r,Γ)`, transferring the Γ contraction, and reassembling the product-form similarity; deriving the basis `X` from convergence of `Gᵐ` stays folded into the hypothesis, exactly as the book takes the form as given.

### Wave-2 (Schur-enabled closures, 2026-07-04) — all axiom-clean, adversarially audited + verified (workflow `split3b-wave2-schur`)

- **(18.7) Henrici departure — CLOSED at Frobenius/departure level** (`Analysis/MatrixPowersHenrici.lean`): `frobSq_schur_pythagoras` (`‖A‖_F²=Σ|λ_i|²+‖N‖_F²`), `departureFSq_eq_frobSq_sub_sum_sq_eigs` (`Δ_F²=‖A‖_F²−Σ|λ_i|²`), `departureFSq_form_independent`, `A_charpoly_factors_schur` (spectrum=Schur diagonal), normal easy direction. Full Henrici inequality + (18.7) binomial power bound remain open (extremal / numerical-radius machinery).
- **§18.1 normal identity + Schur power expansion — CLOSED** (`Analysis/MatrixPowersSchur.lean`): `pow_eq_unitary_conj` (`Aᵏ=U(D+N)ᵏUᴴ`), `strictUpper_pow_eq_zero` (`Nⁿ=0` nilpotency — Jordan-free finite expansion), `normal_upperTriangular_isDiag` + `normal_schur_strictUpper_eq_zero` (the "normal Schur factor is diagonal" fact absent from Mathlib, proved from scratch — this also discharges Henrici's hard normal⟹N=0 direction), and `norm_pow_normal_eq` (`‖Aᵏ‖₂=ρ(A)ᵏ` for normal A, [Nonempty (Fin n)]). Berger's general power inequality remains allowed-BLOCKED (needs unitary dilation).
- **ch16 complex-Sylvester Schur discharge — BUILT (complex path)** (`Analysis/SylvesterSchurExistence.lean`): `complexSylvester_schur_factors_exist` (Schur factors exist unconditionally, discharging the "supplied factors" datum for the complex path) + full complex Bartels–Stewart column solve `complexSylvester_exists_unique_of_schur_shift` (`∃! X, AX−XB=C` over ℂ, only residual hypothesis = per-column eigenvalue-separation `det(R−μ I)≠0`, not target-equivalent). Honest scope: does NOT touch the ch16 *real* quasi-triangular theorems (16.4/16.7-16.8) — a real matrix has no real triangular Schur form; that real-Schur/quasi-triangular route stays Codex's blocked lane.

### Wave-3 (2026-07-04) — (18.7) power bound closed; [106] necessity partial

- **(18.7) 2-norm power bound — CLOSED** (`Analysis/MatrixPowersBinomialBound.lean`, ACCEPT + axiom-clean): the printed truncated binomial `‖Aᵏ‖₂ ≤ Σ_{i<n} C(k,i)ρ^{k−i}Δ₂ⁱ` (`opNorm_schurpow_le_binomial`, `exists_schur_powerBounds`) via a Pascal-recursion decomposition of `(D+N)ᵏ` into N-degree pieces + band-shift truncation from `Nⁿ=0`; plus `norm_pow_nilpotent` (ρ=0 case, stronger than printed) and the crude `(ρ+Δ₂)ᵏ`. Genuine Mathlib l2 op-norm; `Δ₂=‖N‖₂` the specific-Schur value (min-over-forms not claimed attained). Only the Henrici *extremal* inequality remains open.
- **[106] semiconvergent existence — NECESSITY direction proved (partial)** (`Analysis/SemiconvergentSpectral.lean`, ACCEPT_WITH_NOTES, axiom-clean, ch17-facing): the honest CONVERSE of the forward power machinery — `eigenvalue_norm_le_one_of_orbit_tendsto` (convergence of `Gᵐ` ⟹ every eigenvalue `‖μ‖ ≤ 1`), the semisimple-collapse `maxGenEigenspace 1 = eigenspace 1` (given `IsFinitelySemisimple`), and the ℂ primary-decomposition internal direct sum (`isInternal_maxGenEigenspace`). The file ITEMIZES the four remaining obstructions to full [106] existence — (1) semisimple-at-1 FROM convergence (needs a Jordan-block growth lower bound, absent), (2) strict `|μ|<1` (needs the scalar power-limit dichotomy), (3) ℂ→ℝ descent (no real-Jordan/real-invariant API), (4) the `ρ(Γ)<1 ⟹ ‖D⁻¹ΓD‖∞<1` diagonal-similarity contraction — each naming the exact missing Mathlib v4.29 lemma. Full [106] remains genuinely allowed-BLOCKED.

### Wave-4 (2026-07-05) — genuine attempts at ALL remaining blocked items (each axiom-clean, adversarially verified, workflow `split3b-wave4-resolve-all-blocked`)

Every previously "allowed-BLOCKED" item was genuinely ATTEMPTED (not a-priori dismissed); each attempt closed substantial new unconditional content and reduced the residual to an *evidenced* obstruction naming the exact missing Mathlib primitive.

- **Classical JNF over ℂ (18.1a/18.1b) — primary decomposition CLOSED; full JNF conditional** (`Analysis/JordanNormalForm.lean`): `exists_primary_blockDiagonal_similar` proves A is similar to a block-diagonal `μ•I + Nμ` form with each `Nμ` nilpotent (`isNilpotent_toMatrix_nilpotentPart`), unconditionally — the honest "reduction to scalar+nilpotent". Full JNF is `jordan_normal_form_of_nilpotentJordanBasis` under the single explicit `NilpotentJordanBasis` hypothesis; evidenced obstruction = the nilpotent Jordan-chain theorem (needs the PID-torsion `ℂ[X]⧸(Xᵏ)` decomposition plumbing, absent from Mathlib v4.29).
- **Berger power inequality — FULLY CLOSED (general k, arbitrary A)** (`Analysis/BergerGeneral.lean`, axiom-clean, Wave-11): `numericalRadius_pow_le` proves `r(Aᵏ) ≤ r(A)ᵏ` UNCONDITIONALLY for every complex A and every k, via **Pearcy's elementary roots-of-unity averaging** (Michigan Math. J. 13 (1966)) — DFT telescoping `pⱼ−(ξωʲ)Tpⱼ=g`, numerical-range positivity `Re⟪g,pⱼ⟫≥0`, character orthogonality `Σpⱼ=k·x`, phase choice — NO unitary dilation (the prior wave rigorously showed the resolvent/Berger-Kato route reaches only ‖A‖≤1, not r(A)≤1). Consequently `norm_pow_le_two_mul_numericalRadius_pow` gives the **unconditional §18.1 (18.7) power bound `‖Aᵏ‖₂ ≤ 2·r(A)ᵏ` for ALL A and ALL k**, removing the Hermitian restriction of `BergerInequality.lean` and the powers-of-two restriction of `BergerResolvent.lean`. (Earlier bullets' "Berger allowed-BLOCKED / conditional" and "needs unitary dilation" remarks are SUPERSEDED — Berger is now proved.)
- **Pseudospectral resolvent (18.8) — resolvent-norm lower bound CLOSED** (`Analysis/PseudospectralResolvent.lean`): `spectrum_one_le_dist_mul_norm_resolvent` proves `1 ≤ ‖z−w‖·‖R(z)‖` (hence `‖R(z)‖ ≥ 1/dist(z,σ)`) for any Banach algebra, the always-true lower half of `‖(zI−A)⁻¹‖=1/σ_min`. Full (18.8) evidenced-BLOCKED = A-valued resolvent analyticity + Cauchy/residue functional calculus, absent.
- **Henrici extremal inequality (18.7) — proved with explicit constant** (`Analysis/HenriciExtremal.lean`): `henrici_departure_le_of_schur` proves `Δ_F(A)² ≤ (Σ_{m<n}√m)·‖AᴴA−AAᴴ‖_F` unconditionally (summation-by-parts `partialTrace_eq_neg_blockMass` + Cauchy–Schwarz `blockMass_le`). **IMPROVED constant (Wave-9, `Analysis/HenriciSharpConstant.lean`, axiom-clean):** `henrici_departure_le_sharp_of_schur` proves the same inequality with the smaller closed-form constant `K_n = ((n−1)n(2n−1)/6)^{1/2}` (global trace-weighted Cauchy–Schwarz + a Fubini reindexing identity), with `henriciSharpConst_le_henriciConst` proving `K_n ≤ Σ√m` (strict for n≥3; ~0.577·n^{3/2} vs 0.667·n^{3/2}). **FULLY SHARP constant now CLOSED (Wave-10, `Analysis/HenriciSharpConstantExact.lean`, axiom-clean):** `henrici_departure_le_exactSharp_of_schur` proves `Δ_F(A)² ≤ ((n³−n)/12)^{1/2}·‖AᴴA−AAᴴ‖_F` — Higham's exact printed sharp constant — PLUS a matching general-n tightness witness proving optimality. New route (not the stalled variational one): the commutator diagonal is trace-free (`sum_commDiagRe_eq_zero`, `Σd_i=tr C=0`), so the Wave-9 uncentered reindexing weights can be CENTERED for free, and `Σ_i(i−(n−1)/2)² = (n³−n)/12` keys the sharp bound. (18.7) is now FULLY closed including the sharp Henrici inequality.
- **[106] gaps (2),(4),(1) CLOSED** (`Analysis/SemiconvergentExistenceGaps.lean`): `scalar_pow_tendsto_dichotomy` (gap 2: μᵐ converges ⟹ μ=1 ∨ ‖μ‖<1) upgrading the closed-disk bound to the printed strict condition; `exists_diag_infNorm_conj_lt_one_of_upperTriangular` (gap 4: Householder δ-scaling diagonal contraction); `genEigenvector_one_rank_two_orbit_norm_tendsto_atTop` (gap 1: rank-2 Jordan chain at 1 ⟹ orbit diverges). Only gap (3) ℂ→ℝ descent remains as the lone bridge (evidenced-BLOCKED = no real-Jordan/real-Schur API), and gap (4)-general reduces to it.

### Wave-5 (2026-07-05) — deep max-effort closures of the highest-leverage residuals (each axiom-clean, adversarially verified + aggregate-collision-checked, workflow `split3b-wave5-deep-closures`)

- **Classical JNF over ℂ — FULLY CLOSED** (`Analysis/NilpotentJordanChain.lean`): the nilpotent Jordan-chain theorem `exists_isSimilar_nilpotentJordanForm` (every nilpotent ℂ-matrix ~ ⨁ shift blocks) proved via Mathlib's PID `Module.torsion_by_prime_power_decomposition` on `ℂⁿ` as a `ℂ[X]`-module (`Module.AEval'`); discharges `NilpotentJordanBasis`, giving UNCONDITIONAL `jordan_normal_form` / `exists_isSimilar_jordan`. **This resolves the JNF-existence background lemma behind Theorem 18.1's general complex case** — the one item previously labelled research-scale. Reusable classical-JNF-over-ℂ result.
- **ℂ→ℝ descent — dim-≤2 real invariant subspace FULLY CLOSED** (`Analysis/RealInvariantSubspace.lean`): `exists_real_invariant_subspace_dim_le_two` and the deflation-ready `real_peel_one_or_two` dichotomy (real eigenvalue 1×1 block, OR conjugate-pair genuine 2×2 `[[α,β],[−β,α]]` block with a proved linearly-independent real basis). This IS the peel-1-or-2 primitive that the Wave-4 RealSchur/[106] obstructions named as the lone missing piece; it closes the gap-(3) analytic core. Residual to the FULL orthogonal (16.4): only the variable-d (1-or-2) orthogonal deflation INDUCTION (a large re-derivation of the peel-1-hardwired Schur template for variable block size — engineering, no missing math).
- **Resolvent holomorphic functional calculus (18.8) — analyticity + ML-estimate CLOSED** (`Analysis/ResolventFunctionalCalculus.lean`): `resolvent_differentiableOn`/`resolvent_analyticAt` (resolvent analytic on the resolvent set — the bridge the Wave-4 note thought missing, actually a near-one-liner via Mathlib's `spectrum.hasDerivAt_resolvent`), `pow_smul_resolvent_differentiableOn`, and the contour `norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le`. `norm_pow_le_of_cauchy_representation` gives the (18.8) bound GIVEN the Dunford residue identity as an explicit hypothesis; the lone remaining step is the A-valued term-by-term Neumann-series/contour interchange (needs a Bochner dominated-convergence swap; evidenced).

### Wave-6 (2026-07-05) — finishing the assembly residuals (each axiom-clean, adversarially verified + collision-checked, workflow `split3b-wave6-finish-assembly`)

- **FULL real quasi-triangular Schur (16.4) — CLOSED** (`Analysis/RealQuasiSchur.lean`): `real_quasi_schur` proves every real A orthogonally similar to a real 1×1/2×2-block quasi-upper-triangular R, unconditionally, via the variable-d deflation induction on the `RealInvariantSubspace` primitive. Closes the Wave-5 (16.4) residual.
- **(18.8) Dunford residue identity — CLOSED** (`Analysis/DunfordResidue.lean`): the A-valued Neumann-series↔contour dominated-convergence swap (`hasSum_circleIntegral_pow_smul_resolvent`), `pow_eq_two_pi_I_inv_smul_circleIntegral` (aᵏ=(2πi)⁻¹∮zᵏR(z)dz), and the UNCONDITIONAL contour power bound `norm_pow_le_of_cauchy_circleIntegral`. Closes the Wave-5 (18.8) residue residual; the §18.2 resolvent/Cauchy route to (18.8) is closed at the analytic level (only the ρ_ε *packaging* needs the external [620]).
- **[106] GAP(1) semisimplicity-from-convergence CLOSED + downstream assembly** (`Analysis/SemiconvergentBlockFormExists.lean`): `maxGenEigenspace_one_eq_eigenspace_of_forall_orbit_tendsto` (convergence of every orbit ⟹ eigenvalue 1 semisimple — the analytic content the book folds into "G semiconvergent"), and `semiconvergent_block_form_exists_of_triangular_complement(_diag_conv)` which, GIVEN a real triangular-complement basis, CONSTRUCTS the ∞-norm contraction (GAP-4) and derives the modulus bound from convergence (GAP-2) to discharge the full block form. The one remaining input — producing that real basis from convergence — needs the full (16.4) `real_quasi_schur` (now available) + a permutation; assembled in Wave-7 (`SemiconvergentExistenceFull.lean`).

| Command | Result | Notes |
|---|---|---|
| `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixPowers.lean` | PASS | after each increment |
| `#print axioms` on all new source-facing theorems | `[propext, Classical.choice, Quot.sound]` | no sorry/new axiom |
| hygiene scan (`sorry\|admit\|axiom\|unsafe\|opaque`) | clean | comment mentions of "axiom" are prose flags on `similarity_absorbs` |
