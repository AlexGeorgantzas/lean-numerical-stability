# Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. — Chapter 6 (Norms)

> **Fresh PDF-first repair (2026-07-21): terminal SOURCE-DISCREPANCY.** The precise prose omitted by the
> previous ledger is now closed. `Higham6Asides.lean` contains a compiled
> counterexample to the book's false claim that the Euclidean norm is
> differentiable at zero, the corrected nonzero Fréchet derivative, and the
> finite Hölder equality theorem from the magnitude-power/common-ray
> conditions together with explicit endpoint equality witnesses.
> `Higham6BlockAntidiag.lean` proves the full finite-conjugate-exponent identity
> `‖[[0,A],[Aᴴ,0]]‖ₚ = max(‖A‖ₚ,‖A‖q)` without the former `hblock` premise.

> **Fresh strict audit and repair (2026-07-18): gate PASS.** The new
> `MixedInverseAmbientRelativeAmplificationRadiusSet` uses the book's common
> ambient-radius denominator, and
> `mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii`
> derives its actual `sSup` limit at the printed product value. The former
> self-normalized API remains available but is no longer used as the source gate.
> The fresh re-audit also corrected a stale ledger mapping: Lemma 6.6(a)/(c)
> was already closed in the imported `Algorithms/Chapter06Lemma66.lean` module.

- **Edition / pages:** 2nd ed., pp. 105–117.
- **Audit mode:** core (primary labels + numbered equations + central definitions + precise body prose; Problems recorded but optional).
- **Ownership:** Chapter 6 is the NORM FOUNDATION LAYER for the whole formalization. Primary home:
  `NumStability/Analysis/Norms.lean` (~23.6k lines, source-facing `CVec`/`CMatrix` norm infrastructure).
  Secondary homes: `NumStability/Analysis/MatrixAlgebra.lean` (real rectangular `rectOpNorm2Le`
  transfer layer, Lemma 6.6(b)–(d) predicate forms), `NumStability/Algorithms/MatrixPowersLp.lean`
  and `Analysis/MatrixPowersLp185Primary.lean` (downstream consumers). Consumers cite the Lemma 6.6 chain
  from `Algorithms/HighamChapter10.lean` and `Algorithms/Ch14GaussJordanSPDCorollary.lean`.
- **Audit date:** 2026-07-16 (branch `formalize/split4-claude`, worktree `ch18-split3-claude-...044646`).
- **Axiom spot-check:** `monotone_iff_absolute_complexVectorNorm`,
  `exists_rankOneCMatrix_isMixedSubordinateMatrixNormValue_one`,
  `complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct`,
  `complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii_of_inverse`,
  `complexMatrixLpNormOfReal_two_absMatrix_bounds`,
  `Lemma66.lemma66_a_op2_le`, `Lemma66.lemma66_c_op2_le`,
  `schneiderStrang_mixedSubordinateMatrixNormRatio_isMax` — all report exactly
  `[propext, Classical.choice, Quot.sound]`.

## Primary labels

| Label | Printed statement (summary) | Status | Lean decls (Norms.lean unless noted) | Scope notes |
|---|---|---|---|---|
| Def. 6.1 | Monotone (`\|x\| ≤ \|y\| ⇒ ‖x‖ ≤ ‖y‖`) and absolute (`‖ \|x\| ‖ = ‖x‖`) norms on C^n | VERIFIED | `IsMonotoneComplexVectorNorm`, `IsAbsoluteComplexVectorNorm` (~l.635) | Abstract norms on `CVec n` via `IsComplexVectorNorm`. |
| Thm. 6.2 (Bauer–Stoer–Witzgall) | A norm on C^n is monotone iff absolute | VERIFIED | `monotone_iff_absolute_complexVectorNorm` (l.799), `absolute_norm_iff_monotone_norm` (l.814); easy direction `absolute_of_monotone_complexVectorNorm` (l.787) | Proved from scratch (coordinate-contraction argument), not imported as hypothesis; printed strength (arbitrary norm on C^n). Higham himself defers the proof to Horn–Johnson / Stewart–Sun. |
| Lemma 6.3 | For unit `x` (α-norm), unit `y` (β-norm) there is `B` with `‖B‖_{α,β} = 1`, `Bx = y` | VERIFIED | `exists_rankOneCMatrix_isMixedSubordinateMatrixNormValue_one` (l.19799); map form `exists_rankOne_isMixedSubordinateNormValue_one` (l.19783); rank-one core (l.19741) | General complex vector norms; the dual/norming functional `z` is produced by a finite-dimensional Hahn–Banach bridge (`NormedCVec.exists_normingFunctionalAt_of_unit_vector`), matching the printed dual-vector proof. |
| Thm. 6.4 | `κ_{α,β}(A) := lim_{ε→0} sup_{‖ΔA‖_{α,β} ≤ ε‖A‖_{α,β}} ‖(A+ΔA)^{-1} − A^{-1}‖_{β,α} / (ε‖A^{-1}‖_{β,α}) = ‖A‖_{α,β}‖A^{-1}‖_{β,α}` | VERIFIED | `MixedInverseAmbientRelativeAmplificationRadiusSet`, `mixedInverseAmbientRelativeAmplificationRadiusSup`, and `mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii` | The feasible value is literally `(e/s)/rho` for every `0 < d ≤ rho*a`. The proof derives the endpoint resolvent upper bound, chooses the sharp perturbation on the boundary `d = rho*a`, constructs perturbed right inverses and norm witnesses, realizes the actual `sSup`, and squeezes it to `a*s`. The small-invertibility guard is eventual and immaterial in the `rho → 0` limit. |
| Thm. 6.5 (Gastinel, Kahan) | `dist_{α,β}(A) = (‖A‖_{α,β}‖A^{-1}‖_{β,α})^{-1} = κ_{α,β}(A)^{-1}` | VERIFIED | `complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct` (l.20505), `..._min_eq_inv_norm_mul_inverse_norm` (l.20488); map level (l.20430–20483); lower bound (l.20194), attaining singular perturbation via Lemma 6.3 (l.20241, l.20296) | General norms; distance stated as attained minimum (`IsMinimumMixedRelativeSingularDistance`), matching the printed min. Both directions proved: every singular `A+ΔA` obeys `‖ΔA‖/‖A‖ ≥ κ^{-1}`, and a rank-one `ΔA = B/‖x‖_α` attains it with `(A+ΔA)A^{-1}y = 0`. |
| Lemma 6.6 | (a) columnwise `‖a_j‖₂ ≤ ‖b_j‖₂` ⇒ `‖A‖_F ≤ ‖B‖_F`, `‖A‖₂ ≤ √rank(B)‖B‖₂`, `\|A\| ≤ ee^T\|B\|`; (b) `\|A\| ≤ B ⇒ ‖A‖₂ ≤ ‖B‖₂`; (c) `\|A\| ≤ \|B\| ⇒ ‖A‖₂ ≤ √rank(B)‖B‖₂`; (d) `‖A‖₂ ≤ ‖\|A\|‖₂ ≤ √rank(A)‖A‖₂` | VERIFIED | Imported `Algorithms/Chapter06Lemma66.lean`: (a) `Lemma66.lemma66_a_frobenius_le`, `Lemma66.lemma66_a_op2_le`, `Lemma66.lemma66_a_abs_entry_le`; (c) `Lemma66.lemma66_c_op2_le`; sharpness `Lemma66.lemma66_a_op2_sharp`. (b)/(d): `rectOpNorm2Le_of_abs_entry_le`, `complexMatrixLpNormOfReal_two_absMatrix_bounds`, `complexMatrixOp2_absMatrix_bounds`, and the real rectangular transfer `rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le`. | Every printed implication is present at source strength. The previous PARTIAL row was a stale search/mapping error, not a missing theorem. |
| Table 6.1 | Attainable constants `α_pq` with `‖x‖_p ≤ α_pq ‖x‖_q` (1, 2, ∞) | VERIFIED | Via eq. (6.4) both directions: `complexVecLpNorm_le_complexVecLpNorm_of_exponent_le` (l.1522), `complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le` (~l.1358); all-ones sharpness witness `complexVecLpNorm_const_one_ofReal` (l.555); ∞ endpoints by dedicated endpoint lemmas | Finite real exponents general `p₁ ≤ p₂`; table entries are specializations. |
| Table 6.2 | Attainable constants `α_pq` for matrix norms 1, 2, ∞, F, M, S incl. rank-sensitive `√rank(A)` (F/2) and `√(mn·rank(A))` (S/2) entries | VERIFIED | Entry lemmas l.10123–10307 (S/M, M/F, F/S, S/F, F/M), M/2 (l.13688), rank-sensitive F/2 (l.12935) and S/2 (l.12949–12987); quotient-constant package incl. sharpness witnesses `l.14061–14347` (all entries except S/2, which has its own witnesses); Problem 6.1 rank-one witness family (l.13714–14150, 14346) | Sharp witnesses supplied for every entry; S/2 sharpness realized by real Hadamard (l.17806) and complex roots-of-unity Vandermonde (l.18325) witnesses. |

## Numbered equations

| Eq. | Content | Status | Lean decls |
|---|---|---|---|
| (6.1) | Hölder inequality `\|x^*y\| ≤ ‖x‖_p‖y‖_q` and equality prose | VERIFIED | `complexVecLpNorm_holder`; endpoint 1/∞ forms; `higham6_holder_equality_of_powerProfile_sameRay` proves equality from the stated power-profile linear dependence and common complex ray; `higham6_holder_endpoint_equality_standardBasis` supplies both endpoint witnesses. |
| (6.2) | Dual norm `‖x‖_D = max_{z≠0} \|z^*x\|/‖z‖` | VERIFIED | `IsDualFunctionalNormValue` least-bound predicate (l.2418) shown equal to unit-vector max (l.18993) and nonzero-ratio max (l.19006). Duality theorem (dual of dual = original) is cited-out by Higham himself; not formalized (SKIP-OK: proof deferred to Horn–Johnson in print). |
| (6.3) | Existence of dual vector: `z^*y = ‖z‖_D‖y‖ = 1` | VERIFIED | `IsNormingFunctionalAt` (l.2406); existence `NormedCVec.exists_normingFunctionalAt_of_unit_vector` (Hahn–Banach bridge); least-bound form (l.2727). |
| (6.4) | `‖x‖_{p₂} ≤ ‖x‖_{p₁} ≤ n^{1/p₁−1/p₂}‖x‖_{p₂}`, attainable | VERIFIED | l.1522 / ~l.1358 + all-ones witness (l.555). |
| (6.5)/(6.6) | Subordinate and mixed subordinate matrix norm (max/ratio forms); `‖A‖₁` max col sum, `‖A‖_∞` max row sum, `‖A‖₂ = σ_max` | VERIFIED | Least-bound carrier `IsMixedSubordinateMatrixNormValue` with max forms (l.18424–19123); p=1 and p=∞ explicit formulas (l.16873, 16925, 19332–19441); `complexMatrixOp2_eq_top_singularValue` (l.11933); `‖A^*A‖₂ = ‖A‖₂²` (l.11846). |
| (6.7) | `‖AB‖_{α,β} ≤ ‖A‖_{γ,β}‖B‖_{α,γ}` | VERIFIED | l.18808 (bound form), l.18822 (value form); consistency of matrix p-norms (l.8515). |
| (6.8) | `κ_{α,β}(A) = ‖A‖_{α,β}‖A^{-1}‖_{β,α}` | VERIFIED | `mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii` returns the product predicate and the printed ambient-radius limit at the same value. |
| (6.9)/(6.10) | Proof steps: `sup_{‖ΔA‖≤1}‖A^{-1}ΔAA^{-1}‖ = ‖A^{-1}‖²` and the lower-bound chain | VERIFIED | Upper: `mixedSubordinate_inverseSandwich_bound` (l.20525) and value form (l.20540); lower/attainment: sharp linearized family (l.20777ff), Lemma-6.3-based step (l.18835). |
| (6.11) | Matrix p-norm definition | VERIFIED | Carrier + p=1/∞ max forms (l.16838–16925). |
| (6.12)/(6.13) | `max_j‖A(:,j)‖_p ≤ ‖A‖_p ≤ n^{1−1/p}max_j‖A(:,j)‖_p`; row analogue with `m^{1/p}` and exponent `p/(p−1)` | VERIFIED | Upper halves l.7381/7414 and l.17433/17481; lower halves l.16643/16658; source-facing bundles l.16754 and l.17496; concrete-function forms l.17677/17694. |
| (6.14) | Schneider–Strang: `max_{A≠0}‖A‖_α/‖A‖_β = (max_x ‖x‖_α/‖x‖_β)(max_x ‖x‖_β/‖x‖_α)` | VERIFIED | `schneiderStrang_mixedSubordinateMatrixNormRatio_isMax` (l.20002) for general vector norms, max attained via Lemma 6.3 rank-one construction; upper direction l.19965. |
| (6.15) | `max_{A≠0}‖A‖_{p₁}/‖A‖_{p₂} = n^{1/min − 1/max}` | VERIFIED | `complexMatrixLpNorm_pq_ratio_isMax` (l.20168) with sharp `n^{\|1/p−1/q\|}`; directional forms l.20105/20135; comparison/divided/bundled forms l.15114–15233, l.18337. |
| (6.16)/(6.17) | Two-sided p-vs-1 and p-vs-2 matrix norm equivalences | VERIFIED | (6.16): l.7807–7904, concrete l.17714; (6.17): l.14899–15092, concrete l.17727. |
| (6.18) | Riesz–Thorin interpolation `‖A‖_p ≤ ‖A‖_{p₁}^θ‖A‖_{p₂}^{1−θ}` | VERIFIED | l.9311 (concrete), l.8710ff (predicate machinery, dedicated Hadamard-three-lines analytic development l.5296–9377), endpoint-aware source form l.17315. |
| (6.19) | `‖A‖_p ≤ ‖A‖₁^{1/p}‖A‖_∞^{1−1/p}` (includes `‖A‖₂ ≤ √(‖A‖₁‖A‖_∞)`) | VERIFIED | l.9393 (mixed-bound form), l.9569 (concrete finite-real wrapper), has-bound wrapper l.9556. |
| (6.20) | `‖A‖_p ≤ ‖A‖₁^{2/p−1}‖A‖₂^{2−2/p}`, `1 ≤ p ≤ 2` | VERIFIED | l.19554 (source form), strict-interior wrapper l.19473. |
| (6.21) | `‖A^*‖_p = ‖A‖_q`, `1/p + 1/q = 1` | VERIFIED | l.16627 (adjoint value form), transpose version l.16609, bound half l.16533; finite conjugate exponents (endpoints via the p=1/∞ formulas). |
| (6.22) | `‖A‖₂ = σ₁(A)`, `‖A‖_F = (Σσᵢ²)^{1/2}` | VERIFIED | `complexMatrixOp2_eq_top_singularValue` (l.11933); Frobenius² = Σσᵢ² (l.10583); full rectangular SVD with unitary factors `U Σ V^* = A` exists (`exists_complexMatrixSVD...`, l.11549–11665); rank = #nonzero singular values (l.9884). Real-case `U, V` real refinement not formalized (prose aside). |
| (6.23)/(6.24) | Sparse-row/column refinements (Problem 6.14) | VERIFIED | Upper halves l.7461/7631 (row) and l.7645/7761 (column); lower halves l.16695; source-facing bundles l.16781/16810; concrete-function forms l.18355/18372. |

## Body prose claims (unnumbered)

| Claim | Status | Notes |
|---|---|---|
| Vector norm axioms; 1/2/∞ norms as Hölder p-norm cases | VERIFIED | `IsComplexVectorNorm` (l.88), `complexVecLpNorm` family. |
| 2-norm unitary invariance + gradient `∇‖x‖₂ = x/‖x‖₂` | SOURCE-CORRECTED | `higham6_euclideanNorm_not_differentiableAt_zero` refutes the literal “for all x” sentence; `higham6_euclideanNorm_hasFDerivAt_of_ne_zero` proves the corrected real Fréchet derivative at every nonzero complex vector. The unitary invariance results remain in `Higham6Asides.lean`. |
| `‖A‖_∞ = ‖\|A\|e‖_∞` | VERIFIED (equivalent form) | `complexMatrixInfNorm_absMatrix_eq` (l.3415) + row-sum characterization (l.9482); the literal ones-vector form is not stated but the content is identical. |
| Frobenius norm consistent; all subordinate norms consistent | VERIFIED | Matrix p-norm submultiplicativity (l.8515), (6.7) composition (l.18808); Frobenius product bounds in the Problem 6.5 operator-ideal block (l.12020–12130). |
| Max norm `‖A‖_M` not consistent; best bound `‖AB‖ ≤ n‖A‖_M‖B‖_M` with equality at all-ones | VERIFIED | `ch6aside_maxNorm_mul_le`, `ch6aside_maxNorm_allOnes_mul`, `ch6aside_maxNorm_equality_allOnes`, and `ch6aside_maxNorm_not_consistent` in `Higham6Asides.lean`. |
| Unitary invariance of 2- and F-norms; `‖A^*‖ = ‖A‖`; `‖QEQ^*‖₂ = ‖E‖₂` vs `‖XEX^{-1}‖₂ ≤ κ₂(X)‖E‖₂` | VERIFIED | `ch6aside_op2_two_sided_unitary_invariant` and `ch6aside_frobenius_two_sided_unitary_invariant` give the complex two-sided invariance; adjoint invariance and the similarity bound follow from the named adjoint results and submultiplicativity. |
| `κ(X) ≥ 1` and `κ_F(X) ≥ √n` | VERIFIED | `ch6aside_conditionNumber_ge_one`, `ch6aside_op2_conditionNumber_ge_one`, and `ch6aside_conditionF_ge_sqrt_n` in `Higham6Asides.lean`. |
| `‖[[0, A], [A^*, 0]]‖_p = max(‖A‖_p, ‖A‖_q)` (unnumbered display) | VERIFIED | `ch6aside_blockAntidiag_lp_eq` in `Higham6BlockAntidiag.lean`; `ch6aside_blockAntidiagLpCLM_components` proves the canonical `PiLp` block action and `ch6aside_withLpBlockSwapCLM_norm` proves the general max-norm identity. No residual block-norm premise. |
| `log ‖A‖_p` convex in `1/p` (Riesz–Thorin) | VERIFIED (as consequence) | Embodied in the (6.18) interpolation development; the convexity statement itself is the same inequality re-parametrized. |
| (6.16)/(6.17) estimate `‖A‖_p` within factor `n^{1/4}` from `‖A‖₁,‖A‖₂,‖A‖_∞` | SKIP-OK | Editorial consequence; the underlying inequalities are formalized. Figure 6.1: SKIP-OK (plot). |

## Problems (optional in core mode)

| Problem | Status | Lean anchors (Norms.lean) |
|---|---|---|
| 6.1 (prove Tables 6.1/6.2, attainability, Hadamard/Vandermonde S/2 equality) | SUBSTANTIAL | Rank-one witness family + profiles (l.13714–14150), all-quotient package (l.14346); real Hadamard S/2 witness (l.17806), complex roots-of-unity Vandermonde witness (l.18325); flat-entry/equal-singular-value equality analysis (l.13411–13611). The full "iff scalar multiple of Hadamard" only-if direction is characterized via the equality-case analysis (l.13599 notes the square full-rank real Hadamard iff as corollary); recorded as substantial rather than literal. |
| 6.2 (`‖xy^*‖ = ‖x‖‖y‖_D` subordinate) | VERIFIED | l.19667 (functional form), l.19700 (concrete matrix form). |
| 6.3 (`‖A‖ = max Re y^*Ax / (‖y‖_D‖x‖)`; `‖A^*‖ = ‖A‖_D`) | VERIFIED | Pairing carrier (l.18456–18462), dual characterization (l.19180), concrete wrapper (l.19246). |
| 6.4 (magic squares: `‖M_n‖_p = μ_n`) | VERIFIED | l.15578 (finite p), l.15643 (p = ∞ endpoint); doubly-stochastic core l.15482. |
| 6.5 (`‖ABC‖_F ≤ ‖A‖₂‖B‖_F‖C‖₂`, unitarily invariant generalization) | VERIFIED | l.12114 (complex F/2 product), operator-ideal generalization l.12733–12839 incl. bare unitarily invariant norm form (l.12793). |
| 6.6 (`κ_{α,β} = max gain / min gain`) | VERIFIED | l.20368 (map level), l.20395 (concrete matrix). |
| 6.7 (`ρ(A) ≤ ‖A‖` consistent norms) | VERIFIED | l.4708–4746 (map + matrix, max-modulus forms). |
| 6.8 (∃ consistent norm ≤ ρ(A)+δ; ρ<1 ⇒ ∃ norm <1) | VERIFIED | Triangularization + weighted-sup development (l.2831–5047), checked/source-facing forms l.8009/8051, contractive corollary l.8134. |
| 6.9 (`c₁‖A‖₂ ≤ ‖A‖_F ≤ c₂‖A‖₂` + equality cases) | VERIFIED | Equality-case pair both directions (l.13068–13205), source package l.13205. |
| 6.10 (block shear 2-norm formula; golden ratio) | VERIFIED | l.14823 (compact), l.14875 (printed square-root formula), golden ratio l.14885–14892. |
| 6.11 (`‖A‖_{1,β}`, `‖A‖_{α,∞}` formulas) | VERIFIED | l.17331 (a), l.17390 (b), rectangular generalizations; `‖A‖_{1,∞}` = max entry via the max-norm carrier. |
| 6.12 (HPD: `‖A‖_{∞,1} = max x^*Ax` on `‖x‖_∞=1`) | VERIFIED | l.4383 (PSD reusable form), l.4459 (source Hermitian PD wording). |
| 6.13 (Hadamard: `‖H‖_p = max(n^{1/p}, n^{1−1/p})`) | VERIFIED | l.17779 (finite real p), l.15987 (p = ∞ endpoint); predicate l.15659. |
| 6.14 (sparse (6.23)/(6.24)) | VERIFIED | See equations table. |
| 6.15 (`‖A‖_p ≤ ‖\|A\|‖_p ≤ n^{min(1/p,1−1/p)}‖A‖_p`) | VERIFIED | Lower half l.15256, sharp upper l.17581, row/column halves l.17522/17549; `\|A\|` carrier l.3073. |
| 6.16 (`ν(x) = Σ(\|Re x_i\| + \|Im x_i\|)`: real norm, not complex; induced `ν(A)`) | VERIFIED | Norm proof l.1168, non-complex-homogeneity subtlety l.1177, explicit induced expression l.3457–3537. |

## Honest-strength notes

1. **Theorem 6.4 is now literal.** The ambient-radius feasible set divides every
   relative inverse change by the common `rho`, not by the perturbation's own
   size. Its final theorem constructs the sharp boundary perturbation and all
   inverse/norm witnesses internally. The older self-normalized set is retained
   as a useful companion formulation but is not cited for source closure.
2. **Lemma 6.6(a) and (c) are closed at printed strength.** The imported
   `Algorithms/Chapter06Lemma66.lean` supplies the columnwise Frobenius,
   operator-2, and entrywise conclusions, the genuine-rank (c) bound, and the
   first printed sharpness witness. The optional second sharpness witness
   `A = eeᵀ`, `B = √n I` is not part of the selected core gate.
3. Hölder/duality/rank-one machinery ((6.1)–(6.3), Lemma 6.3, (6.14)) is done for **general abstract
   complex vector norms**, exceeding the p-norm-only reading, with a finite-dimensional Hahn–Banach
   norming-functional bridge replacing the cited duality theorem.
4. Endpoint (`p = 1, ∞`) cases are handled by separate endpoint lemmas throughout; the ENNReal `p`
   plumbing means most "for all p ≥ 1" rows are literally `1 ≤ p` real plus explicit endpoints.
5. A docstring citation is never counted as coverage: every row above was checked at the statement
   level against the printed text.

## Selected-scope gate: PASS (primary labels + numbered equations)

**Update (2026-07-14 audit-closure):** Lemma 6.6(a) and (c) are now CLOSED at printed strength in
`NumStability/Algorithms/Chapter06Lemma66.lean` (axiom-clean, adversarially verified):
`lemma66_a_frobenius_le` (a.i `‖A‖_F ≤ ‖B‖_F`), `lemma66_a_op2_le` (a.ii `‖A‖₂ ≤ √rank(B)‖B‖₂`),
`lemma66_a_abs_entry_le` (a.iii `|A| ≤ ee^T|B|`), `lemma66_c_op2_le` (c), plus `lemma66_a_op2_sharp`
(rank-1 equality witness showing √rank is attained). This clears the two primary-label blockers.

All five requested primary labels, including Theorem 6.4, are now VERIFIED at
printed strength, and all numbered equations (6.1)–(6.24) have statement-level
coverage. **Gate = PASS for the strict primary-label + numbered-equation +
central-definition scope.**

**Follow-up (2026-07-17):** the norm asides are now closed in `NumStability/Analysis/Higham6Asides.lean`
(axiom-clean): `ch6aside_conditionNumber_ge_one` (`κ(X) ≥ 1` for any submultiplicative/definite norm; `κ_F ≥ √n`),
the two-sided unitary invariance `‖UAV‖₂ = ‖A‖₂`, `‖UAV‖_F = ‖A‖_F`, and the max-norm inconsistency bound
`‖AB‖_M ≤ n‖A‖_M‖B‖_M` with all-ones equality. The block-antidiagonal `‖[[0,A],[A^*,0]]‖₂ = ‖A‖₂` is proved
conditional on one explicit standard hypothesis (block-diagonal l2 op-norm = max of block norms).

The former block-diagonal-op-norm hypothesis and the (6.1) equality-condition
residual are superseded by the 2026-07-21 theorems above. The older conditional
`ch6aside_blockAntidiag_op2_eq` is retained only as a historical reduction, not
as the source-closure endpoint. The second Lemma 6.6(a) sharpness witness
`A=ee^T, B=√n·I` remains optional in core mode.

**De-orphaning (2026-07-17, bridge B5(b)):** the `Chapter06Lemma66.lean` operator-2-norm theorems
`lemma66_a_op2_le` / `lemma66_c_op2_le` were previously ORPHANED (zero consumers repo-wide — the
`CMatrix` op2 layer of this file was never reached by the Ch.10/Ch.14 modules, which carried their
Lemma-6.6 usage through the separate real componentwise (b)/(d) chain in `MatrixAlgebra.lean`). They are
now genuinely consumed by `NumStability/Algorithms/Ch10Ch14Lemma66Op2Bridge.lean` (axiom-clean),
which applies `lemma66_c_op2_le` to prove the printed 2-norm step cited from Lemma 6.6 in BOTH chapters:
`lemma66c_absMatrix_op2_le_sqrt_card` (`‖ |B| ‖₂ ≤ √n‖B‖₂`), `lemma66c_ch10_absFactor_op2Sq_le`
(Ch.10 (10.7) key inequality `‖ |R| ‖₂² ≤ n‖R‖₂²`), and `lemma66c_ch14_residual_op2_le_sqrt_card`
(the Ch.14 §14.3.4 residual `‖G‖₂ ≤ …√n…` lift). This is a distinct realization from the
`MatrixAlgebra.lean` (b)/(d) chain referenced below — that chain remains the one used inside the existing
Ch.10/Ch.14 real-layer certificates.

## Cross-chapter role

Chapter 6 is consumed everywhere norms appear; the concrete dependency spine observed in this repo:

- **Ch7 (perturbation theory):** dual-vector (6.3) and mixed subordinate norms feed the
  Rigal–Gaches/D. J. Higham condition-number developments (`HighamChapter7.lean` cites (6.21)).
- **Ch10/Ch14 (Cholesky, GJE/inversion):** the Lemma 6.6 (b)/(d) chain is load-bearing for
  `‖|R^T||R|‖₂ ≤ n‖A‖₂`-type certificates (`HighamChapter10.lean` l.815–949,
  `Ch14GaussJordanSPDCorollary.lean` l.507–671).
- **Ch15 (condition estimation):** matrix p-norm estimation context of §6.3 ((6.12)–(6.20)) is the
  stated motivation; `Ch15CondEstimators.lean`/`Chapter15CondEst.lean` build on the p-norm value API.
- **Ch18 (matrix powers):** `Algorithms/MatrixPowersLp.lean` and `Analysis/MatrixPowersLp185Primary.lean`
  consume the `complexMatrixLpNorm` layer and norm-equivalence rows.
- **Ch20 (least squares):** §6.4 SVD packaging (unitary factors, singular-value/2-norm bridge) is the
  declared main SVD consumer.
- Theorem 6.5's "condition number = reciprocal distance to singularity" pattern recurs for the
  problem classes named in §6.5 (matrix inversion, eigenproblems); the mixed-norm κ machinery here is
  the foundation used by the Ch14/Ch21 perturbation-radius modules.
