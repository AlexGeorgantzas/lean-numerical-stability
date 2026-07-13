# Higham Chapter 15 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), verified from `pdfinfo` title metadata and the source DOI path.
- Chapter: 15, "Condition Number Estimation".
- Printed pages read: 287-302 (body §§15.1-15.6), plus the Chapter 15 Problems.
- Source file: `References/1.9780898718027.ch15.pdf`.
- Mode: core.
- Parallel split: 3A (Chapter 15 only; Split 3B, chapters 16-19, is complete).
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, the Split 3A section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 15 rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: **PASS** (2026-07-13). Every selected primary label of Chapter 15 is closed at printed strength, with one honestly-documented probabilistic residual (the tail bound of Theorem 15.6 — see Residuals). All new modules are axiom-clean (`[propext, Classical.choice, Quot.sound]`) and adversarially verified.

## Note on prior mis-labeling

Before this pass, the mathematics for the 1-norm power method, LAPACK estimator, and tridiagonal condition numbers already lived in the repository but was **mislabeled as Chapter 14**:

- `Algorithms/CondEstimation.lean` (`oneNormPowerMethod`, `oneNormPowerMethod_lower_bound`, `lapackNormEstimator`, `lapackNormEstimator_lower_bound`) — labeled "§14.1/§14.3".
- `Algorithms/LU/TridiagonalCond.lean` (`tridiag_exact_inv_abs`, `tridiag_diagdom_cond_bound`, `ikebe_tridiag_inv_structure`) — labeled "§14.5".
- `Analysis/ConditionEstimatorLowerBound.lean` (already cross-references §15.1 eq. (15.1)).

The new modules below are **import-only**: they reuse those proofs verbatim under correct Chapter-15 labels and add only the genuinely new content (the p-norm power method / Lemma 15.2 tier, the exact `‖Ax‖₁ = γ‖x‖₁` invariant, and the LINPACK/Dixon material). No pre-existing file was edited.

## Primary-label coverage

| Label | Statement (Higham 2nd ed.) | Status | Main Lean declaration(s) | File |
|---|---|---|---|---|
| **Algorithm 15.1** (p-norm power method) | §15.2, p. 289: iterate `y=Ax`, `z=Aᵀdualp(y)`, `x=dualq(z)`; computes `γ, x` with `γ ≤ ‖A‖_p`, `‖Ax‖_p = γ‖x‖_p` | CLOSED | `Ch15.PNormPair.powerStep`, `.powerStep_gamma_le_opP`, `.powerStep_scaling` | `Algorithms/PNormPowerMethod.lean` |
| **Lemma 15.2** | §15.2, p. 290-291: (a) `zₖᵀxₖ = ‖yₖ‖_p`; (b) `‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p ≤ ‖A‖_p`; first ineq. strict off convergence | CLOSED | `Ch15.PNormPair.lemma152a`, `.lemma152b`, `Ch15.lemma152b_strict`, `.gammaSeq_mono`, `.gammaSeq_le_opP` | `Algorithms/PNormPowerMethod.lean` |
| **Algorithm 15.3** (1-norm power method) | §15.3, p. 292: computes `γ, x` with `γ ≤ ‖A‖₁` and `‖Ax‖₁ = γ‖x‖₁` | CLOSED | `Higham15.H15_Algorithm15_3_spec` (`_lower_bound` + `_norm_eq`), `_x_oneNorm_eq_one` | `Algorithms/Chapter15CondEst.lean` |
| **Algorithm 15.4** (LAPACK norm estimator) | §15.3, p. 293: computes `γ, v=Aw` with `γ ≤ ‖A‖₁`, `‖v‖₁/‖w‖₁ = γ` | CLOSED (lower bound) / PARTIAL (exact ratio) | `Higham15.H15_Algorithm15_4_lower_bound`, `_ratio_witness` (ratio `≤ γ`) | `Algorithms/Chapter15CondEst.lean` |
| **eq. (15.1)** (1-norm condition number) | §15.1, p. 306: `κ₁(A) = ‖A‖₁‖A⁻¹‖₁`; scaled estimator is a lower bound | CLOSED | `Higham15.H15_kappaOne`, `_kappaOne_eq_of_rightInverse`, `H15_Algorithm15_4_condEstimate_le_kappaOne` | `Algorithms/Chapter15CondEst.lean` |
| **Algorithm 15.5** (LINPACK estimator) | §15.5, p. 296-297: nonsingular upper-triangular `U` + weights; `Uy=d`, `dⱼ=±1`; estimate `≤ ‖U⁻¹‖` | CLOSED | `Ch15.linpackY`, `linpackD_isPlusMinusOne`, `linpackY_solves`, `linpackY_infNorm_le_infNorm_inv_nonsingular` | `Algorithms/Ch15CondEstimators.lean` |
| **Theorem 15.6** (Dixon) | §15.5, p. 298, eq. (15.7): deterministic left inequality + probabilistic right tail | CLOSED (deterministic core) / OBSTRUCTION (probabilistic tail) | `Ch15.dixon_left_inequality`, `dixon_quadForm_gram_eq`, `dixon_sqrt_quadForm_le_opNorm2`, `gram_inv_of_isInverse` | `Algorithms/Ch15CondEstimators.lean` |
| **Theorem 15.7** (tridiagonal LU inverse) | §15.6, p. 299: `|L||U|=|A| ⟹ |U⁻¹||L⁻¹|=|A⁻¹|` | CLOSED | `Ch15.H15_Theorem15_7` (← `tridiag_exact_inv_abs`) | `Algorithms/LU/TridiagonalCondCh15.lean` |
| **Theorem 15.8** (diag-dominant bound) | §15.6, p. 300: row-diag-dominant tridiagonal, `y≥0`: `‖|U⁻¹||L⁻¹|y‖∞ ≤ (2n−1)‖|A⁻¹|y‖∞` | CLOSED | `Ch15.H15_Theorem15_8` (← `tridiag_diagdom_cond_bound`) | `Algorithms/LU/TridiagonalCondCh15.lean` |
| **Theorem 15.9** (Ikebe) | §15.6, p. 300: irreducible tridiagonal `A⁻¹` has rank-1 structure `xᵢyⱼ` (i≤j), `pᵢqⱼ` (i≥j) | CLOSED | `Ch15.H15_Theorem15_9` (← `ikebe_tridiag_inv_structure`) | `Algorithms/LU/TridiagonalCondCh15.lean` |

## Honest-strength notes

- **Lemma 15.2 (abstract + concrete).** The chain (b) is *derived* in `lemma152b` from a bundle (`PNormPair`) whose seven fields are exactly Higham's printed dual-norm/Hölder/operator primitives — `dualp(v)ᵀv=‖v‖_p`, `‖dualp(v)‖_q≤1` (weaker than the printed `=1`, so the theorem is stronger), `dualq(w)ᵀw=‖w‖_q`, `‖dualq(w)‖_p=1`, Hölder `uᵀv≤‖u‖_q‖v‖_p`, and `‖Av‖_p≤‖A‖_p‖v‖_p`. The conclusion is never a hypothesis. Non-vacuity is established by two fully-discharged concrete instances: `pNormPair_two` (p=2, `opP = opNorm2 A` the Mathlib spectral operator norm; Cauchy-Schwarz as Hölder) and `pNormPair_one` (p=1, `opP = oneNorm A` the max-column-sum; `dualp=signVec`, `dualq=±e_j`). Hence `gammaSeq_two_le_opNorm2` and `gammaSeq_one_le_oneNorm` are genuine lower bounds on the true operator norms.
- **Algorithm 15.3.** The repository recursion stores `γ` from the *previous* iterate on the converged branch, so its stored `.γ` field is not in general `‖A·(returned x)‖₁`. We therefore report, exactly as the algorithm prescribes, `γ := ‖Ax‖₁` for the genuine final iterate, and prove the new invariant `H15_Algorithm15_3_x_oneNorm_eq_one` (`‖x‖₁ = 1` for the start `n⁻¹e` and every basis vertex `eⱼ`), upgrading the existing `≤1` invariant to equality. Both printed conclusions then hold at full strength with no added hypothesis.
- **Algorithm 15.4.** The lower bound `γ ≤ ‖A‖₁` and the scaled-κ₁ lower bound are closed. The printed *exact* ratio `‖v‖₁/‖w‖₁ = γ` is proved only as `≤ γ` for the alternating-vector witness `(w,v)=(b,Ab)`: the estimator returns a `max` of two arms, and an import-only wrapper cannot rewrite it to expose which arm won. Disclosed in the docstring; the primary label (the `γ ≤ ‖A‖₁` guarantee) is fully closed.
- **Algorithm 15.5.** `Uy=d` with `dⱼ=±1` is *proved* (`linpackYSteps_solves`), not assumed, via the upper-triangular row split and a frozen-coordinate stability lemma; the sign rule `linpackSign` is the book's weighted look-ahead test. The nonzero-diagonal side condition is *derived* from nonsingularity (`det U = ∏ᵢ Uᵢᵢ`), so the headline hypotheses are the printed ones. The lower bound is unconditional; `w ≥ 0` is carried for fidelity though the bound holds for all `w` (documented).
- **Theorem 15.6.** The deterministic core is closed at full strength: `(AAᵀ)⁻¹=(A⁻¹)ᵀA⁻¹`, `xᵀ(AAᵀ)⁻¹x=‖A⁻¹x‖₂²`, and the always-true left inequality `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂` (k=1 form of (15.7)). See Residuals for the probabilistic tail.
- **Theorems 15.7-15.9.** Thin correctly-labeled wrappers delegating verbatim to the base proofs. The `(2n−1)` constant of 15.8 is stated in the conclusion (not smuggled). The 15.8 row-sum hypothesis is the diagonal-dominance structural consequence itself proved unconditionally in the base module (`unit_bidiag_row_sum_bound`). The 15.9 hypotheses encode the LU factorization + bidiagonal inverse product formulas that irreducibility yields; the conclusion is the genuine printed rank-1 existential.

## Residuals / obstructions

- **Theorem 15.6 probabilistic tail (EVIDENCED_OBSTRUCTION).** The right inequality of (15.7), `‖A⁻¹‖₂ ≤ θ(xᵀ(AAᵀ)⁻ᵏx)^{1/2k}` holding with probability `≥ 1 − 0.8θ^{−k/2}n^{1/2}` for `x` uniform on the unit sphere, is not formalized. Precise missing Mathlib API: (a) the marginal/pushforward law that a squared coordinate (equivalently `(uᵀx)²`) of a uniform point on `Sⁿ⁻¹` is `Beta(1/2,(n−1)/2)` — Mathlib has `MeasureTheory.Measure.toSphere` and `ProbabilityTheory.betaMeasure` separately but no lemma linking them; (b) a Beta CDF small-argument tail bound `∫₀^ε betaPDF(1/2,(n−1)/2) ≤ c√ε√n` — `Beta.lean` provides only the pdf, `lintegral_betaPDF_eq_one`, and measurability. The union bound over singular directions (`measure_iUnion_le`) exists but is moot without (a),(b).
- **Lemma 15.2 general real p (documented residual).** The abstract `PNormPair` tier proves Lemma 15.2 for *any* `p` once the dual-norm data is supplied; the two endpoint instances Higham singles out (p=2 → power method on `AᵀA`; p=1 → LAPACK basis) are fully built. A third instance for general `p ∈ (1,∞)` is not built because Mathlib lacks a packaged mixed-`p` vector dual norm with its induced operator `p`-norm and attained `dualp`. This residual is only the general-`p` `dualp` construction, not any part of Lemma 15.2's logic.

## Appendix A / Problems (wave 2)

Split 3A owns Appendix A solutions 15.1, 15.4, 15.7 (per `split_primary_contracts.md`). These are optional in core mode; they were selected and formalized as a second wave because they are useful precise mathematical targets.

| Problem | Statement | Status | Main Lean declaration(s) | File |
|---|---|---|---|---|
| **15.4** | `PA=LU` partial pivoting: `‖A⁻¹‖∞/2ⁿ⁻¹ ≤ ‖U⁻¹‖∞ ≤ n‖A⁻¹‖∞` | CLOSED | `Ch15.ch15p4_infNorm_Uinv_two_sided` (+ `ch15p4_infNorm_Linv_le` `‖L⁻¹‖∞ ≤ 2ⁿ⁻¹`, `ch15p4_infNorm_L_le` `‖L‖∞ ≤ n`) | `Algorithms/LU/Ch15Problem4.lean` |
| **15.1** | rewrite `‖|A||A⁻¹||A|‖∞` for estimation by the LAPACK estimator | CLOSED | `Ch15.tripleProduct_rewrite`, `tripleProduct_infNorm_eq_reducedMatrix`, `lapackEstimator_le_tripleProduct` (honest lower bound) | `Algorithms/CondEstimationTripleProduct.lean` |
| **15.7** | `3n−2`-parameter representation of the irreducible-tridiagonal inverse (symmetrize) | SUBSTANTIVE_PARTIAL | `Ch15.ikebe_symmetrized_representation(_constructive)`, `inv_scaling_relation`, `symmetrizerDiag_isSymmetric` | `Algorithms/LU/Ikebe15Symmetrized.lean` |

Honest-strength notes (wave 2):
- **15.4** — full two-sided bound at printed strength; the constants `2ⁿ⁻¹` and `n` are derived into the conclusion (`‖L⁻¹‖∞ ≤ 2ⁿ⁻¹` proved from scratch by a downward row-sum induction; the repo previously had only the upper-triangular column-sum form). The partial-pivoting fact `|Lᵢⱼ| ≤ 1` is the sole `≤1` hypothesis (the definition of partial pivoting). Uses the repo's `PermutedLUFactSpec` and `IsInverse`.
- **15.1** — exact, unconditional reduction identity `‖|A||A⁻¹||A|‖∞ = ‖C‖∞` with `C = |A|·|A⁻¹ diag(g)|` a genuine nonnegative matrix (`g = |A|·𝟙`), folding the two outer `|A|` factors into a nonnegative weight and removing the middle `|A⁻¹|` via `cond_norm_identity`. The estimator step is stated honestly as a lower bound (`lapackNormEstimator` on `Cᵀ ≤ ‖|A||A⁻¹||A|‖∞`), matching that Algorithm 15.4 is itself only a lower-bound estimator.
- **15.7** — the symmetrization is fully proved: an explicit diagonal `D = symmetrizerDiag A` (product of `√(aₘ,ₘ₊₁/aₘ₊₁,ₘ)`) makes `DAD⁻¹` symmetric, `DA⁻¹D⁻¹` is then symmetric, giving the collapse identity `dᵢ²(A⁻¹)ᵢⱼ = dⱼ²(A⁻¹)ⱼᵢ` and the representation `(A⁻¹)ᵢⱼ = (dⱼ/dᵢ)·u₍ₘᵢₙ₎·v₍ₘₐₓ₎` with only `u=Dx`, `v=y/D` and `D` (the Ikebe lower factors `p,q` eliminated). **Residual:** the literal `3n−2` free-parameter *count* is documented (not formalized as a `Fintype.card`/dimension theorem) — formalizing it needs the scaling-quotient dimension argument. Hypothesis note: the symmetrizer uses `PosRatio` (adjacent super/sub-diagonal ratios `> 0`, i.e. same sign — the condition for a *real* symmetrizer), which is stronger than bare irreducibility; this is disclosed in the module, not disguised. Hence recorded honestly as SUBSTANTIVE_PARTIAL, not full closure.

Remaining Chapter 15 Problems: 15.2 (starting-vector heuristic — open-ended "develop an algorithm"), 15.3 and 15.5 (fixed-matrix numerical experiments), 15.6 (O(n) Ikebe algorithm — implementation), 15.8 (explicitly a research problem). Correctly not selected (empirical / open / not Split-3A-owned appendix targets).

## Verification

- `lake build LeanFpAnalysis.FP.Algorithms.PNormPowerMethod LeanFpAnalysis.FP.Algorithms.Chapter15CondEst LeanFpAnalysis.FP.Algorithms.Ch15CondEstimators LeanFpAnalysis.FP.Algorithms.LU.TridiagonalCondCh15` — success.
- Full `lake build` after wiring the four modules into `LeanFpAnalysis/FP/Algorithms.lean` — success.
- `#print axioms` on every headline declaration — `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`native_decide`/`set_option` in any of the four new files.
- Adversarial verification of all four modules: ACCEPT (T1, T4), ACCEPT_WITH_NOTES (T2, T3, notes as documented above).
