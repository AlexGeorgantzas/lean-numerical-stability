import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed
import NumStability.Algorithms.MatrixPowersPseudospectralCriterion
import NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.LowerBounds

/-!
# Analysis.PseudospectralResolvent

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

-- Analysis/PseudospectralResolvent.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, §18.2 — the analytic *resolvent-norm* foundation underneath
-- eq (18.8)  ‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}  and the resolvent-norm
-- characterisation of the ε-pseudospectrum.
--
-- CONTEXT.  `Algorithms/MatrixPowersPseudospectralCriterion.lean` records eq
-- (18.8) as DEFERRED, noting that a proof needs three ingredients absent from
-- Mathlib v4.29:
--   (1) a resolvent-norm bound  ‖(zI−A)⁻¹‖ ≥ ε⁻¹  characterising the
--       ε-pseudospectrum boundary;
--   (2) the Dunford / holomorphic-functional-calculus contour representation
--       Aᵏ = (1/2πi) ∮_Γ zᵏ (zI−A)⁻¹ dz;
--   (3) a contour ML-estimate.
--
-- This module supplies ingredient (1) — the genuinely provable analytic
-- building block — UNCONDITIONALLY, at maximal honest strength, over any
-- complete normed algebra (so it specialises to the matrix 2-norm algebra
-- `CStarMatrix (Fin n) (Fin n) ℂ` that instantiates Higham's ‖·‖₂, and to any
-- Banach algebra).  It does NOT attempt ingredients (2)/(3): Mathlib has the
-- scalar/`E`-valued Cauchy integral (`circleIntegral_sub_center_inv_smul_…`)
-- but NO matrix holomorphic functional calculus and NO
-- resolvent = Cauchy-integral-of-powers identity, so full (18.8) remains out
-- of reach by assembly.  The precise obstruction is documented at the foot of
-- the file.
--
-- WHAT IS UNCONDITIONAL HERE (ingredient (1), no extra hypotheses):
--   * `resolvent_factor` — the exact factorisation
--       ↑ₐw − a = (↑ₐz − a)·(1 − (z−w)•R(z))
--     that drives every lower bound below.
--   * `spectrum_one_le_dist_mul_norm_resolvent` — the headline resolvent-norm
--       lower bound  1 ≤ ‖z − w‖ · ‖R(z)‖  for every spectral point `w` and
--       every resolvent point `z`.
--   * `spectrum_one_div_dist_le_norm_resolvent` — the ‖R(z)‖ ≥ 1/|z−w| form.
--   * `spectrum_one_le_dist_mul_norm_resolvent'` — the `dist`-flavoured form.
--   * `dist_ge_one_div_norm_resolvent` — dist(z, w) ≥ 1/‖R(z)‖, i.e. the
--       spectrum keeps its distance from any resolvent point, quantitatively;
--       this is exactly the statement "the ε-pseudospectrum
--       {z : ‖R(z)‖ ≥ ε⁻¹} is a neighbourhood of the spectrum" in local form.
--
-- All statements are over `[NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]`
-- and hold verbatim for Higham's ‖·‖₂ on complex matrices.





namespace NumStability

open scoped BigOperators

section ResolventNorm

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A]
  [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A






















































































end ResolventNorm

-- ============================================================
-- §18.2  EVIDENCED OBSTRUCTION to full eq (18.8)
-- ============================================================
--
-- With ingredient (1) above in hand UNCONDITIONALLY, the remaining gap to
-- eq (18.8)  ‖Aᵏ‖₂ ≤ ε⁻¹ · ρ_ε(A)^{k+1}  is ingredients (2)+(3): the
-- Banach-algebra holomorphic functional calculus, specifically the identity
--
--     Aᵏ = (1/2πi) ∮_Γ zᵏ · (zI − A)⁻¹ dz     (Γ a contour enclosing σ(A)),
--
-- together with the contour ML-estimate that turns it into
-- ‖Aᵏ‖ ≤ (len Γ / 2π)·(max_Γ ‖zᵏ‖)·(max_Γ ‖R(z)‖).  Taking Γ the boundary of
-- the ε-pseudospectrum gives max_Γ ‖R(z)‖ = ε⁻¹ (the resolvent-norm
-- characterisation, whose ≥ half is `spectrum_one_le_dist_mul_norm_resolvent`)
-- and len Γ / 2π · max_Γ ‖zᵏ‖ ≤ ρ_ε(A)^{k+1}, yielding (18.8).
--
-- CONCRETE MATHLIB GAP (searched, v4.29):
--   • Mathlib HAS the `E`-valued Cauchy integral
--     `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`
--     and `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_…` in
--     `Mathlib/Analysis/Complex/CauchyIntegral.lean`, i.e. the Cauchy formula
--     for BANACH-SPACE-VALUED analytic functions.
--   • Mathlib LACKS: (a) that `z ↦ resolvent a z` is analytic as an
--     `A`-valued function on the resolvent set (only `resolvent_isBigO_inv`,
--     `resolvent_tendsto_cobounded`, and the scalar geometric series
--     `hasFPowerSeriesOnBall_inverse_one_sub_smul` exist in
--     `Mathlib/Analysis/Normed/Algebra/Spectrum.lean`); and (b) the
--     functional-calculus residue identity `aᵏ = (2πi)⁻¹ ∮ zᵏ R(z) dz`.
--     There is NO holomorphic functional calculus in Mathlib (only the
--     CONTINUOUS functional calculus for C⋆-algebras, in
--     `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/`, which
--     does not provide a Cauchy-contour power representation and does not
--     apply to non-normal matrices).
--   • Grep for `circleIntegral.*resolvent` / holomorphic functional calculus
--     over all of Mathlib returns nothing; the only "Dunford" hit is the
--     purely-algebraic `LinearAlgebra/JordanChevalley.lean`, unrelated to the
--     contour integral.
--
-- Bridging (a)+(b) is a multi-file research development (analyticity of the
-- resolvent, Bochner integrability of the `A`-valued integrand, and the
-- residue identity), not an assembly over existing lemmas.  Hence full (18.8)
-- is NOT delivered here; only its unconditional resolvent-norm foundation is.

-- Axiom check (performed, lines then removed): each headline declaration
-- (`resolvent_factor`, `spectrum_one_le_dist_mul_norm_resolvent`,
-- `spectrum_one_div_dist_le_norm_resolvent`,
-- `spectrum_one_le_dist_mul_norm_resolvent'`,
-- `dist_ge_one_div_norm_resolvent`) depends only on the standard trio
-- `[propext, Classical.choice, Quot.sound]` — no `sorry`, `admit`, custom
-- axiom, `unsafe`, `opaque`, `native_decide`, or `set_option` escape hatch.

end NumStability
