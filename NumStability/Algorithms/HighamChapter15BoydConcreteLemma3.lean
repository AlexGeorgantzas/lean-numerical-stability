import NumStability.Algorithms.HighamChapter15BoydSourceLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydConcrete
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydConcrete
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydConcrete
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydConcrete

/-!
# HighamChapter15BoydConcreteLemma3 (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydConcreteLemma3`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

private theorem boyd_weight_exponents_cancel {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * |a| ^ (2 - p) = 1 := by
  rw [← Real.rpow_add (abs_pos.mpr ha)]
  convert Real.rpow_zero |a| using 1
  ring

private theorem hasDerivAt_abs_rpow_affine {p a b : ℝ} (hp : 1 < p) :
    HasDerivAt (fun t : ℝ => |a + t * b| ^ p)
      (p * |a| ^ (p - 2) * a * b) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hbase : HasDerivAt (fun u : ℝ => |u| ^ p)
      (p * |a| ^ (p - 2) * a) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow a hp
  convert hbase.comp 0 hline using 1 <;>
    simp only [zero_mul, add_zero, Function.comp_apply] <;> ring

/-- The displayed first formula is the actual derivative of the constrained
Lagrangian line. -/
theorem boydConstrainedLagrangianLine_hasDerivAt
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) :
    HasDerivAt (boydConstrainedLagrangianLine p A x h)
      (boydConstrainedLagrangianFirst p A x h 0) 0 := by
  have hN : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        |boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ p)
      (∑ i : Fin m, p * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A x i * boydRectActionCLM A h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_abs_rpow_affine hp
  have hD : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n, |x j + t * h j| ^ p)
      (∑ j : Fin n, p * |x j| ^ (p - 2) * x j * h j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    exact hasDerivAt_abs_rpow_affine hp
  have htot := hN.sub (hD.const_mul
    (realLpPowerSum p (boydRectActionCLM A x)))
  convert htot using 1
  unfold boydConstrainedLagrangianFirst
  simp only [zero_mul, add_zero]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem hasDerivAt_gradientFactor_affine {p a b : ℝ}
    (ha : a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => b * (|a + t * b| ^ (p - 2) * (a + t * b)))
      (b * ((p - 1) * |a| ^ (p - 2) * b)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfactor : HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u)
      ((p - 1) * |a| ^ (p - 2)) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self p a ha
  have hbase := hfactor.comp 0 hline
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hbase.const_mul b

/-- The second-variation quadratic is the actual derivative of the literal
first-derivative formula.  Together with the preceding theorem this is a
genuine second derivative witness, not a contraction hypothesis. -/
theorem boydConstrainedLagrangianFirst_hasDerivAt
    {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0) :
    HasDerivAt (boydConstrainedLagrangianFirst p A x h)
      (boydConstrainedSecondVariation p A x h) 0 := by
  have hN : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, p *
        boydRectActionCLM A h i *
          (|boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ (p - 2) *
            (boydRectActionCLM A x i + t * boydRectActionCLM A h i)))
      (∑ i : Fin m, p * (p - 1) *
        |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i * boydRectActionCLM A h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hi := (hasDerivAt_gradientFactor_affine
      (p := p) (a := boydRectActionCLM A x i)
      (b := boydRectActionCLM A h i) (hycoord i)).const_mul p
    convert hi using 1 <;> ring_nf
  have hD : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n, p *
        h j * (|x j + t * h j| ^ (p - 2) * (x j + t * h j)))
      (∑ j : Fin n, p * (p - 1) * |x j| ^ (p - 2) * h j * h j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    have hj := (hasDerivAt_gradientFactor_affine
      (p := p) (a := x j) (b := h j) (hxcoord j)).const_mul p
    convert hj using 1 <;> ring_nf
  have htot := hN.sub (hD.const_mul
    (realLpPowerSum p (boydRectActionCLM A x)))
  convert htot using 1
  unfold boydConstrainedSecondVariation boydWeightedPair
  have hout : (∑ i : Fin m, p * (p - 1) *
      |boydRectActionCLM A x i| ^ (p - 2) *
      boydRectActionCLM A h i * boydRectActionCLM A h i) =
      p * (p - 1) * ∑ i : Fin m,
        |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i * boydRectActionCLM A h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hin : (∑ j : Fin n, p * (p - 1) * |x j| ^ (p - 2) * h j * h j) =
      p * (p - 1) * ∑ j : Fin n, |x j| ^ (p - 2) * h j * h j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hout, hin]
  ring

/-- Source-facing certificate that the constrained second variation is an
actual second derivative. -/
theorem boydConstrainedSecondVariation_is_second_derivative
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0) :
    HasDerivAt (boydConstrainedLagrangianLine p A x h)
        (boydConstrainedLagrangianFirst p A x h 0) 0 ∧
      HasDerivAt (boydConstrainedLagrangianFirst p A x h)
        (boydConstrainedSecondVariation p A x h) 0 :=
  ⟨boydConstrainedLagrangianLine_hasDerivAt hp A x h,
    boydConstrainedLagrangianFirst_hasDerivAt A x h hxcoord hycoord⟩

end Ch15
end NumStability
