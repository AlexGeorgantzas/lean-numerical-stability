import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProductMeasure
import LeanFpAnalysis.HDP.Probability.Concentration.SubExponential

/-!
# Bernstein Inequality Infrastructure

Reusable Chernoff/MGF spine for HDP Chapter 2, Section 2.8.  The public
Bernstein inequalities will connect the `ψ₁` norm to the local signed MGF
condition from Proposition 2.7.1(e); this file isolates the finite-sum
Chernoff step so that later optimized statements can reuse it directly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace LeanFpAnalysis.HDP

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section MGFSpine

variable {ι : Type*} [Fintype ι]

/-- Variance proxy appearing in Bernstein's inequality for local
sub-exponential MGF bounds. -/
def subExponentialVarianceProxySum (K : ι → ℝ) : ℝ :=
  ∑ i, K i ^ 2

@[simp]
lemma subExponentialVarianceProxySum_def (K : ι → ℝ) :
    subExponentialVarianceProxySum K = ∑ i, K i ^ 2 := rfl

/-- The variance proxy is nonnegative. -/
lemma subExponentialVarianceProxySum_nonneg (K : ι → ℝ) :
    0 ≤ subExponentialVarianceProxySum K := by
  unfold subExponentialVarianceProxySum
  exact Finset.sum_nonneg fun i _ => sq_nonneg (K i)

/-- Deterministic finite maximum used for the `maxᵢ ‖Xᵢ‖ψ₁` term in
Theorems 2.8.1 and 2.8.2. -/
def finiteMaxValue [Nonempty ι] (K : ι → ℝ) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty K

lemma le_finiteMaxValue [Nonempty ι] (K : ι → ℝ) (i : ι) :
    K i ≤ finiteMaxValue K := by
  classical
  exact
    Finset.le_sup'
      (s := (Finset.univ : Finset ι)) (f := K) (Finset.mem_univ i)

lemma finiteMaxValue_nonneg [Nonempty ι] {K : ι → ℝ}
    (hK : ∀ i, 0 ≤ K i) :
    0 ≤ finiteMaxValue K := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  exact (hK i₀).trans (le_finiteMaxValue K i₀)

/-- Finite `ℓ∞` norm of a deterministic coefficient vector. -/
def coeffLInfNorm [Nonempty ι] (a : ι → ℝ) : ℝ :=
  finiteMaxValue (fun i => |a i|)

lemma abs_coeff_le_linf [Nonempty ι] (a : ι → ℝ) (i : ι) :
    |a i| ≤ coeffLInfNorm a := by
  classical
  simpa [coeffLInfNorm] using
    le_finiteMaxValue (fun i => |a i|) i

lemma coeffLInfNorm_nonneg [Nonempty ι] (a : ι → ℝ) :
    0 ≤ coeffLInfNorm a :=
  finiteMaxValue_nonneg (fun i => abs_nonneg (a i))

lemma two_mul_three_pow_le_factorial_add_two (n : ℕ) :
    2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hthree : 3 ≤ n + 3 := by omega
      have hmul : 3 * (2 * 3 ^ n) ≤ (n + 3) * (n + 2).factorial :=
        Nat.mul_le_mul hthree ih
      have hleft : 3 * (2 * 3 ^ n) = 2 * 3 ^ (n + 1) := by ring
      have hright : (n + 3).factorial = (n + 3) * (n + 2).factorial := by
        rw [show n + 3 = (n + 2) + 1 by omega, Nat.factorial_succ]
      simpa [show n + 1 + 2 = n + 3 by omega, hleft, hright] using hmul

lemma exp_tail_term_le_geometric {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (n + 2) / (n + 2).factorial ≤ (x ^ 2 / 2) * (x / 3) ^ n := by
  have hfacR : (2 * 3 ^ n : ℝ) ≤ ((n + 2).factorial : ℝ) := by
    exact_mod_cast two_mul_three_pow_le_factorial_add_two n
  have hden_pos : 0 < (2 * 3 ^ n : ℝ) := by positivity
  have hinv : (1 : ℝ) / ((n + 2).factorial : ℝ) ≤ 1 / (2 * 3 ^ n : ℝ) :=
    one_div_le_one_div_of_le hden_pos hfacR
  calc
    x ^ (n + 2) / ((n + 2).factorial : ℝ)
        = x ^ (n + 2) * (1 / ((n + 2).factorial : ℝ)) := by ring
    _ ≤ x ^ (n + 2) * (1 / (2 * 3 ^ n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hx _)
    _ = (x ^ 2 / 2) * (x / 3) ^ n := by
      rw [div_pow]
      field_simp [show (2 : ℝ) ≠ 0 by norm_num, show (3 : ℝ) ≠ 0 by norm_num,
        pow_ne_zero n (show (3 : ℝ) ≠ 0 by norm_num)]
      ring_nf

/-- Scalar Bernstein exponential remainder for nonnegative arguments. -/
lemma real_exp_le_quadratic_geometric {x : ℝ} (hx0 : 0 ≤ x) (hx3 : x < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
  let f : ℕ → ℝ := fun n => x ^ n / (n.factorial : ℝ)
  have hf : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial x
  have htail : Summable fun n => f (n + 2) :=
    (summable_nat_add_iff 2).2 hf
  have hsplit :
      (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range 2, f n) + ∑' n : ℕ, f (n + 2) :=
    (hf.sum_add_tsum_nat_add 2).symm
  have hnorm : ‖x / 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hx0 (by norm_num : (0 : ℝ) ≤ 3))]
    nlinarith
  have hgeom_summable : Summable fun n : ℕ => (x ^ 2 / 2) * (x / 3) ^ n :=
    (summable_geometric_of_norm_lt_one hnorm).mul_left (x ^ 2 / 2)
  have htail_le :
      (∑' n : ℕ, f (n + 2)) ≤ ∑' n : ℕ, (x ^ 2 / 2) * (x / 3) ^ n := by
    refine Summable.tsum_le_tsum ?_ htail hgeom_summable
    intro n
    simpa [f, add_comm, add_left_comm, add_assoc] using
      exp_tail_term_le_geometric hx0 n
  have hgeom_sum :
      (∑' n : ℕ, (x ^ 2 / 2) * (x / 3) ^ n) =
        (x ^ 2 / 2) * (1 - x / 3)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
  have hfinite : (∑ n ∈ Finset.range 2, f n) = 1 + x := by
    simp [f, Finset.sum_range_succ]
  calc
    Real.exp x = ∑' n : ℕ, f n := by
      dsimp [f]
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = (∑ n ∈ Finset.range 2, f n) + ∑' n : ℕ, f (n + 2) := hsplit
    _ ≤ (1 + x) + ∑' n : ℕ, (x ^ 2 / 2) * (x / 3) ^ n := by
      rw [hfinite]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right htail_le (1 + x)
    _ = (1 + x) + (x ^ 2 / 2) * (1 - x / 3)⁻¹ := by
      rw [hgeom_sum]
    _ = 1 + x + x ^ 2 / (2 * (1 - x / 3)) := by
      field_simp [show (2 : ℝ) ≠ 0 by norm_num, show 1 - x / 3 ≠ 0 by nlinarith]

lemma inv_one_add_add_sq_half_le_quadratic_neg {y : ℝ} (_hy0 : 0 ≤ y) :
    1 / (1 + y + y ^ 2 / 2) ≤ 1 - y + y ^ 2 / 2 := by
  have hden : 0 < 1 + y + y ^ 2 / 2 := by nlinarith [sq_nonneg y]
  field_simp [hden.ne']
  nlinarith [sq_nonneg (y ^ 2)]

lemma quadratic_neg_le_bernstein_neg {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    1 - y + y ^ 2 / 2 ≤ 1 - y + y ^ 2 / (2 * (1 - y / 3)) := by
  have hden : 0 < 1 - y / 3 := by nlinarith
  have hden_le_one : 1 - y / 3 ≤ 1 := by nlinarith
  have hinv : 1 ≤ (1 - y / 3)⁻¹ := (one_le_inv₀ hden).2 hden_le_one
  have hmul : y ^ 2 / 2 ≤ (y ^ 2 / 2) * (1 - y / 3)⁻¹ := by
    have hnon : 0 ≤ y ^ 2 / 2 := by positivity
    simpa using mul_le_mul_of_nonneg_left hinv hnon
  calc
    1 - y + y ^ 2 / 2 ≤ 1 - y + (y ^ 2 / 2) * (1 - y / 3)⁻¹ := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul (1 - y)
    _ = 1 - y + y ^ 2 / (2 * (1 - y / 3)) := by
      field_simp [show (2 : ℝ) ≠ 0 by norm_num, hden.ne']

/-- Scalar Bernstein exponential remainder for negative arguments. -/
lemma real_exp_neg_le_bernstein_quadratic {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / (2 * (1 - y / 3)) := by
  have hden : 0 < 1 + y + y ^ 2 / 2 := by nlinarith [sq_nonneg y]
  have hquad_exp : 1 + y + y ^ 2 / 2 ≤ Real.exp y :=
    Real.quadratic_le_exp_of_nonneg hy0
  have hinv : (Real.exp y)⁻¹ ≤ (1 + y + y ^ 2 / 2)⁻¹ :=
    inv_anti₀ hden hquad_exp
  have hfirst : Real.exp (-y) ≤ 1 / (1 + y + y ^ 2 / 2) := by
    rw [Real.exp_neg]
    simpa [one_div] using hinv
  exact hfirst.trans ((inv_one_add_add_sq_half_le_quadratic_neg hy0).trans
    (quadratic_neg_le_bernstein_neg hy0 hy3))

/-- The scalar inequality behind Exercise 2.8.5:
`exp x ≤ 1 + x + x² / (2(1 - |x|/3))` for `|x| < 3`. -/
lemma real_exp_le_bernstein_quadratic {x : ℝ} (hx : |x| < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - |x| / 3)) := by
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using real_exp_le_quadratic_geometric hx0 (by simpa [abs_of_nonneg hx0] using hx)
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have hy0 : 0 ≤ -x := by linarith
    have hy3 : -x < 3 := by simpa [abs_of_neg hxneg] using hx
    simpa [abs_of_neg hxneg, sub_eq_add_neg, neg_sq] using
      real_exp_neg_le_bernstein_quadratic hy0 hy3

/-- Second-order upper Taylor bound for the negative exponential. -/
lemma real_exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let g : ℝ → ℝ := fun y => 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hg_deriv :
      ∀ y : ℝ, HasDerivAt g (-1 + y + Real.exp (-y)) y := by
    intro y
    dsimp [g]
    convert
      (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        (((hasDerivAt_id y).pow 2).div_const 2)).sub
        ((Real.hasDerivAt_exp (-y)).comp y ((hasDerivAt_id y).neg)) using 1
    simp [id]
  have hg_nonneg :
      (0 : ℝ → ℝ) ≤ fun y : ℝ => -1 + y + Real.exp (-y) := by
    intro y
    change 0 ≤ -1 + y + Real.exp (-y)
    have h := Real.add_one_le_exp (-y)
    linarith
  have hg_mono : Monotone g :=
    monotone_of_hasDerivAt_nonneg hg_deriv hg_nonneg
  have h0u : g 0 ≤ g u := hg_mono hu
  have hg0 : g 0 = 0 := by simp [g]
  have hgu : 0 ≤ g u := by simpa [hg0] using h0u
  dsimp [g] at hgu
  nlinarith

/-- Bennett's scalar exponential comparison on the nonnegative part. -/
lemma real_exp_le_bennett_remainder_nonneg {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : 0 < v) :
    Real.exp u ≤ 1 + u + (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by
  let fu : ℕ → ℝ := fun n => u ^ n / (n.factorial : ℝ)
  let fv : ℕ → ℝ := fun n => v ^ n / (n.factorial : ℝ)
  let c : ℝ := u ^ 2 / v ^ 2
  have hfu : Summable fu := by
    simpa [fu] using Real.summable_pow_div_factorial u
  have hfv : Summable fv := by
    simpa [fv] using Real.summable_pow_div_factorial v
  have htailu : Summable fun n : ℕ => fu (n + 2) :=
    (summable_nat_add_iff 2).2 hfu
  have htailv : Summable fun n : ℕ => fv (n + 2) :=
    (summable_nat_add_iff 2).2 hfv
  have hsplitu :
      (∑' n : ℕ, fu n) =
        (∑ n ∈ Finset.range 2, fu n) + ∑' n : ℕ, fu (n + 2) :=
    (hfu.sum_add_tsum_nat_add 2).symm
  have hsplitv :
      (∑' n : ℕ, fv n) =
        (∑ n ∈ Finset.range 2, fv n) + ∑' n : ℕ, fv (n + 2) :=
    (hfv.sum_add_tsum_nat_add 2).symm
  have hfiniteu : (∑ n ∈ Finset.range 2, fu n) = 1 + u := by
    simp [fu, Finset.sum_range_succ]
  have hfinitev : (∑ n ∈ Finset.range 2, fv n) = 1 + v := by
    simp [fv, Finset.sum_range_succ]
  have hexpu : Real.exp u = ∑' n : ℕ, fu n := by
    dsimp [fu]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hexpv : Real.exp v = ∑' n : ℕ, fv n := by
    dsimp [fv]
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hterm :
      ∀ n : ℕ, fu (n + 2) ≤ c * fv (n + 2) := by
    intro n
    have hpow_u :
        u ^ (n + 2) = u ^ 2 * u ^ n := by
      rw [show n + 2 = 2 + n by omega, pow_add]
    have hpow_v :
        v ^ (n + 2) = v ^ 2 * v ^ n := by
      rw [show n + 2 = 2 + n by omega, pow_add]
    have hpow_le : u ^ (n + 2) ≤ c * v ^ (n + 2) := by
      calc
        u ^ (n + 2) = u ^ 2 * u ^ n := hpow_u
        _ ≤ u ^ 2 * v ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hu huv n) (sq_nonneg u)
        _ = c * v ^ (n + 2) := by
          dsimp [c]
          rw [hpow_v]
          field_simp [hv.ne']
    have hfac_pos : 0 < ((n + 2).factorial : ℝ) := by positivity
    dsimp [fu, fv]
    calc
      u ^ (n + 2) / ((n + 2).factorial : ℝ)
          ≤ (c * v ^ (n + 2)) / ((n + 2).factorial : ℝ) :=
        div_le_div_of_nonneg_right hpow_le hfac_pos.le
      _ = c * (v ^ (n + 2) / ((n + 2).factorial : ℝ)) := by ring
  have htail_scaled :
      (∑' n : ℕ, fu (n + 2))
        ≤ c * ∑' n : ℕ, fv (n + 2) := by
    calc
      (∑' n : ℕ, fu (n + 2))
          ≤ ∑' n : ℕ, c * fv (n + 2) := by
        exact Summable.tsum_le_tsum hterm htailu (htailv.mul_left c)
      _ = c * ∑' n : ℕ, fv (n + 2) := by
        rw [tsum_mul_left]
  have htailv_eq :
      (∑' n : ℕ, fv (n + 2)) = Real.exp v - (1 + v) := by
    have hsum :
        Real.exp v = (1 + v) + ∑' n : ℕ, fv (n + 2) := by
      calc
        Real.exp v = ∑' n : ℕ, fv n := hexpv
        _ = (∑ n ∈ Finset.range 2, fv n) + ∑' n : ℕ, fv (n + 2) := hsplitv
        _ = (1 + v) + ∑' n : ℕ, fv (n + 2) := by rw [hfinitev]
    linarith
  calc
    Real.exp u = ∑' n : ℕ, fu n := hexpu
    _ = (∑ n ∈ Finset.range 2, fu n) + ∑' n : ℕ, fu (n + 2) := hsplitu
    _ = (1 + u) + ∑' n : ℕ, fu (n + 2) := by rw [hfiniteu]
    _ ≤ (1 + u) + c * ∑' n : ℕ, fv (n + 2) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left htail_scaled (1 + u)
    _ = 1 + u + (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by
      dsimp [c]
      rw [htailv_eq]
      ring

/-- Bennett's pointwise exponential comparison:
`eᵘ ≤ 1 + u + (u²/v²)(eᵛ - 1 - v)` for `v > 0` and `u ≤ v`. -/
lemma real_exp_le_bennett_remainder {u v : ℝ}
    (hv : 0 < v) (huv : u ≤ v) :
    Real.exp u ≤ 1 + u + (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by
  by_cases hu_nonneg : 0 ≤ u
  · exact real_exp_le_bennett_remainder_nonneg hu_nonneg huv hv
  · have hneg := real_exp_neg_le_quadratic (u := -u) (by linarith)
    have hvquad : 1 + v + v ^ 2 / 2 ≤ Real.exp v :=
      Real.quadratic_le_exp_of_nonneg hv.le
    have hcoef :
        (1 / 2 : ℝ) ≤ (Real.exp v - 1 - v) / v ^ 2 := by
      have hv2pos : 0 < v ^ 2 := sq_pos_of_pos hv
      rw [le_div_iff₀ hv2pos]
      nlinarith
    have hterm :
        u ^ 2 / 2 ≤ (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by
      calc
        u ^ 2 / 2 = u ^ 2 * (1 / 2) := by ring
        _ ≤ u ^ 2 * ((Real.exp v - 1 - v) / v ^ 2) :=
          mul_le_mul_of_nonneg_left hcoef (sq_nonneg u)
        _ = (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by ring
    calc
      Real.exp u = Real.exp (-(-u)) := by ring_nf
      _ ≤ 1 - (-u) + (-u) ^ 2 / 2 := hneg
      _ = 1 + u + u ^ 2 / 2 := by ring
      _ ≤ 1 + u + (u ^ 2 / v ^ 2) * (Real.exp v - 1 - v) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hterm (1 + u)

/-- The scalar factor `g(λ)` in HDP Exercise 2.8.5. -/
def boundedBernsteinMGFScale (K θ : ℝ) : ℝ :=
  θ ^ 2 / (2 * (1 - |θ| * K / 3))

lemma boundedBernsteinMGFScale_nonneg {K θ : ℝ} (_hK : 0 ≤ K)
    (hθ : |θ| * K < 3) :
    0 ≤ boundedBernsteinMGFScale K θ := by
  unfold boundedBernsteinMGFScale
  have hden : 0 < 2 * (1 - |θ| * K / 3) := by nlinarith
  positivity

lemma exp_mul_le_one_add_mul_add_boundedBernstein {K θ x : ℝ}
    (hK : 0 < K) (hx : |x| ≤ K) (hθ : |θ| < 3 / K) :
    Real.exp (θ * x) ≤ 1 + θ * x + boundedBernsteinMGFScale K θ * x ^ 2 := by
  have habsθK_lt : |θ| * K < 3 := by
    rw [lt_div_iff₀ hK] at hθ
    simpa [mul_comm] using hθ
  have habsθx_le : |θ * x| ≤ |θ| * K := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg θ)
  have habsθx_lt : |θ * x| < 3 := habsθx_le.trans_lt habsθK_lt
  have hscalar := real_exp_le_bernstein_quadratic (x := θ * x) habsθx_lt
  have hden_small : 0 < 2 * (1 - |θ| * K / 3) := by nlinarith
  have hden_le : 2 * (1 - |θ| * K / 3) ≤ 2 * (1 - |θ * x| / 3) := by
    nlinarith
  have hinv :
      1 / (2 * (1 - |θ * x| / 3)) ≤
        1 / (2 * (1 - |θ| * K / 3)) :=
    one_div_le_one_div_of_le hden_small hden_le
  have hterm :
      (θ * x) ^ 2 / (2 * (1 - |θ * x| / 3)) ≤
        boundedBernsteinMGFScale K θ * x ^ 2 := by
    calc
      (θ * x) ^ 2 / (2 * (1 - |θ * x| / 3))
          = (θ * x) ^ 2 * (1 / (2 * (1 - |θ * x| / 3))) := by ring
      _ ≤ (θ * x) ^ 2 * (1 / (2 * (1 - |θ| * K / 3))) := by
        exact mul_le_mul_of_nonneg_left hinv (sq_nonneg (θ * x))
      _ = boundedBernsteinMGFScale K θ * x ^ 2 := by
        unfold boundedBernsteinMGFScale
        ring
  exact hscalar.trans (by nlinarith)

/-- HDP Exercise 2.8.5.  If `X` is centered and `|X| ≤ K` a.s., then its
MGF is controlled by the Bernstein factor
`g(λ) = λ² / (2 * (1 - |λ| K / 3))` for `|λ| < 3 / K`. -/
theorem bounded_bernstein_mgf_bound
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K θ : ℝ}
    (hK : 0 < K)
    (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hθ : |θ| < 3 / K) :
    mgf X μ θ ≤
      Real.exp (boundedBernsteinMGFScale K θ * ∫ ω, X ω ^ 2 ∂μ) := by
  let g : ℝ := boundedBernsteinMGFScale K θ
  have habsθK_lt : |θ| * K < 3 := by
    rw [lt_div_iff₀ hK] at hθ
    simpa [mul_comm] using hθ
  have hg_nonneg : 0 ≤ g := by
    dsimp [g]
    exact boundedBernsteinMGFScale_nonneg hK.le habsθK_lt
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-K) K := by
    filter_upwards [hbound] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have hexp_int : Integrable (fun ω => Real.exp (θ * X ω)) μ :=
    ProbabilityTheory.integrable_exp_mul_of_mem_Icc hXm hIcc
  have hX_int : Integrable X μ := by
    refine Integrable.of_bound hXm.aestronglyMeasurable K ?_
    filter_upwards [hbound] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hXsq_aesm : AEStronglyMeasurable (fun ω => X ω ^ 2) μ := by
    simpa [pow_two] using (hXm.mul hXm).aestronglyMeasurable
  have hXsq_int : Integrable (fun ω => X ω ^ 2) μ := by
    refine Integrable.of_bound hXsq_aesm (K ^ 2) ?_
    filter_upwards [hbound] with ω hω
    have hsq : |X ω| ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg (X ω)) hω 2
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω)), sq_abs] using hsq
  let G : Ω → ℝ := fun ω => 1 + θ * X ω + g * X ω ^ 2
  have hG_int : Integrable G μ := by
    have hconst : Integrable (fun _ω : Ω => (1 : ℝ)) μ := integrable_const 1
    have hlin : Integrable (fun ω => θ * X ω) μ := hX_int.const_mul θ
    have hquad : Integrable (fun ω => g * X ω ^ 2) μ := hXsq_int.const_mul g
    simpa [G, add_assoc] using (hconst.add hlin).add hquad
  have hpoint : (fun ω => Real.exp (θ * X ω)) ≤ᶠ[ae μ] G := by
    filter_upwards [hbound] with ω hω
    simpa [G, g] using
      exp_mul_le_one_add_mul_add_boundedBernstein hK hω hθ
  have hintegral_le : ∫ ω, Real.exp (θ * X ω) ∂μ ≤ ∫ ω, G ω ∂μ :=
    integral_mono_ae hexp_int hG_int hpoint
  have hG_integral :
      ∫ ω, G ω ∂μ = 1 + θ * (∫ ω, X ω ∂μ) + g * (∫ ω, X ω ^ 2 ∂μ) := by
    calc
      ∫ ω, G ω ∂μ
          = ∫ ω, (1 : ℝ) + θ * X ω + g * X ω ^ 2 ∂μ := rfl
      _ = ∫ ω, ((1 : ℝ) + θ * X ω) ∂μ + ∫ ω, g * X ω ^ 2 ∂μ := by
        exact integral_add (integrable_const 1 |>.add (hX_int.const_mul θ)) (hXsq_int.const_mul g)
      _ = (∫ _ω : Ω, (1 : ℝ) ∂μ + ∫ ω, θ * X ω ∂μ) +
            ∫ ω, g * X ω ^ 2 ∂μ := by
        rw [integral_add (integrable_const 1) (hX_int.const_mul θ)]
      _ = 1 + θ * (∫ ω, X ω ∂μ) + g * (∫ ω, X ω ^ 2 ∂μ) := by
        rw [integral_const, integral_const_mul, integral_const_mul]
        simp
  have hsecond_nonneg : 0 ≤ ∫ ω, X ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (X ω)
  have hlin_to_exp :
      1 + g * (∫ ω, X ω ^ 2 ∂μ) ≤
        Real.exp (g * ∫ ω, X ω ^ 2 ∂μ) := by
    simpa [add_comm] using
      Real.add_one_le_exp (g * ∫ ω, X ω ^ 2 ∂μ)
  calc
    mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
    _ ≤ ∫ ω, G ω ∂μ := hintegral_le
    _ = 1 + θ * (∫ ω, X ω ∂μ) + g * (∫ ω, X ω ^ 2 ∂μ) := hG_integral
    _ = 1 + g * (∫ ω, X ω ^ 2 ∂μ) := by simp [hmean]
    _ ≤ Real.exp (g * ∫ ω, X ω ^ 2 ∂μ) := hlin_to_exp

/-- Variance sum appearing in the bounded Bernstein inequality. -/
def boundedBernsteinVarianceSum (X : ι → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∑ i, ∫ ω, X i ω ^ 2 ∂μ

lemma boundedBernsteinVarianceSum_nonneg
    {X : ι → Ω → ℝ} :
    0 ≤ boundedBernsteinVarianceSum X μ := by
  unfold boundedBernsteinVarianceSum
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg (X i ω)

/-- Fixed-parameter Chernoff form behind bounded Bernstein. -/
theorem bounded_bernstein_mgf_sum_two_sided
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K θ t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : 0 < K)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_window : θ < 3 / K) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp
        (-θ * t + boundedBernsteinMGFScale K θ * boundedBernsteinVarianceSum X μ) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let V : ℝ := boundedBernsteinVarianceSum X μ
  let g : ℝ := boundedBernsteinMGFScale K θ
  have hθ_abs : |θ| < 3 / K := by simpa [abs_of_nonneg hθ_nonneg] using hθ_window
  have hIcc : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-K) K := by
    intro i
    filter_upwards [hbound i] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have h_each_int_pos :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun ω => Real.exp (θ * X i ω)) μ := by
    intro i _hi
    exact ProbabilityTheory.integrable_exp_mul_of_mem_Icc (hXm i).aemeasurable (hIcc i)
  have hsum_int_pos :
      Integrable (fun ω => Real.exp (θ * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := θ) hXm (s := (Finset.univ : Finset ι)) h_each_int_pos
    simpa [S, Finset.sum_apply] using h
  have hmgf_sum_pos :
      mgf S μ θ = ∏ i, mgf (X i) μ θ := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), X i) μ θ =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (X i) μ θ :=
      hindep.mgf_sum (t := θ) hXm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le_pos :
      mgf S μ θ ≤ Real.exp (g * V) := by
    have hsingle :
        ∀ i, mgf (X i) μ θ ≤
          Real.exp (g * ∫ ω, X i ω ^ 2 ∂μ) := by
      intro i
      dsimp [g]
      exact bounded_bernstein_mgf_bound
        (μ := μ) (X := X i) (K := K) (θ := θ)
        hK (hXm i).aemeasurable (hbound i) (hmean i) hθ_abs
    calc
      mgf S μ θ = ∏ i, mgf (X i) μ θ := hmgf_sum_pos
      _ ≤ ∏ i, Real.exp (g * ∫ ω, X i ω ^ 2 ∂μ) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact hsingle i
      _ = Real.exp (∑ i, g * ∫ ω, X i ω ^ 2 ∂μ) := by
        rw [Real.exp_sum]
      _ = Real.exp (g * V) := by
        congr 1
        dsimp [V, boundedBernsteinVarianceSum]
        rw [Finset.mul_sum]
  let η : ℝ := -θ
  have hη_nonpos : η ≤ 0 := by
    dsimp [η]
    exact neg_nonpos.mpr hθ_nonneg
  have hη_abs : |η| < 3 / K := by
    simpa [η, abs_neg] using hθ_abs
  have hg_eta : boundedBernsteinMGFScale K η = g := by
    dsimp [η, g, boundedBernsteinMGFScale]
    simp [abs_neg]
  have h_each_int_neg :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun ω => Real.exp (η * X i ω)) μ := by
    intro i _hi
    exact ProbabilityTheory.integrable_exp_mul_of_mem_Icc (hXm i).aemeasurable (hIcc i)
  have hsum_int_neg :
      Integrable (fun ω => Real.exp (η * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := η) hXm (s := (Finset.univ : Finset ι)) h_each_int_neg
    simpa [S, Finset.sum_apply] using h
  have hmgf_sum_neg :
      mgf S μ η = ∏ i, mgf (X i) μ η := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), X i) μ η =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (X i) μ η :=
      hindep.mgf_sum (t := η) hXm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le_neg :
      mgf S μ η ≤ Real.exp (g * V) := by
    have hsingle :
        ∀ i, mgf (X i) μ η ≤
          Real.exp (g * ∫ ω, X i ω ^ 2 ∂μ) := by
      intro i
      have hraw :=
        bounded_bernstein_mgf_bound
          (μ := μ) (X := X i) (K := K) (θ := η)
          hK (hXm i).aemeasurable (hbound i) (hmean i) hη_abs
      simpa [hg_eta] using hraw
    calc
      mgf S μ η = ∏ i, mgf (X i) μ η := hmgf_sum_neg
      _ ≤ ∏ i, Real.exp (g * ∫ ω, X i ω ^ 2 ∂μ) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact hsingle i
      _ = Real.exp (∑ i, g * ∫ ω, X i ω ^ 2 ∂μ) := by
        rw [Real.exp_sum]
      _ = Real.exp (g * V) := by
        congr 1
        dsimp [V, boundedBernsteinVarianceSum]
        rw [Finset.mul_sum]
  let U : Set Ω := {ω | t ≤ S ω}
  let L : Set Ω := {ω | S ω ≤ -t}
  have hsubset : {ω | t ≤ |∑ i, X i ω|} ⊆ U ∪ L := by
    intro ω hω
    by_cases hnonneg : 0 ≤ S ω
    · left
      dsimp [U, S] at *
      simpa [abs_of_nonneg hnonneg] using hω
    · right
      have hneg : S ω < 0 := lt_of_not_ge hnonneg
      have hle : S ω ≤ -t := by
        have hAbs : t ≤ -(S ω) := by
          have hωS : t ≤ |S ω| := by simpa [S] using hω
          simpa [abs_of_neg hneg] using hωS
        linarith
      exact hle
  have hupper :
      μ.real U ≤ Real.exp (-θ * t + g * V) := by
    have htail :
        μ.real U ≤ Real.exp (-θ * t) * mgf S μ θ := by
      dsimp [U]
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := S) t hθ_nonneg hsum_int_pos
    calc
      μ.real U ≤ Real.exp (-θ * t) * mgf S μ θ := htail
      _ ≤ Real.exp (-θ * t) * Real.exp (g * V) := by
        exact mul_le_mul_of_nonneg_left hmgf_le_pos (Real.exp_pos _).le
      _ = Real.exp (-θ * t + g * V) := by rw [Real.exp_add]
  have hlower :
      μ.real L ≤ Real.exp (-θ * t + g * V) := by
    have htail :
        μ.real L ≤ Real.exp (-η * (-t)) * mgf S μ η := by
      dsimp [L]
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := μ) (X := S) (-t) hη_nonpos hsum_int_neg
    calc
      μ.real L ≤ Real.exp (-η * (-t)) * mgf S μ η := htail
      _ ≤ Real.exp (-η * (-t)) * Real.exp (g * V) := by
        exact mul_le_mul_of_nonneg_left hmgf_le_neg (Real.exp_pos _).le
      _ = Real.exp (-θ * t + g * V) := by
        dsimp [η]
        rw [Real.exp_add]
        ring_nf
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ μ.real (U ∪ L) := MeasureTheory.measureReal_mono hsubset
    _ ≤ μ.real U + μ.real L := MeasureTheory.measureReal_union_le U L
    _ ≤ Real.exp (-θ * t + g * V) + Real.exp (-θ * t + g * V) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-θ * t + boundedBernsteinMGFScale K θ *
        boundedBernsteinVarianceSum X μ) := by
      dsimp [g, V]
      ring

lemma bounded_bernstein_theta_nonneg {K V t : ℝ}
    (_hK : 0 < K) (_hV : 0 < V) (ht : 0 ≤ t) :
    0 ≤ t / (V + K * t / 3) := by
  have hden : 0 < V + K * t / 3 := by positivity
  exact div_nonneg ht hden.le

lemma bounded_bernstein_theta_lt {K V t : ℝ}
    (hK : 0 < K) (hV : 0 < V) (ht : 0 ≤ t) :
    t / (V + K * t / 3) < 3 / K := by
  have hden : 0 < V + K * t / 3 := by positivity
  rw [div_lt_div_iff₀ hden hK]
  nlinarith

lemma bounded_bernstein_exponent_optimized {K V t : ℝ}
    (hK : 0 < K) (hV : 0 < V) (ht : 0 ≤ t) :
    let θ : ℝ := t / (V + K * t / 3);
    -θ * t + boundedBernsteinMGFScale K θ * V =
      -(t ^ 2 / 2) / (V + K * t / 3) := by
  let θ : ℝ := t / (V + K * t / 3)
  change -θ * t + boundedBernsteinMGFScale K θ * V =
      -(t ^ 2 / 2) / (V + K * t / 3)
  have hden : 0 < V + K * t / 3 := by positivity
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    exact div_nonneg ht hden.le
  have hden2 : 0 < 1 - |θ| * K / 3 := by
    have hlt : θ < 3 / K := by
      dsimp [θ]
      exact bounded_bernstein_theta_lt hK hV ht
    rw [abs_of_nonneg hθ_nonneg]
    rw [lt_div_iff₀ hK] at hlt
    nlinarith
  dsimp [θ, boundedBernsteinMGFScale]
  rw [abs_of_nonneg (div_nonneg ht hden.le)]
  field_simp [hden.ne', hden2.ne', hK.ne']
  ring

/-- HDP Theorem 2.8.4, optimized bounded Bernstein inequality in the
positive variance-sum case. -/
theorem bounded_bernstein_sum_two_sided_positive_variance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : 0 < K)
    (hVpos : 0 < boundedBernsteinVarianceSum X μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp
        (-(t ^ 2 / 2) / (boundedBernsteinVarianceSum X μ + K * t / 3)) := by
  classical
  let V : ℝ := boundedBernsteinVarianceSum X μ
  let θ : ℝ := t / (V + K * t / 3)
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ, V]
    exact bounded_bernstein_theta_nonneg hK hVpos ht
  have hθ_window : θ < 3 / K := by
    dsimp [θ, V]
    exact bounded_bernstein_theta_lt hK hVpos ht
  have htail :=
    bounded_bernstein_mgf_sum_two_sided
      (μ := μ) (X := X) (K := K) (θ := θ) (t := t)
      hindep hXm hbound hmean hK hθ_nonneg hθ_window
  have hopt :
      -θ * t + boundedBernsteinMGFScale K θ * V =
        -(t ^ 2 / 2) / (V + K * t / 3) := by
    simpa [θ] using bounded_bernstein_exponent_optimized hK hVpos ht
  have htailV :
      μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ 2 * Real.exp (-θ * t + boundedBernsteinMGFScale K θ * V) := by
    simpa [V] using htail
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ 2 * Real.exp (-θ * t + boundedBernsteinMGFScale K θ * V) := htailV
    _ = 2 * Real.exp (-(t ^ 2 / 2) / (V + K * t / 3)) := by rw [hopt]

/-- HDP Theorem 2.8.4, bounded Bernstein inequality.  The variance parameter
is the displayed sum `σ² = ∑ᵢ E Xᵢ²`, written here as
`boundedBernsteinVarianceSum X μ`. -/
theorem bounded_bernstein_sum_two_sided
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : 0 < K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp
        (-(t ^ 2 / 2) / (boundedBernsteinVarianceSum X μ + K * t / 3)) := by
  classical
  let V : ℝ := boundedBernsteinVarianceSum X μ
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    exact boundedBernsteinVarianceSum_nonneg
  by_cases hVpos : 0 < V
  · simpa [V] using
      bounded_bernstein_sum_two_sided_positive_variance
        (μ := μ) (X := X) (K := K) (t := t)
        hindep hXm hbound hmean hK hVpos ht
  · have hVzero : V = 0 := le_antisymm (le_of_not_gt hVpos) hVnonneg
    by_cases htpos : 0 < t
    · have hsum_zero :
          (∑ i, ∫ ω, X i ω ^ 2 ∂μ) = 0 := by
        simpa [V, boundedBernsteinVarianceSum] using hVzero
      have hIntegral_zero : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 0 := by
        have hnonneg :
            ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∫ ω, X i ω ^ 2 ∂μ := by
          intro i _hi
          exact integral_nonneg fun ω => sq_nonneg (X i ω)
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset ι))
            (f := fun i => ∫ ω, X i ω ^ 2 ∂μ) hnonneg).1 hsum_zero
        intro i
        exact hall i (Finset.mem_univ i)
      have hXsq_int : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := by
        intro i
        have hXsq_aesm : AEStronglyMeasurable (fun ω => X i ω ^ 2) μ := by
          simpa [pow_two] using ((hXm i).aemeasurable.mul (hXm i).aemeasurable).aestronglyMeasurable
        refine Integrable.of_bound hXsq_aesm (K ^ 2) ?_
        filter_upwards [hbound i] with ω hω
        have hsq : |X i ω| ^ 2 ≤ K ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg (X i ω)) hω 2
        simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X i ω)), sq_abs] using hsq
      have hXi_zero : ∀ i, X i =ᵐ[μ] 0 := by
        intro i
        have hsq_zero :
            (fun ω => X i ω ^ 2) =ᵐ[μ] (fun _ω => (0 : ℝ)) :=
          (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X i ω)) (hXsq_int i)).1
            (hIntegral_zero i)
        exact hsq_zero.mono fun ω hω => by
          exact (sq_eq_zero_iff.mp hω)
      have h_all_zero : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 :=
        (Filter.eventually_all).2 hXi_zero
      have hEvent_empty :
          {ω | t ≤ |∑ i, X i ω|} =ᶠ[ae μ] (∅ : Set Ω) := by
        refine Filter.eventuallyEq_set.mpr ?_
        filter_upwards [h_all_zero] with ω hω
        have hsum : (∑ i, X i ω) = 0 := by simp [hω]
        simp [hsum, htpos.not_ge]
      have hprob_zero : μ.real {ω | t ≤ |∑ i, X i ω|} = 0 := by
        rw [MeasureTheory.measureReal_congr hEvent_empty]
        simp
      calc
        μ.real {ω | t ≤ |∑ i, X i ω|} = 0 := hprob_zero
        _ ≤ 2 * Real.exp
            (-(t ^ 2 / 2) / (boundedBernsteinVarianceSum X μ + K * t / 3)) := by
          positivity
    · have htzero : t = 0 := le_antisymm (le_of_not_gt htpos) ht
      have hprob : μ.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 := measureReal_le_one
      have hrhs :
          1 ≤ 2 * Real.exp
            (-(t ^ 2 / 2) / (boundedBernsteinVarianceSum X μ + K * t / 3)) := by
        simp [htzero, V, hVzero]
      exact hprob.trans hrhs

/-- HDP Theorem 2.8.4 with an explicit named variance parameter `σ²`. -/
theorem bounded_bernstein_sum_two_sided_of_variance_eq
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t σ2 : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hσ2 : σ2 = boundedBernsteinVarianceSum X μ)
    (hK : 0 < K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(t ^ 2 / 2) / (σ2 + K * t / 3)) := by
  simpa [hσ2] using
    bounded_bernstein_sum_two_sided
      (μ := μ) (X := X) (K := K) (t := t)
      hindep hXm hbound hmean hK ht

/-- The Bennett function `h(u) = (1+u) log(1+u) - u` appearing in HDP
Theorem 2.9.2. -/
def bennettFunction (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u

/-- Scalar MGF bound behind Bennett's inequality.  If `X` is centered and
`|X| ≤ K`, then for nonnegative `θ`,
`E exp(θX) ≤ exp((E X² / K²) * (exp(θK)-1-θK))`. -/
theorem bennett_mgf_bound
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K θ : ℝ}
    (hK : 0 < K)
    (hθ : 0 ≤ θ)
    (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    mgf X μ θ ≤
      Real.exp (((∫ ω, X ω ^ 2 ∂μ) / K ^ 2) *
        (Real.exp (θ * K) - 1 - θ * K)) := by
  by_cases hθ0 : θ = 0
  · subst hθ0
    simp
  have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
  let A : ℝ := Real.exp (θ * K) - 1 - θ * K
  let q : ℝ := A / K ^ 2
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-K) K := by
    filter_upwards [hbound] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have hexp_int : Integrable (fun ω => Real.exp (θ * X ω)) μ :=
    ProbabilityTheory.integrable_exp_mul_of_mem_Icc hXm hIcc
  have hX_int : Integrable X μ := by
    refine Integrable.of_bound hXm.aestronglyMeasurable K ?_
    filter_upwards [hbound] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hXsq_aesm : AEStronglyMeasurable (fun ω => X ω ^ 2) μ := by
    simpa [pow_two] using (hXm.mul hXm).aestronglyMeasurable
  have hXsq_int : Integrable (fun ω => X ω ^ 2) μ := by
    refine Integrable.of_bound hXsq_aesm (K ^ 2) ?_
    filter_upwards [hbound] with ω hω
    have hsq : |X ω| ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg (X ω)) hω 2
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω)), sq_abs] using hsq
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have h := Real.add_one_le_exp (θ * K)
    nlinarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hA_nonneg (sq_nonneg K)
  let G : Ω → ℝ := fun ω => 1 + θ * X ω + q * X ω ^ 2
  have hG_int : Integrable G μ := by
    have hconst : Integrable (fun _ω : Ω => (1 : ℝ)) μ := integrable_const 1
    have hlin : Integrable (fun ω => θ * X ω) μ := hX_int.const_mul θ
    have hquad : Integrable (fun ω => q * X ω ^ 2) μ := hXsq_int.const_mul q
    simpa [G, add_assoc] using (hconst.add hlin).add hquad
  have hpoint : (fun ω => Real.exp (θ * X ω)) ≤ᶠ[ae μ] G := by
    filter_upwards [hbound] with ω hω
    have hxle : X ω ≤ K := (abs_le.mp hω).2
    have hscalar :=
      real_exp_le_bennett_remainder
        (u := θ * X ω) (v := θ * K) (by positivity)
        (mul_le_mul_of_nonneg_left hxle hθ)
    have hterm :
        ((θ * X ω) ^ 2 / (θ * K) ^ 2) * A = q * X ω ^ 2 := by
      dsimp [A, q]
      field_simp [hθpos.ne', hK.ne']
    have hterm' :
        ((θ * X ω) ^ 2 / (θ * K) ^ 2) *
          (Real.exp (θ * K) - 1 - θ * K) = q * X ω ^ 2 := by
      simpa [A] using hterm
    calc
      Real.exp (θ * X ω)
          ≤ 1 + θ * X ω + ((θ * X ω) ^ 2 / (θ * K) ^ 2) *
              (Real.exp (θ * K) - 1 - θ * K) := hscalar
      _ = G ω := by
        dsimp [G]
        rw [hterm']
  have hintegral_le : ∫ ω, Real.exp (θ * X ω) ∂μ ≤ ∫ ω, G ω ∂μ :=
    integral_mono_ae hexp_int hG_int hpoint
  have hG_integral :
      ∫ ω, G ω ∂μ = 1 + θ * (∫ ω, X ω ∂μ) + q * (∫ ω, X ω ^ 2 ∂μ) := by
    calc
      ∫ ω, G ω ∂μ
          = ∫ ω, (1 : ℝ) + θ * X ω + q * X ω ^ 2 ∂μ := rfl
      _ = ∫ ω, ((1 : ℝ) + θ * X ω) ∂μ + ∫ ω, q * X ω ^ 2 ∂μ := by
        exact integral_add (integrable_const 1 |>.add (hX_int.const_mul θ)) (hXsq_int.const_mul q)
      _ = (∫ _ω : Ω, (1 : ℝ) ∂μ + ∫ ω, θ * X ω ∂μ) +
            ∫ ω, q * X ω ^ 2 ∂μ := by
        rw [integral_add (integrable_const 1) (hX_int.const_mul θ)]
      _ = 1 + θ * (∫ ω, X ω ∂μ) + q * (∫ ω, X ω ^ 2 ∂μ) := by
        rw [integral_const, integral_const_mul, integral_const_mul]
        simp
  have hsecond_nonneg : 0 ≤ ∫ ω, X ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (X ω)
  have hlin_to_exp :
      1 + q * (∫ ω, X ω ^ 2 ∂μ) ≤
        Real.exp (q * ∫ ω, X ω ^ 2 ∂μ) := by
    simpa [add_comm] using
      Real.add_one_le_exp (q * ∫ ω, X ω ^ 2 ∂μ)
  calc
    mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
    _ ≤ ∫ ω, G ω ∂μ := hintegral_le
    _ = 1 + θ * (∫ ω, X ω ∂μ) + q * (∫ ω, X ω ^ 2 ∂μ) := hG_integral
    _ = 1 + q * (∫ ω, X ω ^ 2 ∂μ) := by simp [hmean]
    _ ≤ Real.exp (q * ∫ ω, X ω ^ 2 ∂μ) := hlin_to_exp
    _ = Real.exp (((∫ ω, X ω ^ 2 ∂μ) / K ^ 2) *
        (Real.exp (θ * K) - 1 - θ * K)) := by
      dsimp [q, A]
      congr 1
      ring

/-- Fixed-parameter Chernoff form behind Bennett's inequality. -/
theorem bennett_mgf_sum_upper_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K θ t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : 0 < K)
    (hθ : 0 ≤ θ) :
    μ.real {ω | t ≤ ∑ i, X i ω}
      ≤ Real.exp
        (-θ * t + (boundedBernsteinVarianceSum X μ / K ^ 2) *
          (Real.exp (θ * K) - 1 - θ * K)) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let V : ℝ := boundedBernsteinVarianceSum X μ
  let A : ℝ := Real.exp (θ * K) - 1 - θ * K
  have hIcc : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-K) K := by
    intro i
    filter_upwards [hbound i] with ω hω
    simpa [Set.mem_Icc, abs_le] using hω
  have h_each_int :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun ω => Real.exp (θ * X i ω)) μ := by
    intro i _hi
    exact ProbabilityTheory.integrable_exp_mul_of_mem_Icc (hXm i).aemeasurable (hIcc i)
  have hsum_int :
      Integrable (fun ω => Real.exp (θ * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := θ) hXm (s := (Finset.univ : Finset ι)) h_each_int
    simpa [S, Finset.sum_apply] using h
  have htail :
      μ.real {ω | t ≤ S ω} ≤ Real.exp (-θ * t) * mgf S μ θ :=
    ProbabilityTheory.measure_ge_le_exp_mul_mgf
      (μ := μ) (X := S) t hθ hsum_int
  have hmgf_sum :
      mgf S μ θ = ∏ i, mgf (X i) μ θ := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), X i) μ θ =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (X i) μ θ :=
      hindep.mgf_sum (t := θ) hXm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le :
      mgf S μ θ ≤ Real.exp ((V / K ^ 2) * A) := by
    have hsingle :
        ∀ i, mgf (X i) μ θ ≤
          Real.exp (((∫ ω, X i ω ^ 2 ∂μ) / K ^ 2) * A) := by
      intro i
      dsimp [A]
      exact bennett_mgf_bound
        (μ := μ) (X := X i) (K := K) (θ := θ)
        hK hθ (hXm i).aemeasurable (hbound i) (hmean i)
    calc
      mgf S μ θ = ∏ i, mgf (X i) μ θ := hmgf_sum
      _ ≤ ∏ i, Real.exp (((∫ ω, X i ω ^ 2 ∂μ) / K ^ 2) * A) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact hsingle i
      _ = Real.exp (∑ i, ((∫ ω, X i ω ^ 2 ∂μ) / K ^ 2) * A) := by
        rw [Real.exp_sum]
      _ = Real.exp ((V / K ^ 2) * A) := by
        congr 1
        dsimp [V, boundedBernsteinVarianceSum]
        rw [← Finset.sum_mul, Finset.sum_div]
  calc
    μ.real {ω | t ≤ ∑ i, X i ω}
        = μ.real {ω | t ≤ S ω} := by simp [S]
    _ ≤ Real.exp (-θ * t) * mgf S μ θ := htail
    _ ≤ Real.exp (-θ * t) * Real.exp ((V / K ^ 2) * A) := by
      exact mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
    _ = Real.exp (-θ * t + (V / K ^ 2) * A) := by rw [Real.exp_add]

lemma bennett_theta_nonneg {K V t : ℝ}
    (hK : 0 < K) (hV : 0 < V) (ht : 0 ≤ t) :
    0 ≤ Real.log (1 + K * t / V) / K := by
  have hbase_ge : 1 ≤ 1 + K * t / V := by
    have hnonneg : 0 ≤ K * t / V := by positivity
    linarith
  exact div_nonneg (Real.log_nonneg hbase_ge) hK.le

lemma bennett_exponent_optimized {K V t θ : ℝ}
    (hK : 0 < K) (hV : 0 < V) (ht : 0 ≤ t)
    (hθ : θ = Real.log (1 + K * t / V) / K) :
    -θ * t + (V / K ^ 2) * (Real.exp (θ * K) - 1 - θ * K)
      = -(V / K ^ 2) * bennettFunction (K * t / V) := by
  subst θ
  have hbase_pos : 0 < 1 + K * t / V := by
    have hnonneg : 0 ≤ K * t / V := by positivity
    linarith
  have hθK :
      Real.log (1 + K * t / V) / K * K =
        Real.log (1 + K * t / V) := by
    field_simp [hK.ne']
  rw [hθK, Real.exp_log hbase_pos]
  dsimp [bennettFunction]
  field_simp [hK.ne', hV.ne']
  ring

/-- HDP Theorem 2.9.2, Bennett inequality for centered independent bounded
variables, in the positive variance case. -/
theorem bennett_sum_upper_tail_positive_variance
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hK : 0 < K)
    (hV : 0 < boundedBernsteinVarianceSum X μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, X i ω}
      ≤ Real.exp (-(boundedBernsteinVarianceSum X μ / K ^ 2) *
        bennettFunction (K * t / boundedBernsteinVarianceSum X μ)) := by
  classical
  let V : ℝ := boundedBernsteinVarianceSum X μ
  let θ : ℝ := Real.log (1 + K * t / V) / K
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ, V]
    exact bennett_theta_nonneg hK hV ht
  have htail :=
    bennett_mgf_sum_upper_tail
      (μ := μ) (X := X) (K := K) (θ := θ) (t := t)
      hindep hXm hbound hmean hK hθ_nonneg
  have hopt :
      -θ * t + (V / K ^ 2) * (Real.exp (θ * K) - 1 - θ * K)
        = -(V / K ^ 2) * bennettFunction (K * t / V) := by
    exact bennett_exponent_optimized hK hV ht rfl
  calc
    μ.real {ω | t ≤ ∑ i, X i ω}
        ≤ Real.exp (-θ * t + (V / K ^ 2) *
          (Real.exp (θ * K) - 1 - θ * K)) := by
      simpa [V] using htail
    _ = Real.exp (-(V / K ^ 2) * bennettFunction (K * t / V)) := by
      rw [hopt]

/-- HDP Theorem 2.9.2, raw-variable form:
`P{∑ᵢ (Xᵢ - E Xᵢ) ≥ t} ≤ exp(-(σ²/K²) h(Kt/σ²))`, where
`σ² = ∑ᵢ E (Xᵢ - E Xᵢ)²`. -/
theorem bennett_sum_centered_deviation_upper_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K t σ2 : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXint : ∀ i, Integrable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω - ∫ ω, X i ω ∂μ| ≤ K)
    (hσ2 : σ2 = boundedBernsteinVarianceSum
      (fun i ω => X i ω - ∫ ω, X i ω ∂μ) μ)
    (hK : 0 < K)
    (hσ2pos : 0 < σ2)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - ∫ ω, X i ω ∂μ)}
      ≤ Real.exp (-(σ2 / K ^ 2) * bennettFunction (K * t / σ2)) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => X i ω - ∫ ω, X i ω ∂μ
  have hindepY : iIndepFun Y μ := by
    simpa [Y] using
      hindep.comp (fun i x => x - ∫ ω, X i ω ∂μ) (fun _ => by fun_prop)
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    dsimp [Y]
    exact (hXm i).sub measurable_const
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    dsimp [Y]
    rw [integral_sub (hXint i) (integrable_const _), integral_const]
    simp
  have hVpos : 0 < boundedBernsteinVarianceSum Y μ := by
    simpa [hσ2] using hσ2pos
  have htail :=
    bennett_sum_upper_tail_positive_variance
      (μ := μ) (X := Y) (K := K) (t := t)
      hindepY hYm (by simpa [Y] using hbound) hYmean hK hVpos ht
  simpa [Y, hσ2] using htail

/-- Conditional Hoeffding lemma for a bounded martingale difference.  If each
regular conditional law sees `X` in a fixed interval and with conditional mean
zero, then `X` has the corresponding conditional sub-Gaussian MGF proxy. -/
theorem hasCondSubgaussianMGF_of_cond_mem_Icc_of_cond_integral_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ}
    {X : Ω → ℝ} {a b : ℝ}
    (hXm : AEMeasurable X μ)
    (hglobal : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hcond_meas : ∀ᵐ ω' ∂(μ.trim hm),
      AEMeasurable X ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
    (hcond_bound : ∀ᵐ ω' ∂(μ.trim hm),
      ∀ᵐ ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'),
        X ω ∈ Set.Icc a b)
    (hcond_mean : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ ω, X ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') = 0) :
    @HasCondSubgaussianMGF Ω m mΩ hm inferInstance X ((‖b - a‖₊ / 2) ^ 2) μ
      inferInstance := by
  refine ⟨?_, ?_⟩
  · intro t
    rw [@condExpKernel_comp_trim Ω m mΩ inferInstance μ inferInstance hm]
    exact integrable_exp_mul_of_mem_Icc hXm hglobal
  · filter_upwards [hcond_meas, hcond_bound, hcond_mean] with ω' hXm' hb hm0 t
    haveI : IsProbabilityMeasure
        ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') := by
      infer_instance
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
      (X := X) (a := a) (b := b) hXm' hb hm0).mgf_le t

/-- Conditional Hoeffding lemma with a past-dependent interval location.  The
length `c` is deterministic, while each regular conditional law may use its own
left endpoint. -/
theorem hasCondSubgaussianMGF_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ}
    {X : Ω → ℝ} {c : ℝ}
    (_hc : 0 ≤ c)
    (hXm : AEMeasurable X μ)
    (hglobal_abs : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hcond_meas : ∀ᵐ ω' ∂(μ.trim hm),
      AEMeasurable X ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
    (hcond_bound : ∀ᵐ ω' ∂(μ.trim hm),
      ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'),
        X ω ∈ Set.Icc a (a + c))
    (hcond_mean : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ ω, X ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') = 0) :
    @HasCondSubgaussianMGF Ω m mΩ hm inferInstance X ((‖c‖₊ / 2) ^ 2) μ
      inferInstance := by
  refine ⟨?_, ?_⟩
  · intro t
    rw [@condExpKernel_comp_trim Ω m mΩ inferInstance μ inferInstance hm]
    have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-c) c := by
      filter_upwards [hglobal_abs] with ω hω
      simpa [Set.mem_Icc, abs_le] using hω
    exact integrable_exp_mul_of_mem_Icc hXm hIcc
  · filter_upwards [hcond_meas, hcond_bound, hcond_mean] with ω' hXm' hbound hm0 t
    rcases hbound with ⟨a, hb⟩
    haveI : IsProbabilityMeasure
        ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') := by
      infer_instance
    have h :=
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
        (X := X) (a := a) (b := a + c) hXm' hb hm0).mgf_le t
    simpa [show a + c - a = c by ring] using h

/-- Variance proxy `∑ᵢ cᵢ²` in the bounded-differences/McDiarmid exponent. -/
def boundedDifferencesVarianceSum (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, c i ^ 2

/-- The sub-Gaussian proxy `cᵢ²/4` for a martingale difference bounded in
an interval of length `cᵢ`. -/
def boundedDifferencesSubgaussianProxy (c : ℕ → ℝ) (i : ℕ) : ℝ≥0 :=
  ⟨c i ^ 2 / 4, by positivity⟩

/-- Insert the deterministic dummy-coordinate width used by the shifted
product-space model for McDiarmid. -/
def shiftedBoundedDifferenceConstants (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => c n

@[simp]
lemma shiftedBoundedDifferenceConstants_zero (c : ℕ → ℝ) :
    shiftedBoundedDifferenceConstants c 0 = 0 := rfl

@[simp]
lemma shiftedBoundedDifferenceConstants_succ (c : ℕ → ℝ) (n : ℕ) :
    shiftedBoundedDifferenceConstants c (n + 1) = c n := rfl

lemma shiftedBoundedDifferenceConstants_nonneg {c : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ shiftedBoundedDifferenceConstants c i
  | 0 => by simp
  | n + 1 => hc n

lemma boundedDifferencesVarianceSum_shifted_succ (c : ℕ → ℝ) (N : ℕ) :
    boundedDifferencesVarianceSum (shiftedBoundedDifferenceConstants c) (N + 1) =
      boundedDifferencesVarianceSum c N := by
  induction N with
  | zero =>
      simp [boundedDifferencesVarianceSum]
  | succ N ih =>
      have hprev :
          ∑ i ∈ Finset.range (N + 1), shiftedBoundedDifferenceConstants c i ^ 2 =
            ∑ i ∈ Finset.range N, c i ^ 2 := by
        simpa [boundedDifferencesVarianceSum] using ih
      calc
        boundedDifferencesVarianceSum (shiftedBoundedDifferenceConstants c) (N + 2)
            = (∑ i ∈ Finset.range (N + 1),
                shiftedBoundedDifferenceConstants c i ^ 2) +
                shiftedBoundedDifferenceConstants c (N + 1) ^ 2 := by
              simp [boundedDifferencesVarianceSum, Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range N, c i ^ 2) + c N ^ 2 := by
              rw [hprev]
              simp
        _ = boundedDifferencesVarianceSum c (N + 1) := by
              simp [boundedDifferencesVarianceSum, Finset.sum_range_succ]

/-- A deterministic diameter lemma used in sharp bounded-differences proofs:
if a nonempty real-valued family has pairwise diameter at most `c`, then all
values lie in some interval of length exactly `c`. -/
lemma exists_Icc_length_of_pairwise_abs_sub_le {α : Type*} [Nonempty α]
    {g : α → ℝ} {c : ℝ} (_hc : 0 ≤ c)
    (hdiam : ∀ x y, |g x - g y| ≤ c) :
    ∃ a : ℝ, ∀ x, g x ∈ Set.Icc a (a + c) := by
  let S : Set ℝ := Set.range g
  have hSnonempty : S.Nonempty := Set.range_nonempty g
  let x0 : α := Classical.choice inferInstance
  have hbddBelow : BddBelow S := by
    refine ⟨g x0 - c, ?_⟩
    rintro y ⟨x, rfl⟩
    have h := hdiam x0 x
    have h' : g x0 - g x ≤ c :=
      (le_abs_self (g x0 - g x)).trans h
    linarith
  refine ⟨sInf S, ?_⟩
  intro x
  constructor
  · exact csInf_le hbddBelow ⟨x, rfl⟩
  · have hlower : g x - c ∈ lowerBounds S := by
      intro y hy
      rcases hy with ⟨z, rfl⟩
      have h := hdiam x z
      have h' : g x - g z ≤ c :=
        (le_abs_self (g x - g z)).trans h
      linarith
    have hle : g x - c ≤ sInf S :=
      le_csInf hSnonempty hlower
    linarith

/-- If a centered random variable is a.s. contained in an interval of length
`c`, then it is a.s. bounded in absolute value by `c`. -/
lemma ae_abs_le_of_mem_Icc_length_of_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {X : Ω → ℝ} {a c : ℝ}
    (hXm : AEMeasurable X ν)
    (hb : ∀ᵐ ω ∂ν, X ω ∈ Set.Icc a (a + c))
    (hmean : ∫ ω, X ω ∂ν = 0) :
    ∀ᵐ ω ∂ν, |X ω| ≤ c := by
  have hbound_abs : ∀ᵐ ω ∂ν, ‖X ω‖ ≤ max |a| |a + c| := by
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hω.1 hω.2
  have hXint : Integrable X ν := by
    exact Integrable.of_bound hXm.aestronglyMeasurable (max |a| |a + c|) hbound_abs
  have hge : a ≤ ∫ ω, X ω ∂ν := by
    calc
      a = ∫ _ω : Ω, a ∂ν := by simp
      _ ≤ ∫ ω, X ω ∂ν := by
        exact integral_mono_ae (integrable_const a) hXint (hb.mono fun _ω hω => hω.1)
  have hle : ∫ ω, X ω ∂ν ≤ a + c := by
    calc
      ∫ ω, X ω ∂ν ≤ ∫ _ω : Ω, a + c ∂ν := by
        exact integral_mono_ae hXint (integrable_const (a + c)) (hb.mono fun _ω hω => hω.2)
      _ = a + c := by simp
  have ha_nonpos : a ≤ 0 := by simpa [hmean] using hge
  have hzero_le_ac : 0 ≤ a + c := by simpa [hmean] using hle
  filter_upwards [hb] with ω hω
  rw [abs_le]
  constructor
  · linarith [hω.1, hzero_le_ac]
  · linarith [hω.2, ha_nonpos]

/-- Conditional interval ranges of deterministic length and zero conditional
mean imply the corresponding global absolute bound. -/
lemma ae_abs_le_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ}
    {X : Ω → ℝ} {c : ℝ}
    (hXm : @Measurable Ω ℝ mΩ (borel ℝ) X)
    (hcond_meas : ∀ᵐ ω' ∂(μ.trim hm),
      AEMeasurable X ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
    (hcond_bound : ∀ᵐ ω' ∂(μ.trim hm),
      ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'),
        X ω ∈ Set.Icc a (a + c))
    (hcond_mean : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ ω, X ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') = 0) :
    ∀ᵐ ω ∂μ, |X ω| ≤ c := by
  let K : @Kernel Ω Ω m mΩ := @condExpKernel Ω mΩ inferInstance μ inferInstance m
  have hcond_abs : ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂K ω', |X ω| ≤ c := by
    filter_upwards [hcond_meas, hcond_bound, hcond_mean] with ω' hXm' hbound hmean
    rcases hbound with ⟨a, ha⟩
    exact @ae_abs_le_of_mem_Icc_length_of_integral_eq_zero Ω mΩ (K ω') _ X a c
      hXm' ha hmean
  have hmeas_set : @MeasurableSet Ω mΩ {ω | |X ω| ≤ c} := by
    change @MeasurableSet Ω mΩ ((fun ω => |X ω|) ⁻¹' Set.Iic c)
    have habs : @Measurable Ω ℝ mΩ (borel ℝ) (fun ω => |X ω|) :=
      @Measurable.comp Ω ℝ ℝ mΩ (borel ℝ) (borel ℝ) abs X measurable_abs hXm
    exact habs measurableSet_Iic
  have hcomp : ∀ᵐ ω ∂(K ∘ₘ μ.trim hm), |X ω| ≤ c := by
    exact @Measure.ae_comp_of_ae_ae Ω Ω m mΩ (μ.trim hm) K (fun ω => |X ω| ≤ c)
      hmeas_set hcond_abs
  have hmeasure : K ∘ₘ μ.trim hm = μ := by
    dsimp [K]
    exact @ProbabilityTheory.condExpKernel_comp_trim Ω m mΩ inferInstance μ inferInstance hm
  rw [← hmeasure]
  exact hcomp

/-- Conditional Hoeffding lemma with past-dependent interval locations, where
the global absolute bound is derived from the conditional interval ranges and
zero conditional means. -/
theorem hasCondSubgaussianMGF_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero_of_measurable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ}
    {X : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c)
    (hXm : @Measurable Ω ℝ mΩ (borel ℝ) X)
    (hcond_meas : ∀ᵐ ω' ∂(μ.trim hm),
      AEMeasurable X ((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'))
    (hcond_bound : ∀ᵐ ω' ∂(μ.trim hm),
      ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω'),
        X ω ∈ Set.Icc a (a + c))
    (hcond_mean : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ ω, X ω ∂((@condExpKernel Ω mΩ inferInstance μ inferInstance m) ω') = 0) :
    @HasCondSubgaussianMGF Ω m mΩ hm inferInstance X ((‖c‖₊ / 2) ^ 2) μ
      inferInstance := by
  have hglobal := ae_abs_le_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero
    (μ := μ) (m := m) (hm := hm) (X := X) (c := c)
    hXm hcond_meas hcond_bound hcond_mean
  exact hasCondSubgaussianMGF_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero
    (μ := μ) (m := m) (hm := hm) (X := X) (c := c)
    hc hXm.aemeasurable hglobal hcond_meas hcond_bound hcond_mean

lemma abs_integral_sub_integral_le_of_ae_abs_sub_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {f g : α → ℝ} {c : ℝ}
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hfg : ∀ᵐ x ∂ν, |f x - g x| ≤ c) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤ c := by
  have hdiff : Integrable (fun x => f x - g x) ν := hf.sub hg
  have habs : Integrable (fun x => |f x - g x|) ν := hdiff.abs
  calc
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| = |∫ x, f x - g x ∂ν| := by
      rw [integral_sub hf hg]
    _ ≤ ∫ x, |f x - g x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ _x : α, c ∂ν := by
      exact integral_mono_ae habs (integrable_const c) hfg
    _ = c := by simp

universe u

/-- Add a deterministic dummy coordinate before an independent sequence.  This
lets the first genuine random coordinate be generated by a Markov kernel, so
all Doob increments are handled uniformly by `Kernel.condExp_traj'`. -/
abbrev shiftedSeqType (X : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => X n

instance shiftedSeqType.measurableSpace {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] :
    ∀ n, MeasurableSpace (shiftedSeqType X n)
  | 0 => inferInstance
  | _ + 1 => inferInstance

instance shiftedSeqType.standardBorel {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)] :
    ∀ n, StandardBorelSpace (shiftedSeqType X n)
  | 0 => inferInstance
  | _ + 1 => inferInstance

instance shiftedSeqType.nonempty {X : ℕ → Type u} [∀ n, Nonempty (X n)] :
    ∀ n, Nonempty (shiftedSeqType X n)
  | 0 => inferInstance
  | _ + 1 => inferInstance

/-- Drop the deterministic dummy coordinate from a shifted sequence. -/
def shiftedTail {X : ℕ → Type u}
    (z : (n : ℕ) → shiftedSeqType X n) (i : ℕ) : X i :=
  z (i + 1)

/-- The shifted product measure family: a deterministic dummy coordinate at
time `0`, followed by the original independent coordinate laws. -/
noncomputable def shiftedMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) :
    (n : ℕ) → Measure (shiftedSeqType X n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => μ n

instance shiftedMeasure.isProbabilityMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] :
    ∀ n, IsProbabilityMeasure (shiftedMeasure (X := X) μ n)
  | 0 => by dsimp [shiftedMeasure]; infer_instance
  | n + 1 => by dsimp [shiftedMeasure]; infer_instance

/-- The finite product law of the shifted independent coordinates strictly
after `a` and up to `N`. -/
noncomputable abbrev shiftedFutureProductMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) (a N : ℕ) :
    Measure ((j : Finset.Ioc a N) → shiftedSeqType X (j : ℕ)) :=
  @Measure.pi (Finset.Ioc a N) (fun j => shiftedSeqType X (j : ℕ)) inferInstance
    (fun j => shiftedSeqType.measurableSpace (X := X) (j : ℕ))
    (fun j => shiftedMeasure (X := X) μ (j : ℕ))

instance shiftedFutureProductMeasure.isProbabilityMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] (a N : ℕ) :
    IsProbabilityMeasure (shiftedFutureProductMeasure (X := X) μ a N) := by
  dsimp [shiftedFutureProductMeasure]
  infer_instance

/-- Coordinate bounded-differences predicate for a function on the first `N`
coordinates of a sequence. -/
def SeqBoundedDifferences {X : ℕ → Type u}
    (f : ((n : ℕ) → X n) → ℝ) (c : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i < N, ∀ x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ c i

/-- If two inputs agree from coordinate `N` onward, coordinate bounded
differences over the first `N` coordinates control the total oscillation by
the sum of the first `N` constants. -/
lemma seqBoundedDifferences_diff_le_sum_of_eq_from {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {M N : ℕ}
    (hbd : SeqBoundedDifferences f c M) (hNM : N ≤ M)
    {x y : (n : ℕ) → X n}
    (hxy : ∀ j, N ≤ j → x j = y j) :
    |f x - f y| ≤ ∑ i ∈ Finset.range N, c i := by
  induction N generalizing x y with
  | zero =>
      have hfun : x = y := by
        funext j
        exact hxy j (zero_le j)
      simp [hfun]
  | succ N ih =>
      let y' := Function.update y N (x N)
      have hxy' : ∀ j, N ≤ j → x j = y' j := by
        intro j hj
        by_cases hNj : j = N
        · subst hNj
          simp [y']
        · have hsucc : N + 1 ≤ j := by omega
          have htail := hxy j hsucc
          simp [y', hNj, htail]
      have hNltM : N < M := lt_of_lt_of_le (Nat.lt_succ_self N) hNM
      have hy'_diff : ∀ j, j ≠ N → y' j = y j := by
        intro j hj
        simp [y', hj]
      have hstep : |f y' - f y| ≤ c N := hbd N hNltM y' y hy'_diff
      have hprev : |f x - f y'| ≤ ∑ i ∈ Finset.range N, c i :=
        ih (Nat.le_of_succ_le hNM) hxy'
      calc
        |f x - f y| ≤ |f x - f y'| + |f y' - f y| := by
          have hsum : f x - f y = (f x - f y') + (f y' - f y) := by ring
          rw [hsum]
          exact abs_add_le _ _
        _ ≤ (∑ i ∈ Finset.range N, c i) + c N := add_le_add hprev hstep
        _ = ∑ i ∈ Finset.range (N + 1), c i := by
          simp [Finset.sum_range_succ]

/-- A finite-coordinate bounded-differences function has deterministic
diameter at most the sum of its coordinate constants. -/
lemma seqBoundedDifferences_diff_le_sum {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (x y : (n : ℕ) → X n) :
    |f x - f y| ≤ ∑ i ∈ Finset.range N, c i := by
  let y' := Function.updateFinset y (Finset.range N) (fun i : Finset.range N => x (i : ℕ))
  have hxy' : f x = f y' := by
    exact hdep fun j hj => by
      have hjmem : j ∈ Finset.range N := by simpa [Finset.mem_range] using hj
      simp [y', Function.updateFinset, hjmem]
  have hy'y_tail : ∀ j, N ≤ j → y' j = y j := by
    intro j hj
    have hjnot : j ∉ Finset.range N := by simpa [Finset.mem_range] using not_lt.mpr hj
    simp [y', Function.updateFinset, hjnot]
  have htail := seqBoundedDifferences_diff_le_sum_of_eq_from
    (X := X) (f := f) (c := c) (M := N) (N := N) hbd le_rfl hy'y_tail
  simpa [hxy'] using htail

/-- A measurable function depending only on the prefix up to `N` is strongly
measurable with respect to the product filtration at level `N`. -/
lemma aestronglyMeasurable_piLE_of_dependsOn {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
    {F : ((n : ℕ) → X n) → ℝ} {N : ℕ} {μ : Measure ((n : ℕ) → X n)}
    (hdep : DependsOn F (Set.Iic N))
    (hFmeas : Measurable F) :
    AEStronglyMeasurable[MeasureTheory.Filtration.piLE (X := X) N] F μ := by
  let base : (n : ℕ) → X n := fun n => Classical.ofNonempty
  let g : ((j : Finset.Iic N) → X (j : ℕ)) → ℝ :=
    fun xN => F (Function.updateFinset base (Finset.Iic N) xN)
  have hg : Measurable g := by
    exact hFmeas.comp (by
      simpa [g] using (measurable_updateFinset (x := base) (s := Finset.Iic N)))
  have hgf : @Measurable ((n : ℕ) → X n) ℝ
      (MeasureTheory.Filtration.piLE (X := X) N) (borel ℝ)
      (fun z => g (Preorder.frestrictLe N z)) := by
    rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe (X := X) N]
    exact hg.comp (Measurable.of_comap_le le_rfl)
  have hpoint : (fun z => g (Preorder.frestrictLe N z)) = F := by
    funext z
    dsimp [g]
    exact hdep fun j hj => by
      have hjmem : j ∈ Finset.Iic N := by simpa [Finset.mem_Iic] using hj
      simp [Function.updateFinset, hjmem, Preorder.frestrictLe]
  exact hgf.aestronglyMeasurable.congr (ae_of_all _ fun _z => by rw [hpoint])

/-- The constant Markov kernel that generates the next independent coordinate
in the shifted sequence model. -/
noncomputable def shiftedIndependentKernel {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n))
    (n : ℕ) :
    Kernel ((i : Finset.Iic n) → shiftedSeqType X i) (shiftedSeqType X (n + 1)) := by
  cases n with
  | zero => exact Kernel.const _ (μ 0)
  | succ n => exact Kernel.const _ (μ (n + 1))

lemma shiftedIndependentKernel_eq_const_shiftedMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) (n : ℕ) :
    shiftedIndependentKernel (X := X) μ n =
      Kernel.const _ (shiftedMeasure (X := X) μ (n + 1)) := by
  cases n <;> rfl

instance shiftedIndependentKernel.isMarkovKernel {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] :
    ∀ n, IsMarkovKernel (shiftedIndependentKernel (X := X) μ n) := by
  intro n
  cases n <;> dsimp [shiftedIndependentKernel] <;> infer_instance

/-- The deterministic initial state on the dummy coordinate. -/
noncomputable def shiftedInitial {X : ℕ → Type u} :
    (i : Finset.Iic 0) → shiftedSeqType X i := fun i => by
  cases i with
  | mk val hval =>
    simp only [Finset.mem_Iic] at hval
    have hzero : val = 0 := Nat.eq_zero_of_le_zero hval
    subst hzero
    exact PUnit.unit

/-- The prefix of a shifted sequence at the deterministic dummy coordinate is
the canonical dummy initial state. -/
lemma frestrictLe_zero_shifted_eq_initial {X : ℕ → Type u}
    (z : (n : ℕ) → shiftedSeqType X n) :
    Preorder.frestrictLe 0 z = shiftedInitial (X := X) := by
  funext i
  cases i with
  | mk val hval =>
    simp only [Finset.mem_Iic] at hval
    have hzero : val = 0 := Nat.eq_zero_of_le_zero hval
    subst hzero
    rfl

/-- The independent product trajectory with a deterministic dummy coordinate
at time `0` and genuine independent coordinates at times `1,2,...`. -/
noncomputable def shiftedIndependentTraj {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] :
    Measure ((n : ℕ) → shiftedSeqType X n) := by
  exact Kernel.traj (shiftedIndependentKernel (X := X) μ) 0 (shiftedInitial (X := X))

instance shiftedIndependentTraj.isProbabilityMeasure {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)] :
    IsProbabilityMeasure (shiftedIndependentTraj (X := X) μ) := by
  dsimp [shiftedIndependentTraj]
  infer_instance

/-- Lift a function of the genuine coordinates to the shifted trajectory space. -/
noncomputable def shiftedFunction {X : ℕ → Type u}
    (f : ((n : ℕ) → X n) → ℝ) :
    ((n : ℕ) → shiftedSeqType X n) → ℝ :=
  fun z => f (shiftedTail z)

lemma shiftedFunction_dependsOn {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {N : ℕ}
    (hf : DependsOn f (Set.Iio N)) :
    DependsOn (shiftedFunction f) (Set.Iic N) := by
  intro z w hzw
  dsimp [shiftedFunction, shiftedTail]
  exact hf fun j hj => hzw (j + 1) (by simpa [Set.mem_Iic] using Nat.succ_le_of_lt hj)

/-- A finite-coordinate bounded-differences function has an integrable shifted
lift under every probability measure, provided the shifted lift is measurable. -/
lemma shiftedFunction_integrable_of_boundedDifferences {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
    {ν : Measure ((n : ℕ) → shiftedSeqType X n)} [IsProbabilityMeasure ν]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (hFmeas : Measurable (shiftedFunction f)) :
    Integrable (shiftedFunction f) ν := by
  let ref : (n : ℕ) → X n := fun n => Classical.ofNonempty
  let S : ℝ := ∑ i ∈ Finset.range N, c i
  let C : ℝ := |f ref| + S
  refine Integrable.of_bound hFmeas.aestronglyMeasurable C ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  let x := shiftedTail z
  have hdiff := seqBoundedDifferences_diff_le_sum (X := X) (f := f) (c := c) (N := N)
    hdep hbd x ref
  have htri : |f x| ≤ |f x - f ref| + |f ref| := by
    calc
      |f x| = |(f x - f ref) + f ref| := by ring_nf
      _ ≤ |f x - f ref| + |f ref| :=
        (abs_add_le (f x - f ref) (f ref) :
          |(f x - f ref) + f ref| ≤ |f x - f ref| + |f ref|)
  dsimp [shiftedFunction] at htri ⊢
  change |f x| ≤ C
  dsimp [C, S]
  linarith

/-- A finite-coordinate bounded-differences function is integrable over any
finite shifted future product once its shifted lift is measurable. -/
lemma shiftedFunction_future_integrable_of_boundedDifferences {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N a : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (hFmeas : Measurable (shiftedFunction f))
    (z : (n : ℕ) → shiftedSeqType X n) :
    Integrable (fun u => shiftedFunction f
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) a N
          (Preorder.frestrictLe a z, u))))
      (shiftedFutureProductMeasure (X := X) μ a N) := by
  let ref : (n : ℕ) → X n := fun n => Classical.ofNonempty
  let S : ℝ := ∑ i ∈ Finset.range N, c i
  let C : ℝ := |f ref| + S
  have hmeas : Measurable (fun u => shiftedFunction f
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) a N
          (Preorder.frestrictLe a z, u)))) := by
    exact hFmeas.comp (by fun_prop)
  refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  let x := shiftedTail
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) a N
          (Preorder.frestrictLe a z, u)))
  have hdiff := seqBoundedDifferences_diff_le_sum (X := X) (f := f) (c := c) (N := N)
    hdep hbd x ref
  have htri : |f x| ≤ |f x - f ref| + |f ref| := by
    calc
      |f x| = |(f x - f ref) + f ref| := by ring_nf
      _ ≤ |f x - f ref| + |f ref| :=
        (abs_add_le (f x - f ref) (f ref) :
          |(f x - f ref) + f ref| ≤ |f x - f ref| + |f ref|)
  dsimp [shiftedFunction] at htri ⊢
  change |f x| ≤ C
  dsimp [C, S]
  linarith

/-- If two shifted sequences agree away from shifted coordinate `i + 1`, then
their genuine tails agree away from coordinate `i`. -/
lemma shiftedTail_eq_of_eq_shifted {X : ℕ → Type u}
    {z w : (n : ℕ) → shiftedSeqType X n} {i : ℕ}
    (h : ∀ j, j ≠ i + 1 → z j = w j) :
    ∀ k, k ≠ i → shiftedTail z k = shiftedTail w k := by
  intro k hk
  exact h (k + 1) (by omega)

/-- The shifted lift of a coordinate-bounded-differences function has the same
bounded-differences constant on the corresponding non-dummy coordinate. -/
lemma shiftedFunction_boundedDifference {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hbd : SeqBoundedDifferences f c N) (hi : i < N)
    {z w : (n : ℕ) → shiftedSeqType X n}
    (h : ∀ j, j ≠ i + 1 → z j = w j) :
    |shiftedFunction f z - shiftedFunction f w| ≤ c i := by
  exact hbd i hi (shiftedTail z) (shiftedTail w) (shiftedTail_eq_of_eq_shifted h)

lemma updateFinset_eq_away_of_frestrictLe_eq {X : ℕ → Type u}
    {i : ℕ} {z w y : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w) :
    ∀ j, j ≠ i + 1 →
      Function.updateFinset y (Finset.Iic (i + 1)) (Preorder.frestrictLe (i + 1) z) j =
      Function.updateFinset y (Finset.Iic (i + 1)) (Preorder.frestrictLe (i + 1) w) j := by
  intro j hj
  by_cases hle : j ≤ i + 1
  · have hj_mem : j ∈ Finset.Iic (i + 1) := by simpa [Finset.mem_Iic] using hle
    have hji : j ≤ i := by omega
    have hzwi : z j = w j := by
      have hfun := congrFun hzw ⟨j, by simpa [Finset.mem_Iic] using hji⟩
      simpa [Preorder.frestrictLe] using hfun
    simp [Function.updateFinset, hj_mem, hzwi]
  · have hj_not : j ∉ Finset.Iic (i + 1) := by simpa [Finset.mem_Iic] using hle
    simp [Function.updateFinset, hj_not]

lemma shiftedFunction_updateFinset_diff_le {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hbd : SeqBoundedDifferences f c N) (hi : i < N)
    {z w y : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w) :
    |shiftedFunction f
        (Function.updateFinset y (Finset.Iic (i + 1)) (Preorder.frestrictLe (i + 1) z)) -
      shiftedFunction f
        (Function.updateFinset y (Finset.Iic (i + 1)) (Preorder.frestrictLe (i + 1) w))| ≤ c i := by
  exact shiftedFunction_boundedDifference (X := X) (f := f) (c := c) (N := N) (i := i)
    hbd hi (updateFinset_eq_away_of_frestrictLe_eq (X := X) (i := i) hzw)

lemma shiftedFunction_updateFinset_Iic_diff_le {X : ℕ → Type u}
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N) (hi : i < N)
    {base z w : (n : ℕ) → shiftedSeqType X n}
    {xz xw : (j : Finset.Iic N) → shiftedSeqType X j}
    (hxw : ∀ j (hj : j ≤ N), j ≠ i + 1 →
      xz ⟨j, by simpa [Finset.mem_Iic] using hj⟩ =
      xw ⟨j, by simpa [Finset.mem_Iic] using hj⟩) :
    |shiftedFunction f (Function.updateFinset z (Finset.Iic N) xz) -
      shiftedFunction f (Function.updateFinset w (Finset.Iic N) xw)| ≤ c i := by
  let F : ((n : ℕ) → shiftedSeqType X n) → ℝ := shiftedFunction f
  have hFdep : DependsOn F (Set.Iic N) := shiftedFunction_dependsOn (X := X) (f := f) hdep
  have hzbase : F (Function.updateFinset z (Finset.Iic N) xz) =
      F (Function.updateFinset base (Finset.Iic N) xz) := by
    exact hFdep fun j hj => by
      have hj_mem : j ∈ Finset.Iic N := by simpa [Finset.mem_Iic] using hj
      simp [Function.updateFinset, hj_mem]
  have hwbase : F (Function.updateFinset w (Finset.Iic N) xw) =
      F (Function.updateFinset base (Finset.Iic N) xw) := by
    exact hFdep fun j hj => by
      have hj_mem : j ∈ Finset.Iic N := by simpa [Finset.mem_Iic] using hj
      simp [Function.updateFinset, hj_mem]
  change |F (Function.updateFinset z (Finset.Iic N) xz) -
      F (Function.updateFinset w (Finset.Iic N) xw)| ≤ c i
  rw [hzbase, hwbase]
  refine shiftedFunction_boundedDifference (X := X) (f := f) (c := c) (N := N) (i := i)
    hbd hi ?_
  intro j hj
  by_cases hjN : j ≤ N
  · have hj_mem : j ∈ Finset.Iic N := by simpa [Finset.mem_Iic] using hjN
    simp [Function.updateFinset, hj_mem, hxw j hjN hj]
  · have hj_not : j ∉ Finset.Iic N := by simpa [Finset.mem_Iic] using hjN
    simp [Function.updateFinset, hj_not]

lemma IicProdIoc_shifted_prefix_eq_away {X : ℕ → Type u}
    {i N : ℕ}
    {z w : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w)
    (u : (j : Finset.Ioc (i + 1) N) → shiftedSeqType X j) :
    ∀ j (hj : j ≤ N), j ≠ i + 1 →
      IicProdIoc (X := shiftedSeqType X) (i + 1) N
        (Preorder.frestrictLe (i + 1) z, u)
        ⟨j, by simpa [Finset.mem_Iic] using hj⟩ =
      IicProdIoc (X := shiftedSeqType X) (i + 1) N
        (Preorder.frestrictLe (i + 1) w, u)
        ⟨j, by simpa [Finset.mem_Iic] using hj⟩ := by
  intro j hj hjne
  by_cases hja : j ≤ i + 1
  · have hji : j ≤ i := by omega
    have hzwi : z j = w j := by
      have hfun := congrFun hzw ⟨j, by simpa [Finset.mem_Iic] using hji⟩
      simpa [Preorder.frestrictLe] using hfun
    simp [IicProdIoc, hja, hzwi]
  · simp [IicProdIoc, hja]

lemma shiftedFunction_future_integral_diff_le {X : ℕ → Type u}
    [∀ n, MeasurableSpace (shiftedSeqType X n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N) (hi : i < N)
    {z w : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w)
    {ν : Measure ((j : Finset.Ioc (i + 1) N) → shiftedSeqType X j)}
    [IsProbabilityMeasure ν]
    (hzint : Integrable (fun u => shiftedFunction f
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) z, u)))) ν)
    (hwint : Integrable (fun u => shiftedFunction f
      (Function.updateFinset w (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) w, u)))) ν) :
    |((∫ u, shiftedFunction f
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) z, u))) ∂ν) -
      (∫ u, shiftedFunction f
      (Function.updateFinset w (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) w, u))) ∂ν))| ≤ c i := by
  refine abs_integral_sub_integral_le_of_ae_abs_sub_le hzint hwint ?_
  filter_upwards with u
  exact shiftedFunction_updateFinset_Iic_diff_le (X := X) (f := f) (c := c)
    (N := N) (i := i) hdep hbd hi
    (base := z) (z := z) (w := w)
    (xz := IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) z, u))
    (xw := IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) w, u))
    (IicProdIoc_shifted_prefix_eq_away (X := X) (i := i) (N := N) hzw u)

/-- Pointwise trajectory-integral representative of the Doob conditional
expectation for the shifted independent product. -/
noncomputable def shiftedTrajM {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ((n : ℕ) → shiftedSeqType X n) → ℝ) (k : ℕ) :
    ((n : ℕ) → shiftedSeqType X n) → ℝ :=
  fun z => ∫ y, F y
    ∂ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) k
      (Preorder.frestrictLe k z)

/-- The trajectory representative at time `k` only depends on the observed
prefix up to `k`. -/
lemma shiftedTrajM_dependsOn {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ((n : ℕ) → shiftedSeqType X n) → ℝ) (k : ℕ) :
    DependsOn (shiftedTrajM μ F k) (Set.Iic k) := by
  intro z w hzw
  dsimp [shiftedTrajM]
  have hp : Preorder.frestrictLe k z = Preorder.frestrictLe k w := by
    funext i
    have hi : (i : ℕ) ≤ k := Finset.mem_Iic.mp i.2
    exact hzw i (by simpa [Set.mem_Iic] using hi)
  rw [hp]

lemma integral_traj_eq_of_dependsOn_Iic {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    {κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1))}
    [∀ n, IsMarkovKernel (κ n)] {F : ((n : ℕ) → X n) → ℝ} {N : ℕ}
    (hdep : DependsOn F (Set.Iic N))
    {x : (i : Finset.Iic N) → X i} {z : (n : ℕ) → X n}
    (hFsm : AEStronglyMeasurable F (ProbabilityTheory.Kernel.traj κ N x)) :
    ∫ y, F y ∂ProbabilityTheory.Kernel.traj κ N x =
      F (Function.updateFinset z (Finset.Iic N) x) := by
  rw [ProbabilityTheory.Kernel.integral_traj (κ := κ) (a := N) (x₀ := x) hFsm]
  apply integral_eq_const
  filter_upwards with y
  exact hdep fun j hj => by
    have hj_mem : j ∈ Finset.Iic N := by simpa [Finset.mem_Iic] using hj
    simp [Function.updateFinset, hj_mem]

lemma integral_traj_eq_partialTraj_of_dependsOn_Iic {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    {κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1))}
    [∀ n, IsMarkovKernel (κ n)] {F : ((n : ℕ) → X n) → ℝ} {k N : ℕ}
    (hkN : k ≤ N) (hdep : DependsOn F (Set.Iic N))
    {xk : (i : Finset.Iic k) → X i} {z : (n : ℕ) → X n}
    (hFint : Integrable F (ProbabilityTheory.Kernel.traj κ k xk)) :
    ∫ y, F y ∂ProbabilityTheory.Kernel.traj κ k xk =
      ∫ xN, F (Function.updateFinset z (Finset.Iic N) xN)
        ∂ProbabilityTheory.Kernel.partialTraj κ k N xk := by
  have hdecomp := ProbabilityTheory.Kernel.integral_traj_partialTraj
    (κ := κ) (a := k) (b := N) hkN (x₀ := xk) (f := F) hFint
  rw [← hdecomp]
  have hsm_ae := ProbabilityTheory.Kernel.aestronglyMeasurable_traj
    (κ := κ) (a := k) (b := N) hkN (f := F) (x₀ := xk) hFint.1
  refine integral_congr_ae ?_
  filter_upwards [hsm_ae] with xN hxN
  exact integral_traj_eq_of_dependsOn_Iic (κ := κ) (N := N) hdep (x := xN) (z := z) hxN

/-- For the shifted independent product, a finite partial trajectory integral
from an observed prefix `a` to `N` is the same as integrating over the product
law of the unobserved shifted coordinates `a < j ≤ N`. -/
lemma shifted_partialTraj_integral_eq_future {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ} {a N : ℕ}
    (haN : a ≤ N)
    {z : (n : ℕ) → shiftedSeqType X n} :
    ∫ xN, F (Function.updateFinset z (Finset.Iic N) xN)
      ∂ProbabilityTheory.Kernel.partialTraj (shiftedIndependentKernel (X := X) μ) a N
        (Preorder.frestrictLe a z)
    = ∫ u, F (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) a N
          (Preorder.frestrictLe a z, u)))
      ∂shiftedFutureProductMeasure (X := X) μ a N := by
  let ν := shiftedFutureProductMeasure (X := X) μ a N
  let pref := Preorder.frestrictLe a z
  let G := fun xN : (j : Finset.Iic N) → shiftedSeqType X (j : ℕ) =>
    F (Function.updateFinset z (Finset.Iic N) xN)
  let e := fun u : (j : Finset.Ioc a N) → shiftedSeqType X (j : ℕ) =>
    IicProdIoc (X := shiftedSeqType X) a N (pref, u)
  have hemb : MeasurableEmbedding e := by
    dsimp [e, pref]
    exact (MeasurableEquiv.IicProdIoc (X := shiftedSeqType X) haN).measurableEmbedding.comp
      (measurableEmbedding_prodMk_left (Preorder.frestrictLe a z))
  have hκ : shiftedIndependentKernel (X := X) μ =
      fun n => ProbabilityTheory.Kernel.const ((i : Finset.Iic n) → shiftedSeqType X (i : ℕ))
        (shiftedMeasure (X := X) μ (n + 1)) := by
    funext n
    exact shiftedIndependentKernel_eq_const_shiftedMeasure (X := X) μ n
  change ∫ xN, G xN
      ∂ProbabilityTheory.Kernel.partialTraj (shiftedIndependentKernel (X := X) μ) a N pref =
    ∫ u, G (e u) ∂ν
  rw [hκ]
  rw [MeasureTheory.partialTraj_const (X := shiftedSeqType X) (μ := shiftedMeasure (X := X) μ)]
  rw [ProbabilityTheory.Kernel.map_apply]
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.id_apply,
    ProbabilityTheory.Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_map]
  exact MeasurableEmbedding.integral_map hemb G
  all_goals fun_prop

/-- Coordinate bounded differences compare the two `i + 1` trajectory
conditional-expectation representatives when the observed histories agree up
to time `i`; the remaining future is integrated against the same product law. -/
lemma shiftedTrajM_succ_diff_le_of_boundedDifferences {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N) (hi : i < N)
    {z w : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w)
    (hzint : Integrable (shiftedFunction f)
      (ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) (i + 1)
        (Preorder.frestrictLe (i + 1) z)))
    (hwint : Integrable (shiftedFunction f)
      (ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) (i + 1)
        (Preorder.frestrictLe (i + 1) w)))
    (hzfuture : Integrable (fun u => shiftedFunction f
      (Function.updateFinset z (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) z, u))))
      (shiftedFutureProductMeasure (X := X) μ (i + 1) N))
    (hwfuture : Integrable (fun u => shiftedFunction f
      (Function.updateFinset w (Finset.Iic N)
        (IicProdIoc (X := shiftedSeqType X) (i + 1) N
          (Preorder.frestrictLe (i + 1) w, u))))
      (shiftedFutureProductMeasure (X := X) μ (i + 1) N)) :
    |shiftedTrajM μ (shiftedFunction f) (i + 1) z -
      shiftedTrajM μ (shiftedFunction f) (i + 1) w| ≤ c i := by
  let κ := shiftedIndependentKernel (X := X) μ
  let F := shiftedFunction f
  have haN : i + 1 ≤ N := Nat.succ_le_of_lt hi
  have hFdep : DependsOn F (Set.Iic N) :=
    shiftedFunction_dependsOn (X := X) (f := f) hdep
  have hz_partial := integral_traj_eq_partialTraj_of_dependsOn_Iic
    (κ := κ) (F := F) (k := i + 1) (N := N) haN hFdep
    (xk := Preorder.frestrictLe (i + 1) z) (z := z) hzint
  have hw_partial := integral_traj_eq_partialTraj_of_dependsOn_Iic
    (κ := κ) (F := F) (k := i + 1) (N := N) haN hFdep
    (xk := Preorder.frestrictLe (i + 1) w) (z := w) hwint
  have hz_future := shifted_partialTraj_integral_eq_future
    (X := X) μ (F := F) (a := i + 1) (N := N) haN (z := z)
  have hw_future := shifted_partialTraj_integral_eq_future
    (X := X) μ (F := F) (a := i + 1) (N := N) haN (z := w)
  change |(∫ y, F y ∂ProbabilityTheory.Kernel.traj κ (i + 1)
        (Preorder.frestrictLe (i + 1) z)) -
      (∫ y, F y ∂ProbabilityTheory.Kernel.traj κ (i + 1)
        (Preorder.frestrictLe (i + 1) w))| ≤ c i
  rw [hz_partial, hw_partial, hz_future, hw_future]
  exact shiftedFunction_future_integral_diff_le (X := X) (f := f) (c := c)
    (N := N) (i := i) hdep hbd hi hzw hzfuture hwfuture

/-- Measurable finite-coordinate bounded-differences functions satisfy the
`i + 1` trajectory comparison without separate integrability hypotheses. -/
lemma shiftedTrajM_succ_diff_le_of_boundedDifferences_measurable {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (hFmeas : Measurable (shiftedFunction f))
    (hi : i < N)
    {z w : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w) :
    |shiftedTrajM μ (shiftedFunction f) (i + 1) z -
      shiftedTrajM μ (shiftedFunction f) (i + 1) w| ≤ c i := by
  refine shiftedTrajM_succ_diff_le_of_boundedDifferences (X := X) μ
    (f := f) (c := c) (N := N) (i := i) hdep hbd hi hzw ?_ ?_ ?_ ?_
  · exact shiftedFunction_integrable_of_boundedDifferences (X := X)
      (ν := ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) (i + 1)
        (Preorder.frestrictLe (i + 1) z)) hdep hbd hFmeas
  · exact shiftedFunction_integrable_of_boundedDifferences (X := X)
      (ν := ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) (i + 1)
        (Preorder.frestrictLe (i + 1) w)) hdep hbd hFmeas
  · exact shiftedFunction_future_integrable_of_boundedDifferences (X := X) μ
      (f := f) (c := c) (N := N) (a := i + 1) hdep hbd hFmeas z
  · exact shiftedFunction_future_integrable_of_boundedDifferences (X := X) μ
      (f := f) (c := c) (N := N) (a := i + 1) hdep hbd hFmeas w

/-- Pointwise trajectory-integral representative of the shifted Doob
martingale differences. -/
noncomputable def shiftedTrajDiff {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ((n : ℕ) → shiftedSeqType X n) → ℝ) : ℕ →
      ((n : ℕ) → shiftedSeqType X n) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun z => shiftedTrajM μ F (k + 1) z - shiftedTrajM μ F k z

/-- Non-initial trajectory differences only depend on the prefix up to that
non-initial time. -/
lemma shiftedTrajDiff_succ_dependsOn {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ((n : ℕ) → shiftedSeqType X n) → ℝ) (i : ℕ) :
    DependsOn (shiftedTrajDiff μ F (i + 1)) (Set.Iic (i + 1)) := by
  intro z w hzw
  dsimp [shiftedTrajDiff]
  have h1 := shiftedTrajM_dependsOn (X := X) μ F (i + 1) hzw
  have h0 : shiftedTrajM μ F i z = shiftedTrajM μ F i w := by
    exact shiftedTrajM_dependsOn (X := X) μ F i
      (fun j hj => hzw j (le_trans hj (Nat.le_succ i)))
  rw [h1, h0]

/-- Coordinate bounded differences give the prefixwise diameter condition for
the shifted trajectory Doob differences. -/
lemma shiftedTrajDiff_diameter_of_boundedDifferences {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N i : ℕ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (hFmeas : Measurable (shiftedFunction f))
    (hi : i < N)
    {z w : (n : ℕ) → shiftedSeqType X n}
    (hzw : Preorder.frestrictLe i z = Preorder.frestrictLe i w) :
    |shiftedTrajDiff μ (shiftedFunction f) (i + 1) z -
      shiftedTrajDiff μ (shiftedFunction f) (i + 1) w| ≤ c i := by
  have hM1 := shiftedTrajM_succ_diff_le_of_boundedDifferences_measurable (X := X) μ
    (f := f) (c := c) (N := N) (i := i) hdep hbd hFmeas hi hzw
  have hM0 : shiftedTrajM μ (shiftedFunction f) i z =
      shiftedTrajM μ (shiftedFunction f) i w := by
    exact shiftedTrajM_dependsOn (X := X) μ (shiftedFunction f) i
      (fun j hj => by
        have hfun := congrFun hzw ⟨j, by simpa [Finset.mem_Iic] using hj⟩
        simpa [Preorder.frestrictLe] using hfun)
  dsimp [shiftedTrajDiff]
  rw [hM0]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hM1

/-- Doob conditional expectation process for a function and filtration. -/
noncomputable def doobM {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (F : Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  μ[F | ℱ k]

/-- For the shifted independent trajectory, the Doob conditional expectation
with respect to the canonical product filtration is represented by integrating
over the future trajectory from the observed prefix. -/
lemma doobM_shifted_ae_eq_traj_integral {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ))
    (k : ℕ) :
    doobM (shiftedIndependentTraj (X := X) μ)
      (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F k
      =ᵐ[shiftedIndependentTraj (X := X) μ]
      fun z => ∫ y, F y
        ∂ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) k
          (Preorder.frestrictLe k z) := by
  dsimp [doobM, shiftedIndependentTraj]
  exact ProbabilityTheory.Kernel.condExp_traj (κ := shiftedIndependentKernel (X := X) μ)
    (a := 0) (b := k) (x₀ := shiftedInitial (X := X)) (f := F) (zero_le k) hFint

/-- The preceding trajectory-integral formula expressed with `shiftedTrajM`. -/
lemma doobM_shifted_ae_eq_trajM {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ))
    (k : ℕ) :
    doobM (shiftedIndependentTraj (X := X) μ)
      (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F k
      =ᵐ[shiftedIndependentTraj (X := X) μ]
      shiftedTrajM μ F k := by
  simpa [shiftedTrajM] using
    doobM_shifted_ae_eq_traj_integral (X := X) μ hFint k

/-- Doob martingale differences, with the first term centered by the global
expectation. -/
noncomputable def doobDiff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (F : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => doobM μ ℱ F 0 ω - ∫ ω, F ω ∂μ
  | k + 1 => fun ω => doobM μ ℱ F (k + 1) ω - doobM μ ℱ F k ω

/-- In the shifted independent product, the dummy first Doob difference is
zero almost surely. -/
lemma doobDiff_shifted_zero_ae_eq_zero {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ)) :
    doobDiff (shiftedIndependentTraj (X := X) μ)
      (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F 0
      =ᵐ[shiftedIndependentTraj (X := X) μ] 0 := by
  have hM := doobM_shifted_ae_eq_traj_integral (X := X) μ hFint 0
  filter_upwards [hM] with z hz
  dsimp [doobDiff]
  rw [hz]
  have hprefix : Preorder.frestrictLe 0 z = shiftedInitial (X := X) :=
    frestrictLe_zero_shifted_eq_initial z
  rw [hprefix]
  change (∫ y, F y
        ∂ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) 0
          (shiftedInitial (X := X))) -
      (∫ y, F y
        ∂ProbabilityTheory.Kernel.traj (shiftedIndependentKernel (X := X) μ) 0
          (shiftedInitial (X := X))) = 0
  ring

/-- The `condExp`-based shifted Doob differences agree almost surely with the
pointwise trajectory representatives. -/
lemma doobDiff_shifted_ae_eq_trajDiff {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ))
    (k : ℕ) :
    doobDiff (shiftedIndependentTraj (X := X) μ)
      (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F k
      =ᵐ[shiftedIndependentTraj (X := X) μ]
      shiftedTrajDiff μ F k := by
  cases k with
  | zero =>
      simpa [shiftedTrajDiff] using
        doobDiff_shifted_zero_ae_eq_zero (X := X) μ hFint
  | succ k =>
      have hM1 := doobM_shifted_ae_eq_trajM (X := X) μ hFint (k + 1)
      have hM0 := doobM_shifted_ae_eq_trajM (X := X) μ hFint k
      filter_upwards [hM1, hM0] with z hz1 hz0
      simp [doobDiff, shiftedTrajDiff, hz1, hz0]

/-- Under the regular conditional kernel given the product filtration up to
time `i`, the sampled trajectory has the same prefix up to `i` as the
conditioning trajectory. -/
lemma condExpKernel_piLE_ae_eq_prefix {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    {μ : Measure ((n : ℕ) → X n)} [IsProbabilityMeasure μ] (i : ℕ) :
    ∀ᵐ z ∂(μ.trim ((MeasureTheory.Filtration.piLE (X := X)).le i)),
      ∀ᵐ y ∂((@condExpKernel _ _ inferInstance μ inferInstance
        (MeasureTheory.Filtration.piLE (X := X) i)) z),
        Preorder.frestrictLe i y = Preorder.frestrictLe i z := by
  let Ω := ((n : ℕ) → X n)
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace Ω) :=
    MeasureTheory.Filtration.piLE (X := X)
  have hfirst : @Measurable Ω Ω (MeasurableSpace.pi : MeasurableSpace Ω) (ℱ i) id :=
    measurable_id'' (ℱ.le i)
  have hsecond : @Measurable Ω Ω (MeasurableSpace.pi : MeasurableSpace Ω)
      (MeasurableSpace.pi : MeasurableSpace Ω) id := measurable_id
  have hpair : @Measurable Ω (Ω × Ω) (MeasurableSpace.pi : MeasurableSpace Ω)
      ((ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω)) (fun ω : Ω => (ω, ω)) :=
    hfirst.prodMk hsecond
  have hp : MeasurableSet[(ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω)]
      {p : Ω × Ω | Preorder.frestrictLe i p.2 = Preorder.frestrictLe i p.1} := by
    have hprefix : @Measurable Ω ((j : Finset.Iic i) → X j)
        (ℱ i) (MeasurableSpace.pi : MeasurableSpace ((j : Finset.Iic i) → X j))
        (Preorder.frestrictLe i) := by
      rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe (X := X) i]
      exact Measurable.of_comap_le le_rfl
    have hfst0 : @Measurable (Ω × Ω) Ω
        ((ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω))
        (ℱ i) Prod.fst := measurable_fst
    have hfst : Measurable[(ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω)]
        (fun p : Ω × Ω => Preorder.frestrictLe i p.1) := hprefix.comp hfst0
    have hsnd0 : @Measurable (Ω × Ω) Ω
        ((ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω))
        (MeasurableSpace.pi : MeasurableSpace Ω) Prod.snd := measurable_snd
    have hsnd : Measurable[(ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω)]
        (fun p : Ω × Ω => Preorder.frestrictLe i p.2) := by
      exact (Preorder.measurable_frestrictLe i).comp hsnd0
    exact measurableSet_eq_fun hsnd hfst
  have hpair_ae : @AEMeasurable Ω (Ω × Ω)
      ((ℱ i).prod (MeasurableSpace.pi : MeasurableSpace Ω))
      (MeasurableSpace.pi : MeasurableSpace Ω) (fun ω : Ω => (ω, ω)) μ := by
    exact ⟨fun ω : Ω => (ω, ω), hpair, ae_eq_refl _⟩
  have hdiag : ∀ᵐ p ∂(@Measure.map Ω (Ω × Ω) _ ((ℱ i).prod
        (MeasurableSpace.pi : MeasurableSpace Ω)) (fun ω : Ω => (ω, ω)) μ),
      Preorder.frestrictLe i p.2 = Preorder.frestrictLe i p.1 := by
    rw [ae_map_iff hpair_ae hp]
    exact ae_of_all _ (fun ω => rfl)
  have hcomp : ∀ᵐ p ∂(μ.trim (ℱ.le i) ⊗ₘ
      (@condExpKernel Ω _ inferInstance μ inferInstance (ℱ i))),
      Preorder.frestrictLe i p.2 = Preorder.frestrictLe i p.1 := by
    rw [ProbabilityTheory.compProd_trim_condExpKernel (μ := μ) (m := ℱ i) (hm := ℱ.le i)]
    exact hdiag
  simpa [Ω, ℱ] using Measure.ae_ae_of_ae_compProd hcomp

/-- Prefixwise diameter of the pointwise shifted Doob representative yields
the conditional interval hypothesis for the `condExp`-based Doob difference. -/
lemma doobDiff_shifted_conditional_range_of_trajDiff_diameter {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ))
    {c : ℝ} (hc : 0 ≤ c) (i : ℕ)
    (hdiam : ∀ z w,
      Preorder.frestrictLe i z = Preorder.frestrictLe i w →
        |shiftedTrajDiff μ F (i + 1) z - shiftedTrajDiff μ F (i + 1) w| ≤ c) :
    ∀ᵐ z ∂((shiftedIndependentTraj (X := X) μ).trim
        ((MeasureTheory.Filtration.piLE (X := shiftedSeqType X)).le i)),
      ∃ a : ℝ, ∀ᵐ y ∂((@condExpKernel _ _ inferInstance
        (shiftedIndependentTraj (X := X) μ) inferInstance
        (MeasureTheory.Filtration.piLE (X := shiftedSeqType X) i)) z),
        doobDiff (shiftedIndependentTraj (X := X) μ)
          (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F (i + 1) y ∈
          Set.Icc a (a + c) := by
  let P := shiftedIndependentTraj (X := X) μ
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace ((n : ℕ) → shiftedSeqType X n)) :=
    MeasureTheory.Filtration.piLE (X := shiftedSeqType X)
  have hEqGlobal := doobDiff_shifted_ae_eq_trajDiff (X := X) μ hFint (i + 1)
  have hEqCond : ∀ᵐ z ∂(P.trim (ℱ.le i)),
      ∀ᵐ y ∂((@condExpKernel _ _ inferInstance P inferInstance (ℱ i)) z),
        doobDiff P ℱ F (i + 1) y = shiftedTrajDiff μ F (i + 1) y := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [ProbabilityTheory.condExpKernel_comp_trim (μ := P) (m := ℱ i) (hm := ℱ.le i)]
    exact hEqGlobal
  have hPrefix := condExpKernel_piLE_ae_eq_prefix
    (X := shiftedSeqType X) (μ := P) i
  filter_upwards [hEqCond, hPrefix] with z hEqz hPrefixz
  let α : Type u := {y : ((n : ℕ) → shiftedSeqType X n) //
      Preorder.frestrictLe i y = Preorder.frestrictLe i z}
  haveI : Nonempty α := ⟨⟨z, rfl⟩⟩
  let g : α → ℝ := fun y => shiftedTrajDiff μ F (i + 1) y.1
  have hdiam_g : ∀ x y : α, |g x - g y| ≤ c := by
    intro x y
    exact hdiam x.1 y.1 (x.2.trans y.2.symm)
  rcases exists_Icc_length_of_pairwise_abs_sub_le (α := α) (g := g) hc hdiam_g with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  filter_upwards [hEqz, hPrefixz] with y hy_eq hy_prefix
  rw [hy_eq]
  exact ha ⟨y, hy_prefix⟩

/-- The Doob differences are adapted to the same filtration. -/
lemma doobDiff_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (F : Ω → ℝ) :
    StronglyAdapted ℱ (doobDiff μ ℱ F) := by
  intro k
  cases k with
  | zero =>
      dsimp [doobDiff, doobM]
      exact stronglyMeasurable_condExp.sub stronglyMeasurable_const
  | succ k =>
      dsimp [doobDiff, doobM]
      exact stronglyMeasurable_condExp.sub
        (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ k)))

/-- Telescoping identity for the sum of the first `N + 1` Doob differences. -/
lemma doobDiff_sum_range_succ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (F : Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range (N + 1), doobDiff μ ℱ F i ω =
      doobM μ ℱ F N ω - ∫ ω, F ω ∂μ := by
  induction N with
  | zero => simp [doobDiff, doobM]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      change (∑ i ∈ Finset.range (N + 1), doobDiff μ ℱ F i ω) +
          (doobM μ ℱ F (N + 1) ω - doobM μ ℱ F N ω) =
        doobM μ ℱ F (N + 1) ω - ∫ ω, F ω ∂μ
      rw [ih]
      ring

/-- If `F` is measurable with respect to filtration level `N`, its Doob
conditional expectation at time `N` is `F` almost surely. -/
lemma doobM_ae_eq_self_of_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {F : Ω → ℝ} {N : ℕ}
    (hFmeas : AEStronglyMeasurable[ℱ N] F μ)
    (hFint : Integrable F μ) :
    doobM μ ℱ F N =ᵐ[μ] F := by
  dsimp [doobM]
  exact condExp_of_aestronglyMeasurable' (ℱ.le N) hFmeas hFint

/-- The first `N + 1` Doob differences telescope to the centered function
whenever the function is measurable at filtration level `N`. -/
lemma doobDiff_sum_range_succ_ae_eq_centered {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {F : Ω → ℝ} {N : ℕ}
    (hFmeas : AEStronglyMeasurable[ℱ N] F μ)
    (hFint : Integrable F μ) :
    (fun ω => ∑ i ∈ Finset.range (N + 1), doobDiff μ ℱ F i ω)
      =ᵐ[μ] fun ω => F ω - ∫ ω, F ω ∂μ := by
  have hM := doobM_ae_eq_self_of_aestronglyMeasurable (μ := μ) ℱ hFmeas hFint
  filter_upwards [hM] with ω hω
  rw [doobDiff_sum_range_succ]
  rw [hω]

/-- Every non-initial Doob difference has zero conditional mean with respect
to the previous filtration level, expressed through the regular conditional
expectation kernel. -/
lemma doobDiff_cond_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) {F : Ω → ℝ} (i : ℕ) :
    ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
      ∫ ω, doobDiff μ ℱ F (i + 1) ω
        ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω') = 0 := by
  let Y : Ω → ℝ := doobDiff μ ℱ F (i + 1)
  have hYint : Integrable Y μ := by
    dsimp [Y, doobDiff]
    exact integrable_condExp.sub integrable_condExp
  have hkernel :=
    condExp_ae_eq_trim_integral_condExpKernel (μ := μ) (m := ℱ i)
      (hm := ℱ.le i) hYint
  have hcond_mu : μ[Y | ℱ i] =ᵐ[μ] 0 := by
    dsimp [Y, doobDiff]
    have hsub := condExp_sub (μ := μ)
      (f := doobM μ ℱ F (i + 1)) (g := doobM μ ℱ F i)
      integrable_condExp integrable_condExp (ℱ i)
    have htower1 := MeasureTheory.Filtration.condExp_condExp (μ := μ) F ℱ (Nat.le_succ i)
    have htower0 := MeasureTheory.Filtration.condExp_condExp (μ := μ) F ℱ (le_rfl : i ≤ i)
    filter_upwards [hsub, htower1, htower0] with ω hs h1 h0
    change μ[doobM μ ℱ F (i + 1) - doobM μ ℱ F i | ℱ i] ω = 0
    rw [hs]
    change μ[μ[F | ℱ (i + 1)] | ℱ i] ω - μ[μ[F | ℱ i] | ℱ i] ω = 0
    have h1' : μ[μ[F | ℱ (i + 1)] | ℱ i] ω = μ[F | ℱ i] ω := by
      simpa using h1
    rw [h1', h0]
    simp
  have hcond_trim : μ[Y | ℱ i] =ᵐ[μ.trim (ℱ.le i)] 0 := by
    exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable (ℱ.le i)
      stronglyMeasurable_condExp stronglyMeasurable_zero hcond_mu
  filter_upwards [hkernel, hcond_trim] with ω' hk hz
  rw [← hk, hz]
  simp

/-- Azuma-Hoeffding/McDiarmid martingale-difference form with the exact
bounded-differences exponent `exp(-2t²/∑ᵢ cᵢ²)`.  This is the concentration
engine used in HDP Theorem 2.9.1 once the Doob martingale differences of a
coordinate-Lipschitz function are identified. -/
theorem mcdiarmid_martingale_difference_upper_tail
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {c : ℕ → ℝ} {n : ℕ} {t : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) (boundedDifferencesSubgaussianProxy c 0) μ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (boundedDifferencesSubgaussianProxy c (i + 1)) μ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c n) := by
  have htail :=
    ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
      (μ := μ) (Y := Y) (cY := boundedDifferencesSubgaussianProxy c)
      (ℱ := ℱ) h_adapted h0 n h_subG ht
  calc
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
        ≤ Real.exp (-t ^ 2 /
          (2 * ∑ i ∈ Finset.range n, boundedDifferencesSubgaussianProxy c i)) := htail
    _ = Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c n) := by
      congr 1
      have hsumproxy :
          ((∑ i ∈ Finset.range n, boundedDifferencesSubgaussianProxy c i : ℝ≥0) : ℝ)
            = boundedDifferencesVarianceSum c n / 4 := by
        calc
          ((∑ i ∈ Finset.range n, boundedDifferencesSubgaussianProxy c i : ℝ≥0) : ℝ)
              = ∑ i ∈ Finset.range n,
                  ((boundedDifferencesSubgaussianProxy c i : ℝ≥0) : ℝ) := by
            simp
          _ = ∑ i ∈ Finset.range n, c i ^ 2 / 4 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rfl
          _ = boundedDifferencesVarianceSum c n / 4 := by
            dsimp [boundedDifferencesVarianceSum]
            rw [Finset.sum_div]
      rw [hsumproxy]
      ring

/-- Bounded martingale-difference form of HDP Theorem 2.9.1.  If the increments
are adapted, globally bounded in intervals of length `cᵢ`, and have zero
conditional means with respect to the previous filtration level, then the
McDiarmid/Azuma exponent is exactly `exp(-2 t² / ∑ᵢ cᵢ²)`. -/
theorem mcdiarmid_martingale_difference_bounded_upper_tail
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {a c : ℕ → ℝ} {n : ℕ} {t : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (hc : ∀ i, 0 ≤ c i)
    (hYm : ∀ i, AEMeasurable (Y i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (a i) (a i + c i))
    (hmean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (hcond_meas : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (Y (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          Y (i + 1) ω ∈ Set.Icc (a (i + 1)) (a (i + 1) + c (i + 1)))
    (hcond_mean : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∫ ω, Y (i + 1) ω
          ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
            (ℱ i)) ω') = 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c n) := by
  have proxy_eq (i : ℕ) :
      ((‖(a i + c i) - a i‖₊ / 2) ^ 2 : ℝ≥0) =
        boundedDifferencesSubgaussianProxy c i := by
    ext
    have hdiff : a i + c i - a i = c i := by ring
    rw [hdiff]
    change ((‖c i‖₊ : ℝ) / 2) ^ 2 = c i ^ 2 / 4
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hc i)]
    ring
  have proxy_eq' (i : ℕ) :
      ((‖c i‖₊ / 2) ^ 2 : ℝ≥0) =
        boundedDifferencesSubgaussianProxy c i := by
    simpa using proxy_eq i
  have h0 :
      HasSubgaussianMGF (Y 0) (boundedDifferencesSubgaussianProxy c 0) μ := by
    have h :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (μ := μ) (X := Y 0) (a := a 0) (b := a 0 + c 0)
        (hYm 0) (hbound 0) hmean0
    simpa [proxy_eq' 0] using h
  have h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (boundedDifferencesSubgaussianProxy c (i + 1)) μ := by
    intro i hi
    have h :=
      hasCondSubgaussianMGF_of_cond_mem_Icc_of_cond_integral_eq_zero
        (μ := μ) (m := ℱ i) (hm := ℱ.le i)
        (X := Y (i + 1)) (a := a (i + 1)) (b := a (i + 1) + c (i + 1))
        (hYm (i + 1)) (hbound (i + 1))
        (hcond_meas i hi) (hcond_bound i hi) (hcond_mean i hi)
    simpa [proxy_eq' (i + 1)] using h
  exact mcdiarmid_martingale_difference_upper_tail
    (μ := μ) (Y := Y) (ℱ := ℱ) (c := c) (n := n) (t := t)
    h_adapted h0 h_subG ht

/-- Bounded martingale-difference McDiarmid form with past-dependent interval
locations.  This is the form naturally produced by the Doob martingale of a
bounded-differences function: after conditioning on the past, the next
increment is centered and lies in some interval of deterministic length `cᵢ`,
but the interval's left endpoint may depend on the past. -/
theorem mcdiarmid_martingale_difference_conditional_range_upper_tail
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {c : ℕ → ℝ} {n : ℕ} {t : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (hc : ∀ i, 0 ≤ c i)
    (hc0 : c 0 = 0)
    (hYm : ∀ i, AEMeasurable (Y i) μ)
    (hglobal_abs : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ c i)
    (h0_zero : Y 0 =ᵐ[μ] 0)
    (hcond_meas : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (Y (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          Y (i + 1) ω ∈ Set.Icc a (a + c (i + 1)))
    (hcond_mean : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∫ ω, Y (i + 1) ω
          ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
            (ℱ i)) ω') = 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c n) := by
  have proxy_eq (i : ℕ) :
      ((‖c i‖₊ / 2) ^ 2 : ℝ≥0) =
        boundedDifferencesSubgaussianProxy c i := by
    ext
    change ((‖c i‖₊ : ℝ) / 2) ^ 2 = c i ^ 2 / 4
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hc i)]
    ring
  have h0 :
      HasSubgaussianMGF (Y 0) (boundedDifferencesSubgaussianProxy c 0) μ := by
    have hzero : HasSubgaussianMGF (0 : Ω → ℝ) 0 μ := by simp
    have hY0 : HasSubgaussianMGF (Y 0) 0 μ :=
      hzero.congr h0_zero.symm
    simpa [boundedDifferencesSubgaussianProxy, hc0] using hY0
  have h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (boundedDifferencesSubgaussianProxy c (i + 1)) μ := by
    intro i hi
    have h :=
      hasCondSubgaussianMGF_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero
        (μ := μ) (m := ℱ i) (hm := ℱ.le i)
        (X := Y (i + 1)) (c := c (i + 1))
        (hc (i + 1)) (hYm (i + 1)) (hglobal_abs (i + 1))
        (hcond_meas i hi) (hcond_bound i hi) (hcond_mean i hi)
    simpa [proxy_eq (i + 1)] using h
  exact mcdiarmid_martingale_difference_upper_tail
    (μ := μ) (Y := Y) (ℱ := ℱ) (c := c) (n := n) (t := t)
    h_adapted h0 h_subG ht

/-- Conditional-range martingale-difference McDiarmid form with the global
absolute bound derived from measurable increments, conditional interval
ranges, and zero conditional means. -/
theorem mcdiarmid_martingale_difference_conditional_range_upper_tail_of_measurable
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {c : ℕ → ℝ} {n : ℕ} {t : ℝ}
    (h_adapted : StronglyAdapted ℱ Y)
    (hc : ∀ i, 0 ≤ c i)
    (hc0 : c 0 = 0)
    (hYm : ∀ i, Measurable (Y i))
    (h0_zero : Y 0 =ᵐ[μ] 0)
    (hcond_meas : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (Y (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          Y (i + 1) ω ∈ Set.Icc a (a + c (i + 1)))
    (hcond_mean : ∀ i < n - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∫ ω, Y (i + 1) ω
          ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
            (ℱ i)) ω') = 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c n) := by
  have proxy_eq (i : ℕ) :
      ((‖c i‖₊ / 2) ^ 2 : ℝ≥0) =
        boundedDifferencesSubgaussianProxy c i := by
    ext
    change ((‖c i‖₊ : ℝ) / 2) ^ 2 = c i ^ 2 / 4
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (hc i)]
    ring
  have h0 :
      HasSubgaussianMGF (Y 0) (boundedDifferencesSubgaussianProxy c 0) μ := by
    have hzero : HasSubgaussianMGF (0 : Ω → ℝ) 0 μ := by simp
    have hY0 : HasSubgaussianMGF (Y 0) 0 μ :=
      hzero.congr h0_zero.symm
    simpa [boundedDifferencesSubgaussianProxy, hc0] using hY0
  have h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (boundedDifferencesSubgaussianProxy c (i + 1)) μ := by
    intro i hi
    have h :=
      hasCondSubgaussianMGF_of_cond_exists_mem_Icc_length_of_cond_integral_eq_zero_of_measurable
        (μ := μ) (m := ℱ i) (hm := ℱ.le i)
        (X := Y (i + 1)) (c := c (i + 1))
        (hc (i + 1)) (hYm (i + 1))
        (hcond_meas i hi) (hcond_bound i hi) (hcond_mean i hi)
    simpa [proxy_eq (i + 1)] using h
  exact mcdiarmid_martingale_difference_upper_tail
    (μ := μ) (Y := Y) (ℱ := ℱ) (c := c) (n := n) (t := t)
    h_adapted h0 h_subG ht

/-- Doob-process McDiarmid form.  Once the Doob increments of `F` are known
to have zero first increment and conditionally centered ranges of deterministic
lengths `cᵢ`, the martingale tail bound applies directly to the centered
function `F - E F`. -/
theorem mcdiarmid_doob_conditional_range_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {F : Ω → ℝ}
    {c : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hFmeas : AEStronglyMeasurable[ℱ N] F μ)
    (hFint : Integrable F μ)
    (hc : ∀ i, 0 ≤ c i)
    (hc0 : c 0 = 0)
    (h0_zero : doobDiff μ ℱ F 0 =ᵐ[μ] 0)
    (hglobal_abs : ∀ i, ∀ᵐ ω ∂μ, |doobDiff μ ℱ F i ω| ≤ c i)
    (hcond_meas : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (doobDiff μ ℱ F (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          doobDiff μ ℱ F (i + 1) ω ∈ Set.Icc a (a + c (i + 1)))
    (hcond_mean : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∫ ω, doobDiff μ ℱ F (i + 1) ω
          ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
            (ℱ i)) ω') = 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ F ω - ∫ ω, F ω ∂μ}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c (N + 1)) := by
  let Y : ℕ → Ω → ℝ := doobDiff μ ℱ F
  have h_adapted : StronglyAdapted ℱ Y := doobDiff_stronglyAdapted μ ℱ F
  have hYm : ∀ i, AEMeasurable (Y i) μ := by
    intro i
    exact ((h_adapted i).mono (ℱ.le i)).aemeasurable (μ := μ)
  have htail :=
    mcdiarmid_martingale_difference_conditional_range_upper_tail
      (μ := μ) (Y := Y) (ℱ := ℱ) (c := c) (n := N + 1) (t := t)
      h_adapted hc hc0 hYm hglobal_abs h0_zero
      hcond_meas hcond_bound hcond_mean ht
  have hsum := doobDiff_sum_range_succ_ae_eq_centered (μ := μ) ℱ hFmeas hFint
  have hevent : {ω | t ≤ ∑ i ∈ Finset.range (N + 1), Y i ω}
      =ᵐ[μ] {ω | t ≤ F ω - ∫ ω, F ω ∂μ} := by
    filter_upwards [hsum] with ω hω
    dsimp [Y] at hω ⊢
    change (t ≤ ∑ i ∈ Finset.range (N + 1), doobDiff μ ℱ F i ω) =
      (t ≤ F ω - ∫ ω, F ω ∂μ)
    rw [hω]
  rw [← MeasureTheory.measureReal_congr hevent]
  exact htail

/-- Doob-process McDiarmid form with the zero conditional means supplied by
the Doob tower property.  It remains only to provide the conditional interval
locations and global absolute bounds for the increments. -/
theorem mcdiarmid_doob_conditional_range_upper_tail_of_ranges
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {F : Ω → ℝ}
    {c : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hFmeas : AEStronglyMeasurable[ℱ N] F μ)
    (hFint : Integrable F μ)
    (hc : ∀ i, 0 ≤ c i)
    (hc0 : c 0 = 0)
    (h0_zero : doobDiff μ ℱ F 0 =ᵐ[μ] 0)
    (hglobal_abs : ∀ i, ∀ᵐ ω ∂μ, |doobDiff μ ℱ F i ω| ≤ c i)
    (hcond_meas : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (doobDiff μ ℱ F (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          doobDiff μ ℱ F (i + 1) ω ∈ Set.Icc a (a + c (i + 1)))
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ F ω - ∫ ω, F ω ∂μ}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c (N + 1)) := by
  refine mcdiarmid_doob_conditional_range_upper_tail
    (μ := μ) (ℱ := ℱ) (F := F) (c := c) (N := N) (t := t)
    hFmeas hFint hc hc0 h0_zero hglobal_abs hcond_meas hcond_bound ?_ ht
  intro i _hi
  exact doobDiff_cond_integral_eq_zero (μ := μ) ℱ i

/-- Doob-process McDiarmid form with global absolute bounds derived from
conditional interval ranges and zero conditional means. -/
theorem mcdiarmid_doob_conditional_range_upper_tail_of_ranges_measurable
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {F : Ω → ℝ}
    {c : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hFmeas : AEStronglyMeasurable[ℱ N] F μ)
    (hFint : Integrable F μ)
    (hc : ∀ i, 0 ≤ c i)
    (hc0 : c 0 = 0)
    (h0_zero : doobDiff μ ℱ F 0 =ᵐ[μ] 0)
    (hcond_meas : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        AEMeasurable (doobDiff μ ℱ F (i + 1))
          ((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance (ℱ i)) ω'))
    (hcond_bound : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ ω ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
          (ℱ i)) ω'),
          doobDiff μ ℱ F (i + 1) ω ∈ Set.Icc a (a + c (i + 1)))
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ F ω - ∫ ω, F ω ∂μ}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c (N + 1)) := by
  let Y : ℕ → Ω → ℝ := doobDiff μ ℱ F
  have h_adapted : StronglyAdapted ℱ Y := doobDiff_stronglyAdapted μ ℱ F
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    exact ((h_adapted i).mono (ℱ.le i)).measurable
  have hcond_mean : ∀ i < (N + 1) - 1,
      ∀ᵐ ω' ∂(μ.trim (ℱ.le i)),
        ∫ ω, Y (i + 1) ω
          ∂((@condExpKernel Ω ‹MeasurableSpace Ω› inferInstance μ inferInstance
            (ℱ i)) ω') = 0 := by
    intro i _hi
    exact doobDiff_cond_integral_eq_zero (μ := μ) ℱ i
  have htail := mcdiarmid_martingale_difference_conditional_range_upper_tail_of_measurable
    (μ := μ) (Y := Y) (ℱ := ℱ) (c := c) (n := N + 1) (t := t)
    h_adapted hc hc0 hYm h0_zero hcond_meas hcond_bound hcond_mean ht
  have hsum := doobDiff_sum_range_succ_ae_eq_centered (μ := μ) ℱ hFmeas hFint
  have hevent : {ω | t ≤ ∑ i ∈ Finset.range (N + 1), Y i ω}
      =ᵐ[μ] {ω | t ≤ F ω - ∫ ω, F ω ∂μ} := by
    filter_upwards [hsum] with ω hω
    dsimp [Y] at hω ⊢
    change (t ≤ ∑ i ∈ Finset.range (N + 1), doobDiff μ ℱ F i ω) =
      (t ≤ F ω - ∫ ω, F ω ∂μ)
    rw [hω]
  rw [← MeasureTheory.measureReal_congr hevent]
  exact htail

/-- Shifted independent-product McDiarmid form reduced to a pointwise diameter
condition for the trajectory Doob representatives.  The remaining
book-specific step is to prove this diameter condition from the coordinate
bounded-differences hypothesis on the original function. -/
theorem mcdiarmid_shifted_doob_of_trajDiff_diameter {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {F : ((n : ℕ) → shiftedSeqType X n) → ℝ}
    {c : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hFmeas : AEStronglyMeasurable[MeasureTheory.Filtration.piLE (X := shiftedSeqType X) N]
      F (shiftedIndependentTraj (X := X) μ))
    (hFint : Integrable F (shiftedIndependentTraj (X := X) μ))
    (hc : ∀ i, 0 ≤ c i)
    (hglobal_abs : ∀ i, ∀ᵐ z ∂(shiftedIndependentTraj (X := X) μ),
      |doobDiff (shiftedIndependentTraj (X := X) μ)
        (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F i z| ≤
        shiftedBoundedDifferenceConstants c i)
    (hcond_meas : ∀ i < N,
      ∀ᵐ z ∂((shiftedIndependentTraj (X := X) μ).trim
        ((MeasureTheory.Filtration.piLE (X := shiftedSeqType X)).le i)),
        AEMeasurable
          (doobDiff (shiftedIndependentTraj (X := X) μ)
            (MeasureTheory.Filtration.piLE (X := shiftedSeqType X)) F (i + 1))
          ((@condExpKernel _ _ inferInstance (shiftedIndependentTraj (X := X) μ)
            inferInstance (MeasureTheory.Filtration.piLE (X := shiftedSeqType X) i)) z))
    (hdiam : ∀ i < N, ∀ z w,
      Preorder.frestrictLe i z = Preorder.frestrictLe i w →
        |shiftedTrajDiff μ F (i + 1) z - shiftedTrajDiff μ F (i + 1) w| ≤ c i)
    (ht : 0 ≤ t) :
    (shiftedIndependentTraj (X := X) μ).real
        {z | t ≤ F z - ∫ z, F z ∂(shiftedIndependentTraj (X := X) μ)}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c N) := by
  let P := shiftedIndependentTraj (X := X) μ
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace ((n : ℕ) → shiftedSeqType X n)) :=
    MeasureTheory.Filtration.piLE (X := shiftedSeqType X)
  let c' := shiftedBoundedDifferenceConstants c
  have hc' : ∀ i, 0 ≤ c' i := shiftedBoundedDifferenceConstants_nonneg hc
  have hc0 : c' 0 = 0 := rfl
  have h0_zero : doobDiff P ℱ F 0 =ᵐ[P] 0 := by
    simpa [P, ℱ] using doobDiff_shifted_zero_ae_eq_zero (X := X) μ hFint
  have hcond_bound : ∀ i < (N + 1) - 1,
      ∀ᵐ z ∂(P.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ y ∂((@condExpKernel _ _ inferInstance P inferInstance (ℱ i)) z),
          doobDiff P ℱ F (i + 1) y ∈ Set.Icc a (a + c' (i + 1)) := by
    intro i hi
    have hiN : i < N := by omega
    have h := doobDiff_shifted_conditional_range_of_trajDiff_diameter
      (X := X) μ hFint (hc i) i (hdiam i hiN)
    simpa [P, ℱ, c'] using h
  have hcond_meas' : ∀ i < (N + 1) - 1,
      ∀ᵐ z ∂(P.trim (ℱ.le i)),
        AEMeasurable (doobDiff P ℱ F (i + 1))
          ((@condExpKernel _ _ inferInstance P inferInstance (ℱ i)) z) := by
    intro i hi
    have hiN : i < N := by omega
    simpa [P, ℱ] using hcond_meas i hiN
  have htail := mcdiarmid_doob_conditional_range_upper_tail_of_ranges
    (μ := P) (ℱ := ℱ) (F := F) (c := c') (N := N) (t := t)
    hFmeas hFint hc' hc0 h0_zero hglobal_abs hcond_meas' hcond_bound ht
  simpa [P, c', boundedDifferencesVarianceSum_shifted_succ] using htail

/-- HDP Theorem 2.9.1 in the shifted independent-product model.  A
measurable function of the first `N` genuine independent coordinates satisfying
coordinate bounded differences obeys McDiarmid's upper-tail bound with the
book exponent `exp (-2 t² / ∑ᵢ cᵢ²)`. -/
theorem mcdiarmid_shifted_boundedDifferences {X : ℕ → Type u}
    [∀ n, MeasurableSpace (X n)] [∀ n, StandardBorelSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    {f : ((n : ℕ) → X n) → ℝ} {c : ℕ → ℝ} {N : ℕ} {t : ℝ}
    (hdep : DependsOn f (Set.Iio N))
    (hbd : SeqBoundedDifferences f c N)
    (hFmeas : Measurable (shiftedFunction f))
    (hc : ∀ i, 0 ≤ c i)
    (ht : 0 ≤ t) :
    (shiftedIndependentTraj (X := X) μ).real
        {z | t ≤ shiftedFunction f z - ∫ z, shiftedFunction f z ∂(shiftedIndependentTraj (X := X) μ)}
      ≤ Real.exp (-2 * t ^ 2 / boundedDifferencesVarianceSum c N) := by
  haveI : ∀ n, Nonempty (X n) := fun n => nonempty_of_isProbabilityMeasure (μ n)
  let P := shiftedIndependentTraj (X := X) μ
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace ((n : ℕ) → shiftedSeqType X n)) :=
    MeasureTheory.Filtration.piLE (X := shiftedSeqType X)
  let F : ((n : ℕ) → shiftedSeqType X n) → ℝ := shiftedFunction f
  let c' := shiftedBoundedDifferenceConstants c
  have hFdep : DependsOn F (Set.Iic N) := shiftedFunction_dependsOn (X := X) (f := f) hdep
  have hFmeasN : AEStronglyMeasurable[ℱ N] F P := by
    dsimp [ℱ, F]
    exact aestronglyMeasurable_piLE_of_dependsOn (X := shiftedSeqType X)
      (F := shiftedFunction f) (N := N) (μ := P) hFdep hFmeas
  have hFint : Integrable F P := by
    dsimp [F, P]
    exact shiftedFunction_integrable_of_boundedDifferences (X := X)
      (ν := shiftedIndependentTraj (X := X) μ) hdep hbd hFmeas
  have hc' : ∀ i, 0 ≤ c' i := shiftedBoundedDifferenceConstants_nonneg hc
  have hc0 : c' 0 = 0 := rfl
  have h0_zero : doobDiff P ℱ F 0 =ᵐ[P] 0 := by
    dsimp [P, ℱ, F]
    simpa using doobDiff_shifted_zero_ae_eq_zero (X := X) μ hFint
  have hcond_meas : ∀ i < (N + 1) - 1,
      ∀ᵐ z ∂(P.trim (ℱ.le i)),
        AEMeasurable (doobDiff P ℱ F (i + 1))
          ((@condExpKernel _ _ inferInstance P inferInstance (ℱ i)) z) := by
    intro i _hi
    have hYmeas : Measurable (doobDiff P ℱ F (i + 1)) := by
      exact (((doobDiff_stronglyAdapted P ℱ F) (i + 1)).mono (ℱ.le (i + 1))).measurable
    filter_upwards with z
    exact hYmeas.aemeasurable
  have hcond_bound : ∀ i < (N + 1) - 1,
      ∀ᵐ z ∂(P.trim (ℱ.le i)),
        ∃ a : ℝ, ∀ᵐ y ∂((@condExpKernel _ _ inferInstance P inferInstance (ℱ i)) z),
          doobDiff P ℱ F (i + 1) y ∈ Set.Icc a (a + c' (i + 1)) := by
    intro i hi
    have hiN : i < N := by omega
    have hdiam : ∀ z w,
      Preorder.frestrictLe i z = Preorder.frestrictLe i w →
        |shiftedTrajDiff μ F (i + 1) z - shiftedTrajDiff μ F (i + 1) w| ≤ c i := by
      intro z w hzw
      dsimp [F]
      exact shiftedTrajDiff_diameter_of_boundedDifferences (X := X) μ
        (f := f) (c := c) (N := N) (i := i) hdep hbd hFmeas hiN hzw
    have h := doobDiff_shifted_conditional_range_of_trajDiff_diameter
      (X := X) μ hFint (hc i) i hdiam
    simpa [P, ℱ, F, c'] using h
  have htail := mcdiarmid_doob_conditional_range_upper_tail_of_ranges_measurable
    (μ := P) (ℱ := ℱ) (F := F) (c := c') (N := N) (t := t)
    hFmeasN hFint hc' hc0 h0_zero hcond_meas hcond_bound ht
  simpa [P, F, c', boundedDifferencesVarianceSum_shifted_succ] using htail

/-- Section 2.8 Bernstein MGF spine, upper tail: if every summand satisfies
the local signed MGF estimate at `θ`, then the independent sum satisfies the
corresponding Chernoff bound. -/
theorem bernstein_mgf_sum_upper_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {θ t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ (K i))
    (hθ_nonneg : 0 ≤ θ)
    (hθ_window : ∀ i, |θ| ≤ 1 / K i) :
    μ.real {ω | t ≤ ∑ i, X i ω}
      ≤ Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  have h_each_int :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun ω => Real.exp (θ * X i ω)) μ := by
    intro i _hi
    exact ((hX i).2 θ (hθ_window i)).1
  have hsum_int :
      Integrable (fun ω => Real.exp (θ * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := θ) hXm (s := (Finset.univ : Finset ι)) h_each_int
    simpa [S, Finset.sum_apply] using h
  have htail :
      μ.real {ω | t ≤ S ω}
        ≤ Real.exp (-θ * t) * mgf S μ θ := by
    simpa [mgf] using
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := S) t hθ_nonneg hsum_int
  have hmgf_sum :
      mgf S μ θ = ∏ i, mgf (X i) μ θ := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), X i) μ θ =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (X i) μ θ :=
      hindep.mgf_sum (t := θ) hXm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le :
      mgf S μ θ ≤
        Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
    calc
      mgf S μ θ = ∏ i, mgf (X i) μ θ := hmgf_sum
      _ ≤ ∏ i, Real.exp (K i ^ 2 * θ ^ 2) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact ((hX i).2 θ (hθ_window i)).2
      _ = Real.exp (∑ i, K i ^ 2 * θ ^ 2) := by
        rw [Real.exp_sum]
      _ = Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
        congr 1
        unfold subExponentialVarianceProxySum
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  calc
    μ.real {ω | t ≤ ∑ i, X i ω}
        = μ.real {ω | t ≤ S ω} := by simp [S]
    _ ≤ Real.exp (-θ * t) * mgf S μ θ := htail
    _ ≤ Real.exp (-θ * t)
        * Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
      exact mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
    _ = Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
      rw [Real.exp_add]

/-- Section 2.8 Bernstein MGF spine, lower tail. -/
theorem bernstein_mgf_sum_lower_tail
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {θ t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ (K i))
    (hθ_nonneg : 0 ≤ θ)
    (hθ_window : ∀ i, |θ| ≤ 1 / K i) :
    μ.real {ω | ∑ i, X i ω ≤ -t}
      ≤ Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let η : ℝ := -θ
  have hη_nonpos : η ≤ 0 := by
    dsimp [η]
    exact neg_nonpos.mpr hθ_nonneg
  have hη_window : ∀ i, |η| ≤ 1 / K i := by
    intro i
    simpa [η, abs_neg] using hθ_window i
  have h_each_int :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun ω => Real.exp (η * X i ω)) μ := by
    intro i _hi
    exact ((hX i).2 η (hη_window i)).1
  have hsum_int :
      Integrable (fun ω => Real.exp (η * S ω)) μ := by
    have h :=
      hindep.integrable_exp_mul_sum
        (t := η) hXm (s := (Finset.univ : Finset ι)) h_each_int
    simpa [S, Finset.sum_apply] using h
  have htail :
      μ.real {ω | S ω ≤ -t}
        ≤ Real.exp (-η * (-t)) * mgf S μ η := by
    simpa [mgf] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := μ) (X := S) (-t) hη_nonpos hsum_int
  have hmgf_sum :
      mgf S μ η = ∏ i, mgf (X i) μ η := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), X i) μ η =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (X i) μ η :=
      hindep.mgf_sum (t := η) hXm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, X i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le :
      mgf S μ η ≤
        Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
    calc
      mgf S μ η = ∏ i, mgf (X i) μ η := hmgf_sum
      _ ≤ ∏ i, Real.exp (K i ^ 2 * η ^ 2) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact ((hX i).2 η (hη_window i)).2
      _ = Real.exp (∑ i, K i ^ 2 * η ^ 2) := by
        rw [Real.exp_sum]
      _ = Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
        congr 1
        unfold subExponentialVarianceProxySum
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          dsimp [η]
          ring
  calc
    μ.real {ω | ∑ i, X i ω ≤ -t}
        = μ.real {ω | S ω ≤ -t} := by simp [S]
    _ ≤ Real.exp (-η * (-t)) * mgf S μ η := htail
    _ ≤ Real.exp (-η * (-t))
        * Real.exp (θ ^ 2 * subExponentialVarianceProxySum K) := by
      exact mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
    _ = Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
      dsimp [η]
      rw [Real.exp_add]
      ring_nf

/-- Section 2.8 Bernstein MGF spine, two-sided tail. -/
theorem bernstein_mgf_sum_two_sided
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {θ t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ (K i))
    (hθ_nonneg : 0 ≤ θ)
    (hθ_window : ∀ i, |θ| ≤ 1 / K i) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let A : Set Ω := {ω | t ≤ S ω}
  let B : Set Ω := {ω | S ω ≤ -t}
  have hsubset : {ω | t ≤ |∑ i, X i ω|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hnonneg : 0 ≤ S ω
    · left
      dsimp [A, S] at *
      simpa [abs_of_nonneg hnonneg] using hω
    · right
      have hneg : S ω < 0 := lt_of_not_ge hnonneg
      have hle : S ω ≤ -t := by
        have hAbs : t ≤ -(S ω) := by
          have hωS : t ≤ |S ω| := by
            simpa [S] using hω
          simpa [abs_of_neg hneg] using hωS
        linarith
      exact hle
  have hupper :
      μ.real A ≤ Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
    dsimp [A, S]
    exact bernstein_mgf_sum_upper_tail
      (μ := μ) (X := X) (K := K) (θ := θ) (t := t)
      hindep hXm hX hθ_nonneg hθ_window
  have hlower :
      μ.real B ≤ Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
    dsimp [B, S]
    exact bernstein_mgf_sum_lower_tail
      (μ := μ) (X := X) (K := K) (θ := θ) (t := t)
      hindep hXm hX hθ_nonneg hθ_window
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ μ.real (A ∪ B) :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ μ.real A + μ.real B :=
      MeasureTheory.measureReal_union_le A B
    _ ≤ Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K)
        + Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := by
      ring

/-- Scalar optimization for Bernstein's Chernoff parameter. -/
lemma bernstein_mgf_exponent_optimized
    {t V M θ : ℝ}
    (ht : 0 ≤ t) (hV : 0 < V) (hM : 0 < M)
    (hθ : θ = min (t / (2 * V)) (1 / (2 * M))) :
    -θ * t + θ ^ 2 * V
      ≤ -(1 / 4 : ℝ) * min (t ^ 2 / V) (t / M) := by
  by_cases hcase : t / (2 * V) ≤ 1 / (2 * M)
  · have hθval : θ = t / (2 * V) := by
      rw [hθ, min_eq_left hcase]
    have hcase' : t * M ≤ V := by
      have hdenV : 0 < 2 * V := by positivity
      have hdenM : 0 < 2 * M := by positivity
      rw [div_le_div_iff₀ hdenV hdenM] at hcase
      nlinarith
    have hmin : min (t ^ 2 / V) (t / M) = t ^ 2 / V := by
      rw [min_eq_left]
      by_cases ht0 : t = 0
      · simp [ht0]
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        rw [div_le_div_iff₀ hV hM]
        nlinarith
    rw [hθval, hmin]
    field_simp [hV.ne']
    ring_nf
    exact le_rfl
  · have hθval : θ = 1 / (2 * M) := by
      rw [hθ, min_eq_right (le_of_not_ge hcase)]
    have hcase_lt : V < t * M := by
      have hlt : 1 / (2 * M) < t / (2 * V) := lt_of_not_ge hcase
      have hdenM : 0 < 2 * M := by positivity
      have hdenV : 0 < 2 * V := by positivity
      rw [div_lt_div_iff₀ hdenM hdenV] at hlt
      nlinarith
    have htpos : 0 < t := by
      by_contra hnot
      have htle : t ≤ 0 := le_of_not_gt hnot
      have ht0 : t = 0 := le_antisymm htle ht
      subst ht0
      nlinarith [hV, hM]
    have hmin : min (t ^ 2 / V) (t / M) = t / M := by
      rw [min_eq_right]
      rw [div_le_div_iff₀ hM hV]
      nlinarith
    rw [hθval, hmin]
    have hineq : V / (4 * M ^ 2) ≤ t / (4 * M) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 4 * M ^ 2)
        (by positivity : 0 < 4 * M)]
      nlinarith
    calc
      -(1 / (2 * M)) * t + (1 / (2 * M)) ^ 2 * V
          = -t / (2 * M) + V / (4 * M ^ 2) := by
        field_simp [hM.ne']
        ring
      _ ≤ -t / (2 * M) + t / (4 * M) := by
        linarith
      _ = -(1 / 4 : ℝ) * (t / M) := by
        field_simp [hM.ne']
        ring

/-- Optimized Bernstein bound from local signed MGF control.  This is the
book's Bernstein min-structure at the MGF-hypothesis level; converting the
hypotheses from `ψ₁` norms is handled separately by Proposition 2.7.1(e). -/
theorem bernstein_mgf_sum_two_sided_optimized
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {M t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ (K i))
    (hKpos : ∀ i, 0 < K i)
    (hMpos : 0 < M)
    (hKM : ∀ i, K i ≤ M)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
        min (t ^ 2 / subExponentialVarianceProxySum K) (t / M)) := by
  classical
  let V : ℝ := subExponentialVarianceProxySum K
  have hVpos : 0 < V := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < K i0 ^ 2 := sq_pos_of_pos (hKpos i0)
    have hterm_le :
        K i0 ^ 2 ≤ ∑ i, K i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (K i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [V, subExponentialVarianceProxySum] using hterm_le)
  let θ : ℝ := min (t / (2 * V)) (1 / (2 * M))
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ]
    exact le_min
      (div_nonneg ht (by positivity : 0 ≤ 2 * V))
      (by positivity)
  have hθ_le_one_div_M : θ ≤ 1 / M := by
    calc
      θ ≤ 1 / (2 * M) := by
        dsimp [θ]
        exact min_le_right _ _
      _ ≤ 1 / M := by
        have h2M : 0 < 2 * M := by positivity
        exact (one_div_le_one_div h2M hMpos).mpr (by nlinarith)
  have hθ_window : ∀ i, |θ| ≤ 1 / K i := by
    intro i
    rw [abs_of_nonneg hθ_nonneg]
    have hMKi : 1 / M ≤ 1 / K i :=
      (one_div_le_one_div hMpos (hKpos i)).mpr (hKM i)
    exact hθ_le_one_div_M.trans hMKi
  have htail :=
    bernstein_mgf_sum_two_sided
      (μ := μ) (X := X) (K := K) (θ := θ) (t := t)
      hindep hXm hX hθ_nonneg hθ_window
  have hexp_arg :
      -θ * t + θ ^ 2 * subExponentialVarianceProxySum K
        ≤ -(1 / 4 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum K) (t / M) := by
    simpa [V, θ] using
      bernstein_mgf_exponent_optimized
        (t := t) (V := V) (M := M) (θ := θ) ht hVpos hMpos rfl
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ 2 * Real.exp (-θ * t + θ ^ 2 * subExponentialVarianceProxySum K) := htail
    _ ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum K) (t / M)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Constant rescaling used to pass from the centered `ψ₁` Orlicz-to-MGF
scale `8K` to Bernstein's book min-structure. -/
lemma bernstein_orlicz_exponent_rescale
    {t V M : ℝ} (ht : 0 ≤ t) (hV : 0 < V) (hM : 0 < M) :
    -(1 / 4 : ℝ) * min (t ^ 2 / (64 * V)) (t / (8 * M))
      ≤ -(1 / 256 : ℝ) * min (t ^ 2 / V) (t / M) := by
  have hscaled_le :
      (1 / 256 : ℝ) * min (t ^ 2 / V) (t / M)
        ≤ (1 / 4 : ℝ) * min (t ^ 2 / (64 * V)) (t / (8 * M)) := by
    have htarget_left :
        (1 / 256 : ℝ) * min (t ^ 2 / V) (t / M) ≤ t ^ 2 / (256 * V) := by
      have hmin := min_le_left (t ^ 2 / V) (t / M)
      calc
        (1 / 256 : ℝ) * min (t ^ 2 / V) (t / M)
            ≤ (1 / 256 : ℝ) * (t ^ 2 / V) :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)
        _ = t ^ 2 / (256 * V) := by ring
    have htarget_right :
        (1 / 256 : ℝ) * min (t ^ 2 / V) (t / M) ≤ t / (32 * M) := by
      have hmin := min_le_right (t ^ 2 / V) (t / M)
      calc
        (1 / 256 : ℝ) * min (t ^ 2 / V) (t / M)
            ≤ (1 / 256 : ℝ) * (t / M) :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)
        _ ≤ t / (32 * M) := by
          field_simp [hM.ne']
          nlinarith
    have hscaled_eq :
        (1 / 4 : ℝ) * min (t ^ 2 / (64 * V)) (t / (8 * M)) =
          min (t ^ 2 / (256 * V)) (t / (32 * M)) := by
      by_cases hcase : t ^ 2 / (64 * V) ≤ t / (8 * M)
      · rw [min_eq_left hcase]
        have hcase' : t ^ 2 / (256 * V) ≤ t / (32 * M) := by
          rw [div_le_div_iff₀ (by positivity : 0 < (256 : ℝ) * V)
            (by positivity : 0 < (32 : ℝ) * M)]
          rw [div_le_div_iff₀ (by positivity : 0 < (64 : ℝ) * V)
            (by positivity : 0 < (8 : ℝ) * M)] at hcase
          nlinarith
        rw [min_eq_left hcase']
        field_simp [hV.ne']
        ring
      · have hcase_le : t / (8 * M) ≤ t ^ 2 / (64 * V) := le_of_not_ge hcase
        rw [min_eq_right hcase_le]
        have hcase' : t / (32 * M) ≤ t ^ 2 / (256 * V) := by
          rw [div_le_div_iff₀ (by positivity : 0 < (32 : ℝ) * M)
            (by positivity : 0 < (256 : ℝ) * V)]
          rw [div_le_div_iff₀ (by positivity : 0 < (8 : ℝ) * M)
            (by positivity : 0 < (64 : ℝ) * V)] at hcase_le
          nlinarith
        rw [min_eq_right hcase']
        field_simp [hM.ne']
        ring
    rw [hscaled_eq]
    exact le_min htarget_left htarget_right
  linarith

/-- Constant rescaling for the positive-`ψ₁`-norm Bernstein corollary using
the admissible Orlicz scales `2‖Xᵢ‖ψ₁`. -/
lemma bernstein_norm_exponent_rescale
    {t V M : ℝ} (ht : 0 ≤ t) (hV : 0 < V) (hM : 0 < M) :
    -(1 / 256 : ℝ) * min (t ^ 2 / (4 * V)) (t / (2 * M))
      ≤ -(1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M) := by
  have hscaled_le :
      (1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M)
        ≤ (1 / 256 : ℝ) * min (t ^ 2 / (4 * V)) (t / (2 * M)) := by
    have hleft :
        (1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M) ≤ t ^ 2 / (1024 * V) := by
      calc
        (1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M)
            ≤ (1 / 1024 : ℝ) * (t ^ 2 / V) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        _ = t ^ 2 / (1024 * V) := by ring
    have hright :
        (1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M) ≤ t / (512 * M) := by
      calc
        (1 / 1024 : ℝ) * min (t ^ 2 / V) (t / M)
            ≤ (1 / 1024 : ℝ) * (t / M) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ ≤ t / (512 * M) := by
          field_simp [hM.ne']
          nlinarith
    have hscaled_eq :
        (1 / 256 : ℝ) * min (t ^ 2 / (4 * V)) (t / (2 * M)) =
          min (t ^ 2 / (1024 * V)) (t / (512 * M)) := by
      by_cases hcase : t ^ 2 / (4 * V) ≤ t / (2 * M)
      · rw [min_eq_left hcase]
        have hcase' : t ^ 2 / (1024 * V) ≤ t / (512 * M) := by
          rw [div_le_div_iff₀ (by positivity : 0 < (1024 : ℝ) * V)
            (by positivity : 0 < (512 : ℝ) * M)]
          rw [div_le_div_iff₀ (by positivity : 0 < (4 : ℝ) * V)
            (by positivity : 0 < (2 : ℝ) * M)] at hcase
          nlinarith
        rw [min_eq_left hcase']
        field_simp [hV.ne']
        ring
      · have hcase_le : t / (2 * M) ≤ t ^ 2 / (4 * V) := le_of_not_ge hcase
        rw [min_eq_right hcase_le]
        have hcase' : t / (512 * M) ≤ t ^ 2 / (1024 * V) := by
          rw [div_le_div_iff₀ (by positivity : 0 < (512 : ℝ) * M)
            (by positivity : 0 < (1024 : ℝ) * V)]
          rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) * M)
            (by positivity : 0 < (4 : ℝ) * V)] at hcase_le
          nlinarith
        rw [min_eq_right hcase']
        field_simp [hM.ne']
        ring
    rw [hscaled_eq]
    exact le_min hleft hright
  linarith

/-- Bernstein inequality for independent centered variables stated with
explicit admissible `ψ₁` Orlicz scales.  This is Theorem 2.8.1 in the
book's min-form with absolute constant `1/256`; replacing admissible scales by
the exact `ψ₁` norms is the remaining norm-attainment step. -/
theorem bernstein_orlicz_sum_two_sided
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K : ι → ℝ} {M t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialOrliczCondition (X i) μ (K i))
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hMpos : 0 < M)
    (hKM : ∀ i, K i ≤ M)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
        min (t ^ 2 / subExponentialVarianceProxySum K) (t / M)) := by
  classical
  let L : ι → ℝ := fun i => 8 * K i
  have hLm : ∀ i, subExponentialMGFCondition (X i) μ (L i) := by
    intro i
    exact
      subExponentialMGFCondition_of_orliczCondition_of_integral_eq_zero
        (μ := μ) (X := X i) (K := K i) (hXm i).aemeasurable (hX i) (hmean i)
  have hLpos : ∀ i, 0 < L i := by
    intro i
    exact mul_pos (by norm_num) (hX i).1
  have h8Mpos : 0 < 8 * M := by positivity
  have hLM : ∀ i, L i ≤ 8 * M := by
    intro i
    exact mul_le_mul_of_nonneg_left (hKM i) (by norm_num)
  have hV :
      subExponentialVarianceProxySum L =
        64 * subExponentialVarianceProxySum K := by
    unfold subExponentialVarianceProxySum L
    calc
      (∑ i, (8 * K i) ^ 2) = ∑ i, 64 * K i ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ = 64 * ∑ i, K i ^ 2 := by
        rw [Finset.mul_sum]
  have hVpos : 0 < subExponentialVarianceProxySum K := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < K i0 ^ 2 := sq_pos_of_pos (hX i0).1
    have hterm_le :
        K i0 ^ 2 ≤ ∑ i, K i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (K i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [subExponentialVarianceProxySum] using hterm_le)
  have htail :=
    bernstein_mgf_sum_two_sided_optimized
      (μ := μ) (X := X) (K := L) (M := 8 * M) (t := t)
      hindep hXm hLm hLpos h8Mpos hLM ht
  rw [hV] at htail
  have hexp_arg :
      -(1 / 4 : ℝ) *
          min (t ^ 2 / (64 * subExponentialVarianceProxySum K)) (t / (8 * M))
        ≤ -(1 / 256 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum K) (t / M) :=
    bernstein_orlicz_exponent_rescale
      (t := t) (V := subExponentialVarianceProxySum K) (M := M) ht hVpos hMpos
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
          min (t ^ 2 / (64 * subExponentialVarianceProxySum K)) (t / (8 * M))) := by
      simpa [mul_assoc] using htail
    _ ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum K) (t / M)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Positive-norm Bernstein inequality for independent centered
sub-exponential variables.  It avoids an infimum-attainment assumption by
using `2‖Xᵢ‖ψ₁` as admissible Orlicz scales, so the absolute constant is
`1/1024`. -/
theorem bernstein_norm_sum_two_sided_positive
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {M t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hMpos : 0 < M)
    (hNormM : ∀ i, subExponentialNorm (X i) μ ≤ M)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / subExponentialVarianceProxySum
          (fun i => subExponentialNorm (X i) μ)) (t / M)) := by
  classical
  let N : ι → ℝ := fun i => subExponentialNorm (X i) μ
  let K : ι → ℝ := fun i => 2 * N i
  have hOrlicz : ∀ i, subExponentialOrliczCondition (X i) μ (K i) := by
    intro i
    exact
      subExponentialOrliczCondition_two_mul_norm
        (μ := μ) (X := X i) (hXm i).aemeasurable (hXse i) (hNormPos i)
  have hKM : ∀ i, K i ≤ 2 * M := by
    intro i
    exact mul_le_mul_of_nonneg_left (hNormM i) (by norm_num)
  have htail :=
    bernstein_orlicz_sum_two_sided
      (μ := μ) (X := X) (K := K) (M := 2 * M) (t := t)
      hindep hXm hOrlicz hmean (by positivity) hKM ht
  have hV :
      subExponentialVarianceProxySum K =
        4 * subExponentialVarianceProxySum N := by
    unfold subExponentialVarianceProxySum K N
    calc
      (∑ i, (2 * subExponentialNorm (X i) μ) ^ 2)
          = ∑ i, 4 * subExponentialNorm (X i) μ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ = 4 * ∑ i, subExponentialNorm (X i) μ ^ 2 := by
        rw [Finset.mul_sum]
  have hVpos : 0 < subExponentialVarianceProxySum N := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < N i0 ^ 2 := sq_pos_of_pos (hNormPos i0)
    have hterm_le :
        N i0 ^ 2 ≤ ∑ i, N i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (N i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [subExponentialVarianceProxySum, N] using hterm_le)
  rw [hV] at htail
  have hexp_arg :
      -(1 / 256 : ℝ) *
          min (t ^ 2 / (4 * subExponentialVarianceProxySum N)) (t / (2 * M))
        ≤ -(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum N) (t / M) :=
    bernstein_norm_exponent_rescale
      (t := t) (V := subExponentialVarianceProxySum N) (M := M) ht hVpos hMpos
  calc
    μ.real {ω | t ≤ |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / (4 * subExponentialVarianceProxySum N)) (t / (2 * M))) := by
      simpa [N, mul_assoc] using htail
    _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum N) (t / M)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Theorem 2.8.1, zero-aware `ψ₁`-norm variance-sum form.  Zero-`ψ₁`
summands are removed using the definiteness of the `ψ₁` gauge, so the bound
keeps the variance proxy `∑ᵢ ‖Xᵢ‖ψ₁²` rather than replacing it by a common
upper bound. -/
theorem bernstein_norm_sum_two_sided
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {M t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hMpos : 0 < M)
    (hNormM : ∀ i, subExponentialNorm (X i) μ ≤ M)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / subExponentialVarianceProxySum
          (fun i => subExponentialNorm (X i) μ)) (t / M)) := by
  classical
  let N : ι → ℝ := fun i => subExponentialNorm (X i) μ
  let P : ι → Prop := fun i => 0 < N i
  by_cases hPnonempty : ∃ i, P i
  · haveI : Nonempty {i : ι // P i} := by
      rcases hPnonempty with ⟨i, hi⟩
      exact ⟨⟨i, hi⟩⟩
    let XJ : {i : ι // P i} → Ω → ℝ := fun j => X j
    have hindepJ : iIndepFun XJ μ := by
      have hpre :=
        ProbabilityTheory.iIndepFun.precomp
          (g := fun j : {i : ι // P i} => (j : ι))
          (by intro a b h; exact Subtype.ext h) hindep
      simpa [XJ] using hpre
    have htailJ :=
      bernstein_norm_sum_two_sided_positive
        (μ := μ) (ι := {i : ι // P i}) (X := XJ) (M := M) (t := t)
        hindepJ
        (fun j => hXm j)
        (fun j => hXse j)
        (fun j => by simpa [XJ] using hmean j)
        (fun j => j.property)
        hMpos
        (fun j => hNormM j)
        ht
    have hzero_ae :
        ∀ i, ¬ P i → X i =ᵐ[μ] fun _ω => (0 : ℝ) := by
      intro i hi
      have hNzero : N i = 0 := by
        exact le_antisymm (le_of_not_gt hi)
          (by simpa [N] using subExponentialNorm_nonneg (X i) μ)
      exact
        subExponentialNorm_eq_zero_iff_ae_eq_zero
          (μ := μ) (X := X i) (hXm i).aemeasurable (hXse i) |>.mp
          (by simpa [N] using hNzero)
    have hsum_ae :
        (fun ω => ∑ i, X i ω)
          =ᵐ[μ] fun ω => ∑ j : {i : ι // P i}, XJ j ω := by
      have hall :
          ∀ᵐ ω ∂μ, ∀ i, ¬ P i → X i ω = 0 := by
        exact Filter.eventually_all.mpr fun i => by
          by_cases hi : P i
          · exact Filter.Eventually.of_forall fun _ω hnot => False.elim (hnot hi)
          · exact (hzero_ae i hi).mono fun _ω hω _ => hω
      refine hall.mono ?_
      intro ω hω
      calc
        ∑ i, X i ω =
            Finset.sum (Finset.filter P Finset.univ) (fun i => X i ω) := by
          have hnot_zero :
              Finset.sum (Finset.filter (fun i => ¬ P i) Finset.univ)
                (fun i => X i ω) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            exact hω i (by simpa using (Finset.mem_filter.mp hi).2)
          have hsplit :=
            Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset ι)) (p := P) (f := fun i => X i ω)
          rw [← hsplit, hnot_zero, add_zero]
        _ = ∑ j : {i : ι // P i}, XJ j ω := by
          symm
          simpa [XJ] using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset ι)) (p := P)
              (f := fun i => X i ω))
    have hVeq :
        subExponentialVarianceProxySum
            (fun j : {i : ι // P i} => subExponentialNorm (XJ j) μ)
          = subExponentialVarianceProxySum N := by
      unfold subExponentialVarianceProxySum
      have hnot_zero :
          Finset.sum (Finset.filter (fun i => ¬ P i) Finset.univ)
            (fun i => N i ^ 2) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hnot : ¬ P i := by simpa using (Finset.mem_filter.mp hi).2
        have hNzero : N i = 0 := by
          exact le_antisymm (le_of_not_gt hnot)
            (by simpa [N] using subExponentialNorm_nonneg (X i) μ)
        simp [hNzero]
      calc
        ∑ j : {i : ι // P i}, subExponentialNorm (XJ j) μ ^ 2
            = Finset.sum (Finset.filter P Finset.univ) (fun i => N i ^ 2) := by
          simpa [XJ, N] using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset ι)) (p := P)
              (f := fun i => N i ^ 2))
        _ = ∑ i, N i ^ 2 := by
          have hsplit :=
            Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset ι)) (p := P) (f := fun i => N i ^ 2)
          rw [← hsplit, hnot_zero, add_zero]
    have hevent :
        {ω | t ≤ |∑ i, X i ω|}
          =ᵐ[μ] {ω | t ≤ |∑ j : {i : ι // P i}, XJ j ω|} :=
      Filter.eventuallyEq_set.mpr <|
        hsum_ae.mono fun _ω hω => by simp [hω]
    calc
      μ.real {ω | t ≤ |∑ i, X i ω|}
          = μ.real {ω | t ≤ |∑ j : {i : ι // P i}, XJ j ω|} :=
        MeasureTheory.measureReal_congr hevent
      _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum
            (fun j : {i : ι // P i} => subExponentialNorm (XJ j) μ)) (t / M)) :=
        htailJ
      _ = 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum N) (t / M)) := by
        rw [hVeq]
  · have hNzero : ∀ i, N i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (by
        intro hi
        exact hPnonempty ⟨i, hi⟩))
        (by simpa [N] using subExponentialNorm_nonneg (X i) μ)
    have hVzero : subExponentialVarianceProxySum N = 0 := by
      unfold subExponentialVarianceProxySum
      simp [hNzero]
    have hprob : μ.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 :=
      measureReal_le_one
    have hrhs : 1 ≤
        2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum N) (t / M)) := by
      rw [hVzero]
      have htM_nonneg : 0 ≤ t / M := div_nonneg ht hMpos.le
      simp [htM_nonneg]
    exact hprob.trans hrhs

/-- Theorem 2.8.1 in the book-facing max-norm form:
for independent centered sub-exponential variables,
`P{|∑ Xᵢ| ≥ t}` is bounded by Bernstein's
`min(t² / ∑ ‖Xᵢ‖ψ₁², t / maxᵢ ‖Xᵢ‖ψ₁)` expression, with an explicit
absolute constant. -/
theorem bernstein_norm_sum_two_sided_max
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / subExponentialVarianceProxySum
          (fun i => subExponentialNorm (X i) μ))
          (t / finiteMaxValue (fun i => subExponentialNorm (X i) μ))) := by
  classical
  let N : ι → ℝ := fun i => subExponentialNorm (X i) μ
  let M : ℝ := finiteMaxValue N
  have hNnonneg : ∀ i, 0 ≤ N i := by
    intro i
    exact subExponentialNorm_nonneg (X i) μ
  have hMnonneg : 0 ≤ M := finiteMaxValue_nonneg hNnonneg
  by_cases hMpos : 0 < M
  · have hNormM : ∀ i, subExponentialNorm (X i) μ ≤ M := by
      intro i
      simpa [N, M] using le_finiteMaxValue N i
    simpa [N, M] using
      bernstein_norm_sum_two_sided
        (μ := μ) (X := X) (M := M) (t := t)
        hindep hXm hXse hmean hMpos hNormM ht
  · have hMzero : M = 0 := le_antisymm (le_of_not_gt hMpos) hMnonneg
    have hNzero : ∀ i, N i = 0 := by
      intro i
      exact le_antisymm
        ((le_finiteMaxValue N i).trans_eq hMzero) (hNnonneg i)
    have hVzero : subExponentialVarianceProxySum N = 0 := by
      unfold subExponentialVarianceProxySum
      simp [hNzero]
    have hprob : μ.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 :=
      measureReal_le_one
    have hrhs : 1 ≤
        2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / subExponentialVarianceProxySum N) (t / M)) := by
      rw [hVzero, hMzero]
      norm_num
    exact hprob.trans (by simpa [N, M] using hrhs)

/-- Weighted optimized Bernstein bound from a common local signed MGF scale.
This is the weighted Section 2.8 min-structure at the MGF-hypothesis level.
The nonzero-coefficient hypothesis is only needed for this direct reuse of the
scale-multiplication lemma; the exact `ψ₁` book theorem will separately handle
zero coefficients when the norm-to-MGF bridge is available. -/
theorem bernstein_mgf_weighted_sum_two_sided_optimized_nonzero
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ K)
    (hKpos : 0 < K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ha : ∀ i, a i ≠ 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let L : ι → ℝ := fun i => |a i| * K
  have hindepY : iIndepFun Y μ := by
    have hcomp :=
      hindep.comp (fun i x => a i * x) (by
        intro i
        fun_prop)
    simpa [Y, Function.comp_def] using hcomp
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using (hXm i).const_mul (a i)
  have hY : ∀ i, subExponentialMGFCondition (Y i) μ (L i) := by
    intro i
    simpa [Y, L] using
      subExponentialMGFCondition_const_mul
        (μ := μ) (X := X i) (K := K) (a := a i) (ha i) (hX i)
  have hLpos : ∀ i, 0 < L i := by
    intro i
    exact mul_pos (abs_pos.mpr (ha i)) hKpos
  have hMpos : 0 < K * A := mul_pos hKpos hApos
  have hLM : ∀ i, L i ≤ K * A := by
    intro i
    have h := mul_le_mul_of_nonneg_left (hA i) hKpos.le
    simpa [L, mul_comm] using h
  have hV :
      subExponentialVarianceProxySum L = K ^ 2 * coeffL2NormSq a := by
    unfold subExponentialVarianceProxySum coeffL2NormSq L
    calc
      (∑ i, (|a i| * K) ^ 2)
          = ∑ i, K ^ 2 * a i ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [mul_pow, sq_abs]
        ring
      _ = K ^ 2 * ∑ i, a i ^ 2 := by
        rw [Finset.mul_sum]
  have htail :=
    bernstein_mgf_sum_two_sided_optimized
      (μ := μ) (X := Y) (K := L) (M := K * A) (t := t)
      hindepY hYm hY hLpos hMpos hLM ht
  rw [hV] at htail
  simpa [Y, coeffL2NormSq] using htail

/-- Weighted Bernstein Chernoff bound at a fixed parameter.  This version
uses the scalar MGF estimate directly, so zero coefficients contribute the
exact quadratic proxy `0` instead of requiring a positive local-MGF scale for
the zero random variable. -/
theorem bernstein_mgf_weighted_sum_two_sided
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {K A θ t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (hθ_nonneg : 0 ≤ θ)
    (hθ_window : |θ| ≤ 1 / (K * A)) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
  classical
  let Y : ι → Ω → ℝ := fun i ω => a i * X i ω
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  have hindepY : iIndepFun Y μ := by
    have hcomp :=
      hindep.comp (fun i x => a i * x) (by
        intro i
        fun_prop)
    simpa [Y, Function.comp_def] using hcomp
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using (hXm i).const_mul (a i)
  have hsum_int_pos :
      Integrable (fun ω => Real.exp (θ * S ω)) μ := by
    have h_each_int :
        ∀ i ∈ (Finset.univ : Finset ι),
          Integrable (fun ω => Real.exp (θ * Y i ω)) μ := by
      intro i _hi
      exact
        (subExponentialMGFCondition_const_mul_bound_of_abs_le
          (μ := μ) (X := X i) (K := K) (A := A) (a := a i) (θ := θ)
          (hX i) hApos (hA i) hθ_window).1
    have h :=
      hindepY.integrable_exp_mul_sum
        (t := θ) hYm (s := (Finset.univ : Finset ι)) h_each_int
    simpa [S, Y, Finset.sum_apply] using h
  have hmgf_sum_pos :
      mgf S μ θ = ∏ i, mgf (Y i) μ θ := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), Y i) μ θ =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (Y i) μ θ :=
      hindepY.mgf_sum (t := θ) hYm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, Y i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le_pos :
      mgf S μ θ ≤ Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
    calc
      mgf S μ θ = ∏ i, mgf (Y i) μ θ := hmgf_sum_pos
      _ ≤ ∏ i, Real.exp (K ^ 2 * a i ^ 2 * θ ^ 2) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact
            (subExponentialMGFCondition_const_mul_bound_of_abs_le
              (μ := μ) (X := X i) (K := K) (A := A) (a := a i) (θ := θ)
              (hX i) hApos (hA i) hθ_window).2
      _ = Real.exp (∑ i, K ^ 2 * a i ^ 2 * θ ^ 2) := by
        rw [Real.exp_sum]
      _ = Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        congr 1
        unfold coeffL2NormSq
        calc
          (∑ i, K ^ 2 * a i ^ 2 * θ ^ 2)
              = ∑ i, θ ^ 2 * (K ^ 2 * a i ^ 2) := by
            exact Finset.sum_congr rfl fun i _ => by ring
          _ = θ ^ 2 * ∑ i, K ^ 2 * a i ^ 2 := by
            rw [Finset.mul_sum]
          _ = θ ^ 2 * (K ^ 2 * ∑ i, a i ^ 2) := by
            congr 1
            rw [Finset.mul_sum]
  let η : ℝ := -θ
  have hη_window : |η| ≤ 1 / (K * A) := by
    simpa [η, abs_neg] using hθ_window
  have hsum_int_neg :
      Integrable (fun ω => Real.exp (η * S ω)) μ := by
    have h_each_int :
        ∀ i ∈ (Finset.univ : Finset ι),
          Integrable (fun ω => Real.exp (η * Y i ω)) μ := by
      intro i _hi
      exact
        (subExponentialMGFCondition_const_mul_bound_of_abs_le
          (μ := μ) (X := X i) (K := K) (A := A) (a := a i) (θ := η)
          (hX i) hApos (hA i) hη_window).1
    have h :=
      hindepY.integrable_exp_mul_sum
        (t := η) hYm (s := (Finset.univ : Finset ι)) h_each_int
    simpa [S, Y, Finset.sum_apply] using h
  have hmgf_sum_neg :
      mgf S μ η = ∏ i, mgf (Y i) μ η := by
    have hsum :
        mgf (∑ i ∈ (Finset.univ : Finset ι), Y i) μ η =
          ∏ i ∈ (Finset.univ : Finset ι), mgf (Y i) μ η :=
      hindepY.mgf_sum (t := η) hYm (Finset.univ : Finset ι)
    have hfun : S = (∑ i : ι, Y i) := by
      funext ω
      simp [S, Finset.sum_apply]
    simpa [hfun] using hsum
  have hmgf_le_neg :
      mgf S μ η ≤ Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
    calc
      mgf S μ η = ∏ i, mgf (Y i) μ η := hmgf_sum_neg
      _ ≤ ∏ i, Real.exp (K ^ 2 * a i ^ 2 * η ^ 2) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i _hi
          exact mgf_nonneg
        · intro i _hi
          exact
            (subExponentialMGFCondition_const_mul_bound_of_abs_le
              (μ := μ) (X := X i) (K := K) (A := A) (a := a i) (θ := η)
              (hX i) hApos (hA i) hη_window).2
      _ = Real.exp (∑ i, K ^ 2 * a i ^ 2 * η ^ 2) := by
        rw [Real.exp_sum]
      _ = Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        congr 1
        unfold coeffL2NormSq
        calc
          (∑ i, K ^ 2 * a i ^ 2 * η ^ 2)
              = ∑ i, θ ^ 2 * (K ^ 2 * a i ^ 2) := by
            exact Finset.sum_congr rfl fun i _ => by
              dsimp [η]
              ring
          _ = θ ^ 2 * ∑ i, K ^ 2 * a i ^ 2 := by
            rw [Finset.mul_sum]
          _ = θ ^ 2 * (K ^ 2 * ∑ i, a i ^ 2) := by
            congr 1
            rw [Finset.mul_sum]
  let U : Set Ω := {ω | t ≤ S ω}
  let L : Set Ω := {ω | S ω ≤ -t}
  have hsubset : {ω | t ≤ |∑ i, a i * X i ω|} ⊆ U ∪ L := by
    intro ω hω
    by_cases hnonneg : 0 ≤ S ω
    · left
      dsimp [U, S, Y] at *
      simpa [abs_of_nonneg hnonneg] using hω
    · right
      have hneg : S ω < 0 := lt_of_not_ge hnonneg
      have hle : S ω ≤ -t := by
        have hAbs : t ≤ -(S ω) := by
          have hωS : t ≤ |S ω| := by
            simpa [S, Y] using hω
          simpa [abs_of_neg hneg] using hωS
        linarith
      exact hle
  have hupper :
      μ.real U ≤ Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
    have htail :
        μ.real U ≤ Real.exp (-θ * t) * mgf S μ θ := by
      dsimp [U]
      exact ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := S) t hθ_nonneg hsum_int_pos
    calc
      μ.real U ≤ Real.exp (-θ * t) * mgf S μ θ := htail
      _ ≤ Real.exp (-θ * t)
          * Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        exact mul_le_mul_of_nonneg_left hmgf_le_pos (Real.exp_pos _).le
      _ = Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        rw [Real.exp_add]
  have hlower :
      μ.real L ≤ Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
    have hη_nonpos : η ≤ 0 := by
      dsimp [η]
      exact neg_nonpos.mpr hθ_nonneg
    have htail :
        μ.real L ≤ Real.exp (-η * (-t)) * mgf S μ η := by
      dsimp [L]
      exact ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := μ) (X := S) (-t) hη_nonpos hsum_int_neg
    calc
      μ.real L ≤ Real.exp (-η * (-t)) * mgf S μ η := htail
      _ ≤ Real.exp (-η * (-t))
          * Real.exp (θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        exact mul_le_mul_of_nonneg_left hmgf_le_neg (Real.exp_pos _).le
      _ = Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
        dsimp [η]
        rw [Real.exp_add]
        ring_nf
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
        ≤ μ.real (U ∪ L) :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ μ.real U + μ.real L :=
      MeasureTheory.measureReal_union_le U L
    _ ≤ Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a))
        + Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := by
      ring

/-- Weighted optimized Bernstein bound from a common local signed MGF scale,
with no nonzero-coefficient restriction. -/
theorem bernstein_mgf_weighted_sum_two_sided_optimized
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialMGFCondition (X i) μ K)
    (hKpos : 0 < K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  by_cases hcoeff_zero : coeffL2NormSq a = 0
  · have hMpos : 0 < K * A := mul_pos hKpos hApos
    have hmin :
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) = 0 := by
      rw [hcoeff_zero]
      simp [div_nonneg ht hMpos.le]
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 := by
        calc
          μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ μ.real Set.univ :=
            MeasureTheory.measureReal_mono (Set.subset_univ _)
          _ = 1 := by simp
      _ ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        rw [hmin]
        norm_num
  · let V : ℝ := K ^ 2 * coeffL2NormSq a
    let M : ℝ := K * A
    have hcoeff_nonneg : 0 ≤ coeffL2NormSq a := by
      unfold coeffL2NormSq
      exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
    have hcoeff_pos : 0 < coeffL2NormSq a :=
      lt_of_le_of_ne hcoeff_nonneg (Ne.symm hcoeff_zero)
    have hVpos : 0 < V := by
      dsimp [V]
      exact mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
    have hMpos : 0 < M := by
      dsimp [M]
      exact mul_pos hKpos hApos
    let θ : ℝ := min (t / (2 * V)) (1 / (2 * M))
    have hθ_nonneg : 0 ≤ θ := by
      dsimp [θ]
      exact le_min
        (div_nonneg ht (by positivity : 0 ≤ 2 * V))
        (by positivity)
    have hθ_le_one_div_M : θ ≤ 1 / M := by
      calc
        θ ≤ 1 / (2 * M) := by
          dsimp [θ]
          exact min_le_right _ _
        _ ≤ 1 / M := by
          have h2M : 0 < 2 * M := by positivity
          exact (one_div_le_one_div h2M hMpos).mpr (by nlinarith)
    have hθ_window : |θ| ≤ 1 / (K * A) := by
      rw [abs_of_nonneg hθ_nonneg]
      simpa [M] using hθ_le_one_div_M
    have htail :=
      bernstein_mgf_weighted_sum_two_sided
        (μ := μ) (X := X) (K := K) (A := A) (θ := θ) (t := t) a
        hindep hXm hX hApos hA hθ_nonneg hθ_window
    have hexp_arg :
        -θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)
          ≤ -(1 / 4 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
      simpa [V, M, θ] using
        bernstein_mgf_exponent_optimized
          (t := t) (V := V) (M := M) (θ := θ) ht hVpos hMpos rfl
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|}
          ≤ 2 * Real.exp (-θ * t + θ ^ 2 * (K ^ 2 * coeffL2NormSq a)) := htail
      _ ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Weighted Bernstein inequality with a common admissible `ψ₁` Orlicz scale.
This is the weighted Theorem 2.8.2 min-form with absolute constant `1/256`,
under the current nonzero-coefficient support hypothesis inherited from the
MGF-level weighted theorem. -/
theorem bernstein_orlicz_weighted_sum_two_sided_nonzero
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialOrliczCondition (X i) μ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ha : ∀ i, a i ≠ 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  have hMGF : ∀ i, subExponentialMGFCondition (X i) μ (8 * K) := by
    intro i
    exact
      subExponentialMGFCondition_of_orliczCondition_of_integral_eq_zero
        (μ := μ) (X := X i) (K := K) (hXm i).aemeasurable (hX i) (hmean i)
  have htail :=
    bernstein_mgf_weighted_sum_two_sided_optimized_nonzero
      (μ := μ) (X := X) (K := 8 * K) (A := A) (t := t) a
      hindep hXm hMGF (by positivity) hApos hA ha ht
  have hcoeff_pos : 0 < coeffL2NormSq a := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < a i0 ^ 2 := sq_pos_of_ne_zero (ha i0)
    have hterm_le :
        a i0 ^ 2 ≤ ∑ i, a i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [coeffL2NormSq] using hterm_le)
  have hVpos : 0 < K ^ 2 * coeffL2NormSq a :=
    mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
  have hMpos : 0 < K * A := mul_pos hKpos hApos
  have hexp_arg :
      -(1 / 4 : ℝ) *
          min (t ^ 2 / ((8 * K) ^ 2 * coeffL2NormSq a)) (t / ((8 * K) * A))
        ≤ -(1 / 256 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
    have h :=
      bernstein_orlicz_exponent_rescale
        (t := t) (V := K ^ 2 * coeffL2NormSq a) (M := K * A) ht hVpos hMpos
    norm_num [mul_pow, mul_assoc, mul_comm, mul_left_comm] at h ⊢
    exact h
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
        ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
          min (t ^ 2 / ((8 * K) ^ 2 * coeffL2NormSq a)) (t / ((8 * K) * A))) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using htail
    _ ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Weighted Bernstein inequality with a common admissible `ψ₁` Orlicz scale,
with no nonzero-coefficient restriction.  This is the weighted Theorem 2.8.2
min-form at an admissible Orlicz scale, with absolute constant `1/256`. -/
theorem bernstein_orlicz_weighted_sum_two_sided
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, subExponentialOrliczCondition (X i) μ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  by_cases hcoeff_zero : coeffL2NormSq a = 0
  · have hMpos : 0 < K * A := mul_pos hKpos hApos
    have hmin :
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) = 0 := by
      rw [hcoeff_zero]
      simp [div_nonneg ht hMpos.le]
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 := by
        calc
          μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ μ.real Set.univ :=
            MeasureTheory.measureReal_mono (Set.subset_univ _)
          _ = 1 := by simp
      _ ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        rw [hmin]
        norm_num
  · have hcoeff_nonneg : 0 ≤ coeffL2NormSq a := by
      unfold coeffL2NormSq
      exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
    have hcoeff_pos : 0 < coeffL2NormSq a :=
      lt_of_le_of_ne hcoeff_nonneg (Ne.symm hcoeff_zero)
    have hMGF : ∀ i, subExponentialMGFCondition (X i) μ (8 * K) := by
      intro i
      exact
        subExponentialMGFCondition_of_orliczCondition_of_integral_eq_zero
          (μ := μ) (X := X i) (K := K) (hXm i).aemeasurable (hX i) (hmean i)
    have htail :=
      bernstein_mgf_weighted_sum_two_sided_optimized
        (μ := μ) (X := X) (K := 8 * K) (A := A) (t := t) a
        hindep hXm hMGF (by positivity) hApos hA ht
    have hVpos : 0 < K ^ 2 * coeffL2NormSq a :=
      mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
    have hMpos : 0 < K * A := mul_pos hKpos hApos
    have hexp_arg :
        -(1 / 4 : ℝ) *
            min (t ^ 2 / ((8 * K) ^ 2 * coeffL2NormSq a)) (t / ((8 * K) * A))
          ≤ -(1 / 256 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
      have h :=
        bernstein_orlicz_exponent_rescale
          (t := t) (V := K ^ 2 * coeffL2NormSq a) (M := K * A) ht hVpos hMpos
      norm_num [mul_pow, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      exact h
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|}
          ≤ 2 * Real.exp (-(1 / 4 : ℝ) *
            min (t ^ 2 / ((8 * K) ^ 2 * coeffL2NormSq a)) (t / ((8 * K) * A))) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using htail
      _ ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Weighted Bernstein inequality with a common positive bound on the
`ψ₁` norms.  It uses `2K` as the common admissible Orlicz scale and therefore
has absolute constant `1/1024`; the nonzero-coefficient support hypothesis is
inherited from the current weighted MGF theorem. -/
theorem bernstein_norm_weighted_sum_two_sided_positive_nonzero
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ha : ∀ i, a i ≠ 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  have hOrlicz : ∀ i, subExponentialOrliczCondition (X i) μ (2 * K) := by
    intro i
    have htwo_norm :
        subExponentialOrliczCondition (X i) μ
          (2 * subExponentialNorm (X i) μ) :=
      subExponentialOrliczCondition_two_mul_norm
        (μ := μ) (X := X i) (hXm i).aemeasurable (hXse i) (hNormPos i)
    have hle : 2 * subExponentialNorm (X i) μ ≤ 2 * K :=
      mul_le_mul_of_nonneg_left (hNormK i) (by norm_num)
    exact subExponentialOrliczCondition_mono_scale (hXm i).aemeasurable htwo_norm hle
  have htail :=
    bernstein_orlicz_weighted_sum_two_sided_nonzero
      (μ := μ) (X := X) (K := 2 * K) (A := A) (t := t) a
      hindep hXm hOrlicz hmean (by positivity) hApos hA ha ht
  have hcoeff_pos : 0 < coeffL2NormSq a := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < a i0 ^ 2 := sq_pos_of_ne_zero (ha i0)
    have hterm_le :
        a i0 ^ 2 ≤ ∑ i, a i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [coeffL2NormSq] using hterm_le)
  have hVpos : 0 < K ^ 2 * coeffL2NormSq a :=
    mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
  have hMpos : 0 < K * A := mul_pos hKpos hApos
  have hexp_arg :
      -(1 / 256 : ℝ) *
          min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))
        ≤ -(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
    have h :=
      bernstein_norm_exponent_rescale
        (t := t) (V := K ^ 2 * coeffL2NormSq a) (M := K * A) ht hVpos hMpos
    norm_num [mul_pow, mul_assoc, mul_comm, mul_left_comm] at h ⊢
    exact h
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
        ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using htail
    _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Weighted Bernstein inequality with a common positive bound on the
`ψ₁` norms, without assuming the individual norms are positive.  Zero-norm
variables are handled by `ψ₁` definiteness and the common admissible scale
`2K`.  The remaining nonzero-coefficient support hypothesis is inherited from
the current weighted MGF theorem. -/
theorem bernstein_norm_weighted_sum_two_sided_nonzero
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ha : ∀ i, a i ≠ 0)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  have hOrlicz : ∀ i, subExponentialOrliczCondition (X i) μ (2 * K) := by
    intro i
    exact
      subExponentialOrliczCondition_two_mul_of_norm_le
        (μ := μ) (X := X i) (K := K)
        (hXm i).aemeasurable (hXse i) hKpos (hNormK i)
  have htail :=
    bernstein_orlicz_weighted_sum_two_sided_nonzero
      (μ := μ) (X := X) (K := 2 * K) (A := A) (t := t) a
      hindep hXm hOrlicz hmean (by positivity) hApos hA ha ht
  have hcoeff_pos : 0 < coeffL2NormSq a := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hterm_pos : 0 < a i0 ^ 2 := sq_pos_of_ne_zero (ha i0)
    have hterm_le :
        a i0 ^ 2 ≤ ∑ i, a i ^ 2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ i0)
    exact hterm_pos.trans_le (by simpa [coeffL2NormSq] using hterm_le)
  have hVpos : 0 < K ^ 2 * coeffL2NormSq a :=
    mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
  have hMpos : 0 < K * A := mul_pos hKpos hApos
  have hexp_arg :
      -(1 / 256 : ℝ) *
          min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))
        ≤ -(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
    have h :=
      bernstein_norm_exponent_rescale
        (t := t) (V := K ^ 2 * coeffL2NormSq a) (M := K * A) ht hVpos hMpos
    norm_num [mul_pow, mul_assoc, mul_comm, mul_left_comm] at h ⊢
    exact h
  calc
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
        ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
          min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using htail
    _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Weighted Bernstein inequality with a common positive bound on the
`ψ₁` norms, with no nonzero-coefficient restriction.  This is the book-facing
Theorem 2.8.2 common-`K` form, with an explicit absolute constant. -/
theorem bernstein_norm_weighted_sum_two_sided
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K A t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (hApos : 0 < A)
    (hA : ∀ i, |a i| ≤ A)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
  classical
  by_cases hcoeff_zero : coeffL2NormSq a = 0
  · have hMpos : 0 < K * A := mul_pos hKpos hApos
    have hmin :
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) = 0 := by
      rw [hcoeff_zero]
      simp [div_nonneg ht hMpos.le]
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 := by
        calc
          μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ μ.real Set.univ :=
            MeasureTheory.measureReal_mono (Set.subset_univ _)
          _ = 1 := by simp
      _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        rw [hmin]
        norm_num
  · have hcoeff_nonneg : 0 ≤ coeffL2NormSq a := by
      unfold coeffL2NormSq
      exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
    have hcoeff_pos : 0 < coeffL2NormSq a :=
      lt_of_le_of_ne hcoeff_nonneg (Ne.symm hcoeff_zero)
    have hOrlicz : ∀ i, subExponentialOrliczCondition (X i) μ (2 * K) := by
      intro i
      exact
        subExponentialOrliczCondition_two_mul_of_norm_le
          (μ := μ) (X := X i) (K := K)
          (hXm i).aemeasurable (hXse i) hKpos (hNormK i)
    have htail :=
      bernstein_orlicz_weighted_sum_two_sided
        (μ := μ) (X := X) (K := 2 * K) (A := A) (t := t) a
        hindep hXm hOrlicz hmean (by positivity) hApos hA ht
    have hVpos : 0 < K ^ 2 * coeffL2NormSq a :=
      mul_pos (sq_pos_of_pos hKpos) hcoeff_pos
    have hMpos : 0 < K * A := mul_pos hKpos hApos
    have hexp_arg :
        -(1 / 256 : ℝ) *
            min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))
          ≤ -(1 / 1024 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A)) := by
      have h :=
        bernstein_norm_exponent_rescale
          (t := t) (V := K ^ 2 * coeffL2NormSq a) (M := K * A) ht hVpos hMpos
      norm_num [mul_pow, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      exact h
    calc
      μ.real {ω | t ≤ |∑ i, a i * X i ω|}
          ≤ 2 * Real.exp (-(1 / 256 : ℝ) *
            min (t ^ 2 / ((2 * K) ^ 2 * coeffL2NormSq a)) (t / ((2 * K) * A))) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using htail
      _ ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
            min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * A))) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)

/-- Theorem 2.8.2 in the book-facing `‖a‖∞` form:
weighted Bernstein for independent centered sub-exponential variables with
a common `ψ₁` bound. -/
theorem bernstein_norm_weighted_sum_two_sided_linf
    [IsProbabilityMeasure μ] [Nonempty ι]
    {X : ι → Ω → ℝ} {K t : ℝ} (a : ι → ℝ)
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / (K ^ 2 * coeffL2NormSq a))
          (t / (K * coeffLInfNorm a))) := by
  classical
  by_cases hApos : 0 < coeffLInfNorm a
  · exact
      bernstein_norm_weighted_sum_two_sided
        (μ := μ) (X := X) (K := K) (A := coeffLInfNorm a) (t := t) a
        hindep hXm hXse hmean hKpos hNormK hApos
        (fun i => abs_coeff_le_linf a i) ht
  · have hAzero : coeffLInfNorm a = 0 :=
      le_antisymm (le_of_not_gt hApos) (coeffLInfNorm_nonneg a)
    have ha_zero : ∀ i, a i = 0 := by
      intro i
      have habs_nonpos : |a i| ≤ 0 := by
        simpa [hAzero] using abs_coeff_le_linf a i
      exact abs_eq_zero.mp (le_antisymm habs_nonpos (abs_nonneg (a i)))
    have hcoeff_zero : coeffL2NormSq a = 0 := by
      unfold coeffL2NormSq
      simp [ha_zero]
    have hprob : μ.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 :=
      measureReal_le_one
    have hrhs : 1 ≤
        2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a))
            (t / (K * coeffLInfNorm a))) := by
      rw [hcoeff_zero, hAzero]
      norm_num
    exact hprob.trans hrhs

/-- Squared `ℓ₂` norm of the constant averaging vector on `Fin N`. -/
lemma coeffL2NormSq_const_inv_card_fin {N : ℕ} (hN : 0 < N) :
    coeffL2NormSq (fun _i : Fin N => ((N : ℝ)⁻¹)) = (N : ℝ)⁻¹ := by
  unfold coeffL2NormSq
  simp
  field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- Algebraic min-form specialization for averaging weights. -/
lemma bernstein_average_min_identity {N : ℕ} (hN : 0 < N) {K t : ℝ}
    (hK : 0 < K) :
    min (t ^ 2 / (K ^ 2 * (N : ℝ)⁻¹)) (t / (K * (N : ℝ)⁻¹)) =
      (N : ℝ) * min (t ^ 2 / K ^ 2) (t / K) := by
  have hNreal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases hcase : t ^ 2 / K ^ 2 ≤ t / K
  · rw [min_eq_left hcase]
    have hcase_alg : t ^ 2 ≤ t * K := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hK) hK] at hcase
      nlinarith
    have hcase' : t ^ 2 / (K ^ 2 * (N : ℝ)⁻¹) ≤ t / (K * (N : ℝ)⁻¹) := by
      field_simp [hNreal, hK.ne']
      exact hcase_alg
    rw [min_eq_left hcase']
    field_simp [hNreal, hK.ne']
  · have hcase_le : t / K ≤ t ^ 2 / K ^ 2 := le_of_not_ge hcase
    rw [min_eq_right hcase_le]
    have hcase_alg : t * K ≤ t ^ 2 := by
      rw [div_le_div_iff₀ hK (sq_pos_of_pos hK)] at hcase_le
      nlinarith
    have hcase' : t / (K * (N : ℝ)⁻¹) ≤ t ^ 2 / (K ^ 2 * (N : ℝ)⁻¹) := by
      field_simp [hNreal, hK.ne']
      exact hcase_alg
    rw [min_eq_right hcase']
    field_simp [hNreal, hK.ne']

/-- Corollary 2.8.3, positive-norm form: Bernstein inequality for averages of
independent centered sub-exponential variables with a common positive
`ψ₁`-norm bound. -/
theorem bernstein_average_norm_two_sided_positive
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(N : ℝ)⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        ((N : ℝ) * min (t ^ 2 / K ^ 2) (t / K))) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let a : Fin N → ℝ := fun _i => (N : ℝ)⁻¹
  have hApos : 0 < (N : ℝ)⁻¹ := by
    exact inv_pos.mpr (Nat.cast_pos.mpr hN)
  have hA : ∀ i, |a i| ≤ (N : ℝ)⁻¹ := by
    intro i
    dsimp [a]
    rw [abs_of_pos hApos]
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    dsimp [a]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr hN.ne')
  have htail :=
    bernstein_norm_weighted_sum_two_sided_positive_nonzero
      (μ := μ) (X := X) (K := K) (A := (N : ℝ)⁻¹) (t := t) a
      hindep hXm hXse hmean hNormPos hKpos hNormK hApos hA ha ht
  have htail_avg :
      μ.real {ω | t ≤ |(N : ℝ)⁻¹ * ∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * (N : ℝ)⁻¹))) := by
    simpa [a, Finset.mul_sum] using htail
  rw [coeffL2NormSq_const_inv_card_fin hN] at htail_avg
  have hmin :
      min (t ^ 2 / (K ^ 2 * (N : ℝ)⁻¹)) (t / (K * (N : ℝ)⁻¹)) =
        (N : ℝ) * min (t ^ 2 / K ^ 2) (t / K) :=
    bernstein_average_min_identity hN hKpos
  simpa [hmin] using htail_avg

/-- Corollary 2.8.3, common-`ψ₁`-bound form: Bernstein inequality for
averages without assuming the individual `ψ₁` norms are positive. -/
theorem bernstein_average_norm_two_sided
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(N : ℝ)⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        ((N : ℝ) * min (t ^ 2 / K ^ 2) (t / K))) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let a : Fin N → ℝ := fun _i => (N : ℝ)⁻¹
  have hApos : 0 < (N : ℝ)⁻¹ := by
    exact inv_pos.mpr (Nat.cast_pos.mpr hN)
  have hA : ∀ i, |a i| ≤ (N : ℝ)⁻¹ := by
    intro i
    dsimp [a]
    rw [abs_of_pos hApos]
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    dsimp [a]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr hN.ne')
  have htail :=
    bernstein_norm_weighted_sum_two_sided_nonzero
      (μ := μ) (X := X) (K := K) (A := (N : ℝ)⁻¹) (t := t) a
      hindep hXm hXse hmean hKpos hNormK hApos hA ha ht
  have htail_avg :
      μ.real {ω | t ≤ |(N : ℝ)⁻¹ * ∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a)) (t / (K * (N : ℝ)⁻¹))) := by
    simpa [a, Finset.mul_sum] using htail
  rw [coeffL2NormSq_const_inv_card_fin hN] at htail_avg
  have hmin :
      min (t ^ 2 / (K ^ 2 * (N : ℝ)⁻¹)) (t / (K * (N : ℝ)⁻¹)) =
        (N : ℝ) * min (t ^ 2 / K ^ 2) (t / K) :=
    bernstein_average_min_identity hN hKpos
  simpa [hmin] using htail_avg

/-- Squared `ℓ₂` norm of the constant normalized-sum vector on `Fin N`. -/
lemma coeffL2NormSq_const_inv_sqrt_card_fin {N : ℕ} (hN : 0 < N) :
    coeffL2NormSq (fun _i : Fin N => (Real.sqrt (N : ℝ))⁻¹) = 1 := by
  unfold coeffL2NormSq
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hNpos).ne'
  simp
  field_simp [hsqrt_ne]

/-- Algebraic min-form specialization for normalized-sum weights
`a_i = N^{-1/2}`. -/
lemma bernstein_normalized_min_identity {N : ℕ} (hN : 0 < N) {K t : ℝ}
    (hK : 0 < K) :
    min (t ^ 2 / K ^ 2) (t / (K * (Real.sqrt (N : ℝ))⁻¹)) =
      min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr hNpos).ne'
  have hright :
      t / (K * (Real.sqrt (N : ℝ))⁻¹) =
        t * Real.sqrt (N : ℝ) / K := by
    field_simp [hK.ne', hsqrt_ne]
  rw [hright]

/-- Normalized version of the Bernstein consequence after Corollary 2.8.3,
in the current positive-`ψ₁`-norm form. -/
theorem bernstein_normalized_sum_norm_two_sided_positive
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let a : Fin N → ℝ := fun _i => (Real.sqrt (N : ℝ))⁻¹
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hApos : 0 < (Real.sqrt (N : ℝ))⁻¹ := inv_pos.mpr hsqrt_pos
  have hA : ∀ i, |a i| ≤ (Real.sqrt (N : ℝ))⁻¹ := by
    intro i
    dsimp [a]
    rw [abs_of_pos hApos]
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    dsimp [a]
    exact inv_ne_zero hsqrt_pos.ne'
  have htail :=
    bernstein_norm_weighted_sum_two_sided_positive_nonzero
      (μ := μ) (X := X) (K := K) (A := (Real.sqrt (N : ℝ))⁻¹) (t := t) a
      hindep hXm hXse hmean hNormPos hKpos hNormK hApos hA ha ht
  have htail_norm_abs :
      μ.real {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a))
            (t / (K * (Real.sqrt (N : ℝ))⁻¹))) := by
    simpa [a, ← Finset.mul_sum, abs_mul, abs_of_pos hApos, mul_assoc]
      using htail
  rw [coeffL2NormSq_const_inv_sqrt_card_fin hN] at htail_norm_abs
  have hmin :
      min (t ^ 2 / K ^ 2) (t / (K * (Real.sqrt (N : ℝ))⁻¹)) =
        min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) :=
    bernstein_normalized_min_identity hN hKpos
  have htail_norm_abs' :
      μ.real {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K)) := by
    simpa [hmin] using htail_norm_abs
  have hEvent :
      {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|} =
        {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|} := by
    ext ω
    change
      (t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|) ↔
        (t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|)
    rw [abs_mul, abs_of_pos hApos]
  simpa [hEvent, abs_of_pos hsqrt_pos] using htail_norm_abs'

/-- Normalized Bernstein consequence after Corollary 2.8.3 without assuming
the individual `ψ₁` norms are positive. -/
theorem bernstein_normalized_sum_norm_two_sided
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let a : Fin N → ℝ := fun _i => (Real.sqrt (N : ℝ))⁻¹
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hApos : 0 < (Real.sqrt (N : ℝ))⁻¹ := inv_pos.mpr hsqrt_pos
  have hA : ∀ i, |a i| ≤ (Real.sqrt (N : ℝ))⁻¹ := by
    intro i
    dsimp [a]
    rw [abs_of_pos hApos]
  have ha : ∀ i, a i ≠ 0 := by
    intro i
    dsimp [a]
    exact inv_ne_zero hsqrt_pos.ne'
  have htail :=
    bernstein_norm_weighted_sum_two_sided_nonzero
      (μ := μ) (X := X) (K := K) (A := (Real.sqrt (N : ℝ))⁻¹) (t := t) a
      hindep hXm hXse hmean hKpos hNormK hApos hA ha ht
  have htail_norm_abs :
      μ.real {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / (K ^ 2 * coeffL2NormSq a))
            (t / (K * (Real.sqrt (N : ℝ))⁻¹))) := by
    simpa [a, ← Finset.mul_sum, abs_mul, abs_of_pos hApos, mul_assoc]
      using htail
  rw [coeffL2NormSq_const_inv_sqrt_card_fin hN] at htail_norm_abs
  have hmin :
      min (t ^ 2 / K ^ 2) (t / (K * (Real.sqrt (N : ℝ))⁻¹)) =
        min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) :=
    bernstein_normalized_min_identity hN hKpos
  have htail_norm_abs' :
      μ.real {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|}
        ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
          min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K)) := by
    simpa [hmin] using htail_norm_abs
  have hEvent :
      {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|} =
        {ω | t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|} := by
    ext ω
    change
      (t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|) ↔
        (t ≤ (Real.sqrt (N : ℝ))⁻¹ * |∑ i, X i ω|)
    rw [abs_mul, abs_of_pos hApos]
  simpa [hEvent, abs_of_pos hsqrt_pos] using htail_norm_abs'

/-- In the normalized Bernstein bound, the quadratic term is the active
regime when `t ≤ K sqrt N`. -/
lemma bernstein_normalized_min_eq_quadratic {N : ℕ} (_hN : 0 < N)
    {K t : ℝ} (hK : 0 < K) (ht : 0 ≤ t)
    (ht_small : t ≤ K * Real.sqrt (N : ℝ)) :
    min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) = t ^ 2 / K ^ 2 := by
  rw [min_eq_left]
  have hle_mul : t ^ 2 ≤ t * (K * Real.sqrt (N : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left ht_small ht
    nlinarith
  field_simp [hK.ne']
  nlinarith

/-- In the normalized Bernstein bound, the linear term is the active regime
when `K sqrt N ≤ t`. -/
lemma bernstein_normalized_min_eq_linear {N : ℕ} (hN : 0 < N)
    {K t : ℝ} (hK : 0 < K)
    (ht_large : K * Real.sqrt (N : ℝ) ≤ t) :
    min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) =
      t * Real.sqrt (N : ℝ) / K := by
  rw [min_eq_right]
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have ht_pos : 0 < t := (mul_pos hK hsqrt_pos).trans_le ht_large
  have hle_mul : t * (K * Real.sqrt (N : ℝ)) ≤ t ^ 2 := by
    have := mul_le_mul_of_nonneg_left ht_large ht_pos.le
    nlinarith
  field_simp [hK.ne']
  nlinarith

/-- Small-deviation regime following Corollary 2.8.3 for the normalized sum:
for `t ≤ K sqrt N`, the exponent is quadratic in `t / K`. -/
theorem bernstein_normalized_sum_small_deviation_norm_two_sided_positive
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t)
    (ht_small : t ≤ K * Real.sqrt (N : ℝ)) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) * (t ^ 2 / K ^ 2)) := by
  have htail :=
    bernstein_normalized_sum_norm_two_sided_positive
      (μ := μ) (N := N) hN (X := X) (K := K) (t := t)
      hindep hXm hXse hmean hNormPos hKpos hNormK ht
  have hmin :
      min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) = t ^ 2 / K ^ 2 :=
    bernstein_normalized_min_eq_quadratic hN hKpos ht ht_small
  simpa [hmin] using htail

/-- Large-deviation regime following Corollary 2.8.3 for the normalized sum:
for `K sqrt N ≤ t`, the exponent is linear in `t sqrt N / K`. -/
theorem bernstein_normalized_sum_large_deviation_norm_two_sided_positive
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hNormPos : ∀ i, 0 < subExponentialNorm (X i) μ)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht_large : K * Real.sqrt (N : ℝ) ≤ t) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        (t * Real.sqrt (N : ℝ) / K)) := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have ht : 0 ≤ t := ((mul_pos hKpos hsqrt_pos).trans_le ht_large).le
  have htail :=
    bernstein_normalized_sum_norm_two_sided_positive
      (μ := μ) (N := N) hN (X := X) (K := K) (t := t)
      hindep hXm hXse hmean hNormPos hKpos hNormK ht
  have hmin :
      min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) =
        t * Real.sqrt (N : ℝ) / K :=
    bernstein_normalized_min_eq_linear hN hKpos ht_large
  simpa [hmin] using htail

/-- Small-deviation regime for the normalized sum, without positive-norm
assumptions. -/
theorem bernstein_normalized_sum_small_deviation_norm_two_sided
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht : 0 ≤ t)
    (ht_small : t ≤ K * Real.sqrt (N : ℝ)) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) * (t ^ 2 / K ^ 2)) := by
  have htail :=
    bernstein_normalized_sum_norm_two_sided
      (μ := μ) (N := N) hN (X := X) (K := K) (t := t)
      hindep hXm hXse hmean hKpos hNormK ht
  have hmin :
      min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) = t ^ 2 / K ^ 2 :=
    bernstein_normalized_min_eq_quadratic hN hKpos ht ht_small
  simpa [hmin] using htail

/-- Large-deviation regime for the normalized sum, without positive-norm
assumptions. -/
theorem bernstein_normalized_sum_large_deviation_norm_two_sided
    [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {K t : ℝ}
    (hindep : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i))
    (hXse : ∀ i, IsSubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hKpos : 0 < K)
    (hNormK : ∀ i, subExponentialNorm (X i) μ ≤ K)
    (ht_large : K * Real.sqrt (N : ℝ) ≤ t) :
    μ.real {ω | t ≤ |(Real.sqrt (N : ℝ))⁻¹ * ∑ i, X i ω|}
      ≤ 2 * Real.exp (-(1 / 1024 : ℝ) *
        (t * Real.sqrt (N : ℝ) / K)) := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have ht : 0 ≤ t := ((mul_pos hKpos hsqrt_pos).trans_le ht_large).le
  have htail :=
    bernstein_normalized_sum_norm_two_sided
      (μ := μ) (N := N) hN (X := X) (K := K) (t := t)
      hindep hXm hXse hmean hKpos hNormK ht
  have hmin :
      min (t ^ 2 / K ^ 2) (t * Real.sqrt (N : ℝ) / K) =
        t * Real.sqrt (N : ℝ) / K :=
    bernstein_normalized_min_eq_linear hN hKpos ht_large
  simpa [hmin] using htail

end MGFSpine

end LeanFpAnalysis.HDP
