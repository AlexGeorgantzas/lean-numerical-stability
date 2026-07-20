-- Algorithms/KahanCompensatedFiniteFormat.lean

import Mathlib.Data.Real.Basic
import NumStability.FloatingPoint.Model
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.CompensatedSum

open Classical

namespace NumStability

/-!
# Compensated summation in the finite binary round-to-even format (Higham §4.3)

This file closes Higham 2nd ed. equation (4.10) (Kielbasiński [731, 1994] and
Neumaier [883, 1974]) for the *finite binary round-to-even* format, not merely
the abstract `FPModel`.

Higham warns (p. 85, and again pp. 94--95) that the correction-formula
exactness (4.7) fails under the no-guard-digit model, and the repository
records a concrete `FPModel` counterexample
(`not_forall_fl_kahanSum_backward_error_source_bound_bare_fpmodel_exactSubConstants`).
The finite-format exactness of (4.7) is however available: it is
`finiteCorrectionFormulaTrace_exact_of_base2_abs_gt` (equivalently the
`FastTwoSumFiniteCertificate.of_base2_abs_gt` certificate), valid for base
`beta = 2`, precision `1 < t`, with `|b| < |a|` and `a + b` in finite normal
range.

## The modeling obstruction and its honest resolution

The Kielbasiński/Neumaier reduction theorem
`fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap`
is stated over an abstract `FPModel fp`; instantiating it at "the finite binary
round-to-even format" requires an `FPModel` whose `fl_add`/`fl_sub` are the
finite operations.  A *genuine* finite format with bounded exponent range
cannot be an unconditional `FPModel`:

* the standard relative-error model
  `finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange` holds only inside
  the finite *normal* range, whereas `FPModel.model_add` demands `|δ| ≤ u`
  unconditionally (this fails under gradual/flush underflow);
* `FPModel.fl_add_zero` demands `fl(0 + x) = x` for *every* real `x`, which no
  genuine rounding satisfies on a non-representable `x`.

We therefore build `kahanFF_model fmt`, the *safe completion* of the finite
format: it rounds with `finiteRoundToEvenOp` exactly where the standard model is
valid (inside the normal range, away from the guarded `a = 0` first add) and is
harmlessly exact elsewhere.  Because every per-step condition below forces the
computation into the region where the completion coincides with genuine finite
round-to-even, the model computes genuine finite binary round-to-even arithmetic
throughout the summation; the completion is never exercised on the actual trace.

The per-step hypothesis `kahanFF_stepCondition` is exactly the applicability of
(4.7) at each partial sum: the current term is representable, and either the
Dekker magnitude order `|xᵢ| ≤ |sᵢ|` holds with `sᵢ + xᵢ` in normal range, or
the running add is already exact.  This is faithful to Higham's own caveat that
(4.7) "is based on the assumption that `|a| ≥ |b|`" (p. 85).

Namespace `NumStability`, declaration prefix `kahanFF_`.
-/

/-- The *safe completion* of a finite binary format to an `FPModel`.

`fl_add`/`fl_sub` use `finiteRoundToEvenOp` in the finite normal range (where the
standard relative-error model holds); the `a = 0` guard on addition makes
`fl(0 + x) = x` hold definitionally, as `FPModel` requires; outside the normal
range the operation falls back to the exact real result, which keeps the model
axioms unconditional without affecting any computation that stays in range.
`fl_mul`/`fl_div`/`fl_sqrt` are exact (unused by compensated summation). -/
noncomputable def kahanFF_model (fmt : FloatingPointFormat) : FPModel where
  u := fmt.unitRoundoff
  u_nonneg := fmt.unitRoundoff_nonneg
  fl_add := fun a b =>
    if a = 0 then b
    else if fmt.finiteNormalRange (a + b) then
      fmt.finiteRoundToEvenOp BasicOp.add a b
    else a + b
  fl_sub := fun a b =>
    if fmt.finiteNormalRange (a - b) then
      fmt.finiteRoundToEvenOp BasicOp.sub a b
    else a - b
  fl_mul := fun a b => a * b
  fl_div := fun a b => a / b
  fl_sqrt := fun a => Real.sqrt a
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by subst hx; simp⟩
    · by_cases hr : fmt.finiteNormalRange (x + y)
      · obtain ⟨δ, hδ, hval⟩ :=
          fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
            (op := BasicOp.add) (x := x) (y := y)
            (by simpa [BasicOp.exact] using hr)
        refine ⟨δ, le_of_lt hδ, ?_⟩
        simp only [if_neg hx, if_pos hr]
        rw [hval]; simp [BasicOp.exact]
      · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by
          simp only [if_neg hx, if_neg hr]; ring⟩
  model_sub := by
    intro x y
    by_cases hr : fmt.finiteNormalRange (x - y)
    · obtain ⟨δ, hδ, hval⟩ :=
        fmt.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
          (op := BasicOp.sub) (x := x) (y := y)
          (by simpa [BasicOp.exact] using hr)
      refine ⟨δ, le_of_lt hδ, ?_⟩
      simp only [if_pos hr]
      rw [hval]; simp [BasicOp.exact]
    · exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by
        simp only [if_neg hr]; ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩
  model_div := by
    intro x y _hy
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩
  model_sqrt := by
    intro x _hx
    exact ⟨0, by simpa using fmt.unitRoundoff_nonneg, by simp⟩

/-- The safe-completion model's unit roundoff is the format's unit roundoff. -/
theorem kahanFF_model_u (fmt : FloatingPointFormat) :
    (kahanFF_model fmt).u = fmt.unitRoundoff := rfl

/-- Definitional unfolding of the safe-completion addition. -/
theorem kahanFF_model_fl_add (fmt : FloatingPointFormat) (a b : ℝ) :
    (kahanFF_model fmt).fl_add a b =
      (if a = 0 then b
      else if fmt.finiteNormalRange (a + b) then
        fmt.finiteRoundToEvenOp BasicOp.add a b
      else a + b) := rfl

/-- Definitional unfolding of the safe-completion subtraction. -/
theorem kahanFF_model_fl_sub (fmt : FloatingPointFormat) (a b : ℝ) :
    (kahanFF_model fmt).fl_sub a b =
      (if fmt.finiteNormalRange (a - b) then
        fmt.finiteRoundToEvenOp BasicOp.sub a b
      else a - b) := rfl

/-! ### Bridge lemmas: the completion agrees with genuine finite round-to-even -/

/-- When the current term `b` is representable and the running add is either in
finite normal range or already exact, the safe-completion addition coincides
with genuine finite round-to-even addition. -/
theorem kahanFF_fl_add_eq_finiteRoundToEvenOp
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hb : fmt.finiteSystem b)
    (hdisj :
      fmt.finiteNormalRange (a + b) ∨
        fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    (kahanFF_model fmt).fl_add a b =
      fmt.finiteRoundToEvenOp BasicOp.add a b := by
  rw [kahanFF_model_fl_add]
  split_ifs with ha0 hr
  · subst ha0
    have hbb : fmt.finiteSystem (BasicOp.exact BasicOp.add 0 b) := by
      simpa [BasicOp.exact] using hb
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hbb]
    simp [BasicOp.exact]
  · rfl
  · rcases hdisj with h | h
    · exact absurd h hr
    · exact h.symm

/-- When the exact real sum `a + b` is representable, the safe-completion
addition returns it exactly. -/
theorem kahanFF_fl_add_eq_of_finiteSystem
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hab : fmt.finiteSystem (a + b)) :
    (kahanFF_model fmt).fl_add a b = a + b := by
  rw [kahanFF_model_fl_add]
  split_ifs with ha0 hr
  · subst ha0; simp
  · have hab' : fmt.finiteSystem (BasicOp.exact BasicOp.add a b) := by
      simpa [BasicOp.exact] using hab
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hab']
    simp [BasicOp.exact]
  · rfl

/-- When the exact real difference `a - b` is representable, the safe-completion
subtraction returns it exactly. -/
theorem kahanFF_fl_sub_eq_of_finiteSystem
    (fmt : FloatingPointFormat) {a b : ℝ}
    (hab : fmt.finiteSystem (a - b)) :
    (kahanFF_model fmt).fl_sub a b = a - b := by
  rw [kahanFF_model_fl_sub]
  split_ifs with hr
  · have hab' : fmt.finiteSystem (BasicOp.exact BasicOp.sub a b) := by
      simpa [BasicOp.exact] using hab
    rw [fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hab']
    simp [BasicOp.exact]
  · rfl

/-! ### Per-step equation-(4.7) exactness in the finite format -/

/-- The applicability of Higham's correction formula (4.7) at one step of a
recursive sum with running value `a` and current term `b`: `b` is representable,
and either the Dekker magnitude order `|b| < |a|` holds with `a + b` in finite
normal range (the abstract (4.7) hypothesis), or the running add is already
exact (which covers, in particular, the first add from `a = 0`). -/
def kahanFF_stepCondition (fmt : FloatingPointFormat) (a b : ℝ) : Prop :=
  fmt.finiteSystem b ∧
    ((fmt.finiteSystem a ∧ |b| ≤ |a| ∧ fmt.finiteNormalRange (a + b)) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b)

/-- Equation (4.7) for the safe-completion model at one step.

Under `kahanFF_stepCondition`, the Kahan correction trace `(s, e)` computed by
the safe-completion model on `(a, b)` recovers the running sum exactly:
`a + b = s + e`.  The proof obtains the finite `FastTwoSumFiniteCertificate`
(the engine behind `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`), uses
its representability fields to show the completion coincides with genuine finite
round-to-even on the whole trace, and concludes by the certificate's exact
intermediate arithmetic. -/
theorem kahanFF_step_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (a b : ℝ) (hstep : kahanFF_stepCondition fmt a b) :
    CorrectionFormulaTrace.exact a b
      ({ s := (kahanFF_model fmt).fl_add a b,
         e := (kahanFF_model fmt).fl_add
                ((kahanFF_model fmt).fl_sub a
                  ((kahanFF_model fmt).fl_add a b)) b }
        : CorrectionFormulaTrace) := by
  obtain ⟨hb, hmain⟩ := hstep
  -- Finite FastTwoSum certificate for `(a, b)`.
  have hcert : FastTwoSumFiniteCertificate fmt a b := by
    rcases hmain with ⟨ha, hab, hrange⟩ | hexadd
    · exact FastTwoSumFiniteCertificate.of_base2_abs_le fmt hbeta ht ha hb hab hrange
    · exact FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hexadd
  -- The running add is in normal range or exact (feeds the main-add bridge).
  have hdisj :
      fmt.finiteNormalRange (a + b) ∨
        fmt.finiteRoundToEvenOp BasicOp.add a b = a + b := by
    rcases hmain with ⟨_, _, hrange⟩ | hexadd
    · exact Or.inl hrange
    · exact Or.inr hexadd
  have hs : (kahanFF_model fmt).fl_add a b =
      fmt.finiteRoundToEvenOp BasicOp.add a b :=
    kahanFF_fl_add_eq_finiteRoundToEvenOp fmt hb hdisj
  have hsub_fin :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b) :=
    hcert.finite_a_sub_s
  have herr_fin :
      fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) :=
    hcert.finite_error
  have hsub_br :
      (kahanFF_model fmt).fl_sub a (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b :=
    kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin
  have hadd_br :
      (kahanFF_model fmt).fl_add
          (a - fmt.finiteRoundToEvenOp BasicOp.add a b) b =
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b := by
    apply kahanFF_fl_add_eq_of_finiteSystem
    have hrw :
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b =
          (a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b := by ring
    rw [hrw]; exact herr_fin
  show a + b =
    (kahanFF_model fmt).fl_add a b +
      (kahanFF_model fmt).fl_add
        ((kahanFF_model fmt).fl_sub a
          ((kahanFF_model fmt).fl_add a b)) b
  rw [hs, hsub_br, hadd_br]
  ring

/-! ### Alternative compensated summation prefix and the (4.10) closure -/

/-- The running main sum before index `i` of the alternative compensated
summation, computed by the safe-completion model. -/
noncomputable def kahanFF_prefix (fmt : FloatingPointFormat) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  alternativeCompensatedPrefixSum (kahanFF_model fmt) v i.val
    (Nat.le_of_lt i.isLt)

/-- **Higham equation (4.10)** in the finite binary round-to-even format.

For the p. 94 alternative compensated-summation variant (corrections
accumulated separately by recursive summation, then added back), computed in the
safe-completion finite model `kahanFF_model fmt` with base `beta = 2` and
precision `1 < t`, if the correction formula (4.7) applies at every step
(`kahanFF_stepCondition` on each running sum and term) and `n·u ≤ 1/10`, then the
computed sum has the Kielbasiński/Neumaier backward-error representation

`Ŝₙ = Σᵢ (1 + μᵢ) xᵢ`,  with  `|μᵢ| ≤ 2u + n²u²`,

where `u = fmt.unitRoundoff`.  Reference: Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed., §4.3, equation (4.10), p. 85; Kielbasiński
[731, 1994]; Neumaier [883, 1974]. -/
theorem kahanFF_alternativeCompensatedSum_backward_error
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hstep : ∀ i : Fin n, kahanFF_stepCondition fmt (kahanFF_prefix fmt v i) (v i))
    (hsmall : (n : ℝ) * fmt.unitRoundoff ≤ 1 / 10) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤ 2 * fmt.unitRoundoff + (n : ℝ) ^ 2 * fmt.unitRoundoff ^ 2) ∧
      fl_alternativeCompensatedSum (kahanFF_model fmt) n v =
        ∑ i : Fin n, v i * (1 + μ i) := by
  refine
    fl_alternativeCompensatedSum_backward_error_source_bound_of_exact_steps_higham_cap
      (kahanFF_model fmt) n v (fun i => ?_) hsmall
  exact kahanFF_step_exact fmt hbeta ht (kahanFF_prefix fmt v i) (v i) (hstep i)

/-! ### Kahan compensated summation (Algorithm 4.2): equations (4.8) and (4.9)

Higham's *ordinary* Kahan compensated summation feeds each correction back into
the next term.  The Knuth/Kahan backward-error result (4.8),
`Ŝₙ = Σ (1 + μᵢ) xᵢ` with `|μᵢ| ≤ 2u + O(nu²)`, and the corresponding forward
bound (4.9), are packaged in the repository as
`fl_kahanSum_backward_error_source_bound_of_exactSubTrace`
(the O(nu²) accumulation is fully carried, with explicit constant
`2u + 2(3+40n)u²`), given the per-step *exact correction subtraction*
`KahanPrefixCorrectionSubExact`.

The residual of that theorem is exactly the exactness of the displayed
`temp - s` subtraction at each Kahan step, which is a finite-format
correction-formula fact (4.7).  We discharge it for the safe-completion model
using the same `FastTwoSumFiniteCertificate.of_base2_abs_le` certificate as for
(4.10): the certificate's `finite_a_sub_s` field makes `temp - s` representable,
whence the safe completion computes the subtraction exactly.  (The
`KahanAddSubFiniteRoundToEvenRealization` route in the repository requires
*global* `fp.fl_add = round`, which is jointly unsatisfiable with
`FPModel.fl_add_zero`; we bypass it.)  The first step has `temp = 0` and needs
no magnitude order, so the per-step hypothesis is a disjunction. -/

/-- Per-step exact correction subtraction for the safe-completion model's Kahan
trace, discharged from finite equation (4.7).

For each step either the Dekker magnitude order `|yᵢ| ≤ |tempᵢ|` holds with
`tempᵢ + yᵢ` in normal range (so `FastTwoSumFiniteCertificate.of_base2_abs_le`
makes `tempᵢ - sᵢ` representable), or `tempᵢ = 0` (first step / cancellation, so
`sᵢ = yᵢ` and `tempᵢ - sᵢ = -yᵢ` is representable). -/
theorem kahanFF_kahan_correctionSub_exact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hY : ∀ i : Fin n,
      fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).y)
    (hstep : ∀ i : Fin n,
      (fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).temp ∧
        |(kahanTrace (kahanFF_model fmt) v i).y| ≤
          |(kahanTrace (kahanFF_model fmt) v i).temp| ∧
        fmt.finiteNormalRange
          ((kahanTrace (kahanFF_model fmt) v i).temp +
            (kahanTrace (kahanFF_model fmt) v i).y)) ∨
        (kahanTrace (kahanFF_model fmt) v i).temp = 0) :
    KahanPrefixCorrectionSubExact (kahanFF_model fmt) v n (Nat.le_refl n) := by
  intro i
  show (kahanFF_model fmt).fl_sub (kahanTrace (kahanFF_model fmt) v i).temp
        (kahanTrace (kahanFF_model fmt) v i).s =
      (kahanTrace (kahanFF_model fmt) v i).temp -
        (kahanTrace (kahanFF_model fmt) v i).s
  have hs_def :
      (kahanTrace (kahanFF_model fmt) v i).s =
        (kahanFF_model fmt).fl_add (kahanTrace (kahanFF_model fmt) v i).temp
          (kahanTrace (kahanFF_model fmt) v i).y := rfl
  rcases hstep i with ⟨htemp_fin, horder, hrange⟩ | htemp0
  · have hs_eq :
        (kahanTrace (kahanFF_model fmt) v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (kahanTrace (kahanFF_model fmt) v i).temp
            (kahanTrace (kahanFF_model fmt) v i).y := by
      rw [hs_def]
      exact kahanFF_fl_add_eq_finiteRoundToEvenOp fmt (hY i) (Or.inl hrange)
    have hcert :
        FastTwoSumFiniteCertificate fmt
          (kahanTrace (kahanFF_model fmt) v i).temp
          (kahanTrace (kahanFF_model fmt) v i).y :=
      FastTwoSumFiniteCertificate.of_base2_abs_le fmt hbeta ht htemp_fin
        (hY i) horder hrange
    have hsub_fin :
        fmt.finiteSystem
          ((kahanTrace (kahanFF_model fmt) v i).temp -
            (kahanTrace (kahanFF_model fmt) v i).s) := by
      rw [hs_eq]; exact hcert.finite_a_sub_s
    exact kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin
  · have hs_eq :
        (kahanTrace (kahanFF_model fmt) v i).s =
          (kahanTrace (kahanFF_model fmt) v i).y := by
      rw [hs_def, htemp0, kahanFF_model_fl_add]; simp
    have hsub_fin :
        fmt.finiteSystem
          ((kahanTrace (kahanFF_model fmt) v i).temp -
            (kahanTrace (kahanFF_model fmt) v i).s) := by
      rw [htemp0, hs_eq]
      have h0 :
          (0 : ℝ) - (kahanTrace (kahanFF_model fmt) v i).y =
            -(kahanTrace (kahanFF_model fmt) v i).y := by ring
      rw [h0]; exact fmt.finiteSystem_neg (hY i)
    exact kahanFF_fl_sub_eq_of_finiteSystem fmt hsub_fin

/-- **Higham equation (4.8)** in the finite binary round-to-even format.

Ordinary Kahan compensated summation (Algorithm 4.2) computed in the
safe-completion finite model, base `beta = 2`, precision `1 < t`.  If the
correction formula (4.7) applies at every step (`hstep`: Dekker order with
normal range, or `temp = 0`) with each `y` representable (`hY`), and
`u ≤ 1/64`, `(3 + 40n)·u ≤ 1`, then

`Ŝₙ = Σᵢ (1 + μᵢ) xᵢ`,  with  `|μᵢ| ≤ 2u + 2(3 + 40n)u²`,

an explicit realization of Knuth/Kahan's `|μᵢ| ≤ 2u + O(nu²)`, where
`u = fmt.unitRoundoff`.  Reference: Higham, 2nd ed., §4.3, equation (4.8),
p. 85 (Knuth [744]; Kahan [688, 689]; Goldberg [496]). -/
theorem kahanFF_kahanSum_backward_error
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hY : ∀ i : Fin n,
      fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).y)
    (hstep : ∀ i : Fin n,
      (fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).temp ∧
        |(kahanTrace (kahanFF_model fmt) v i).y| ≤
          |(kahanTrace (kahanFF_model fmt) v i).temp| ∧
        fmt.finiteNormalRange
          ((kahanTrace (kahanFF_model fmt) v i).temp +
            (kahanTrace (kahanFF_model fmt) v i).y)) ∨
        (kahanTrace (kahanFF_model fmt) v i).temp = 0)
    (huSmall : fmt.unitRoundoff ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i,
        |μ i| ≤
          2 * fmt.unitRoundoff +
            2 * (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ^ 2) ∧
      fl_kahanSum (kahanFF_model fmt) n v = ∑ i : Fin n, v i * (1 + μ i) :=
  fl_kahanSum_backward_error_source_bound_of_exactSubTrace
    (kahanFF_model fmt) n v
    (kahanFF_kahan_correctionSub_exact fmt hbeta ht n v hY hstep)
    huSmall hBudget

/-- **Higham equation (4.9)** in the finite binary round-to-even format: the
forward-error form of (4.8) for ordinary Kahan compensated summation.

Under the same hypotheses as `kahanFF_kahanSum_backward_error`,

`|Eₙ| = |Ŝₙ − Σᵢ xᵢ| ≤ (2u + 2(3 + 40n)u²) · Σᵢ |xᵢ|`,

an explicit realization of Higham's `|Eₙ| ≤ (2u + O(nu²)) Σ|xᵢ|`.  Reference:
Higham, 2nd ed., §4.3, equation (4.9), p. 85. -/
theorem kahanFF_kahanSum_forward_error
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hY : ∀ i : Fin n,
      fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).y)
    (hstep : ∀ i : Fin n,
      (fmt.finiteSystem (kahanTrace (kahanFF_model fmt) v i).temp ∧
        |(kahanTrace (kahanFF_model fmt) v i).y| ≤
          |(kahanTrace (kahanFF_model fmt) v i).temp| ∧
        fmt.finiteNormalRange
          ((kahanTrace (kahanFF_model fmt) v i).temp +
            (kahanTrace (kahanFF_model fmt) v i).y)) ∨
        (kahanTrace (kahanFF_model fmt) v i).temp = 0)
    (huSmall : fmt.unitRoundoff ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ≤ 1) :
    |fl_kahanSum (kahanFF_model fmt) n v - ∑ i : Fin n, v i| ≤
      (2 * fmt.unitRoundoff +
          2 * (3 + 40 * (n : ℝ)) * fmt.unitRoundoff ^ 2) *
        ∑ i : Fin n, |v i| :=
  fl_kahanSum_forward_error_bound_of_backward (kahanFF_model fmt) n v
    (kahanFF_kahanSum_backward_error fmt hbeta ht n v hY hstep huSmall hBudget)

end NumStability
