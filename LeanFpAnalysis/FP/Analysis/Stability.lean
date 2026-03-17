-- Stability.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Error

namespace LeanFpAnalysis.FP

/-!
# Stability and Condition Number

Following Higham, "Accuracy and Stability of Numerical Algorithms", §1.7–§1.9.

We formalise the key concepts that classify how well an algorithm handles
the unavoidable rounding errors introduced by finite precision arithmetic:
backward stability and the condition number of a problem.
-/

-- ============================================================
-- §1.7  Backward error predicates
-- ============================================================

/-- Backward error bound for a computed result `xhat` for scalar problem `f` at input `a`.

    Asserts that there exists a perturbation Δa with |Δa| ≤ ε such that `xhat` is
    the *exact* solution to the perturbed problem `f(a + Δa)`:
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat

    The vector analog is `backwardErrorBoundedVec`. -/
def backwardErrorBounded (f : ℝ → ℝ) (a xhat ε : ℝ) : Prop :=
  ∃ Δa : ℝ, |Δa| ≤ ε ∧ f (a + Δa) = xhat

/-- Backward error bound for a computed vector result `xhat` for problem
    `f : (Fin n → ℝ) → (Fin m → ℝ)` at input `a`.

    Asserts that there exists a componentwise perturbation Δa with |Δa i| ≤ ε for all i,
    such that `xhat` is the *exact* solution to the perturbed problem `f(a + Δa)`:
      ∃ Δa, (∀ i, |Δa i| ≤ ε) ∧ f(fun i => a i + Δa i) = xhat

    The scalar analog is `backwardErrorBounded`. -/
def backwardErrorBoundedVec (n m : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ))
    (a : Fin n → ℝ) (xhat : Fin m → ℝ) (ε : ℝ) : Prop :=
  ∃ Δa : Fin n → ℝ, (∀ i, |Δa i| ≤ ε) ∧ f (fun i => a i + Δa i) = xhat

-- ============================================================
-- §1.7  Backward stability (scalar problems)
-- ============================================================

/-- An algorithm computing `f : ℝ → ℝ` at input `a` is **backward stable**
    if the computed result `xhat` is the exact answer for a slightly perturbed
    input.  The perturbation is required to be no larger than `c * u`:
      ∃ Δa, |Δa| ≤ c * u ∧ f(a + Δa) = xhat

    Typically the constant c depends on the algorithm; u is the unit roundoff. -/
def isBackwardStable (fp : FPModel) (f : ℝ → ℝ) (alg : ℝ → ℝ)
    (c : ℝ) : Prop :=
  ∀ a : ℝ, backwardErrorBounded f a (alg a) (c * fp.u)

-- ============================================================
-- §1.7  Backward stability (vector problems)
-- ============================================================

/-- Backward stability for a vector-to-vector problem `f : (Fin n → ℝ) → (Fin m → ℝ)`.

    The computed output `alg a` is the exact answer for a componentwise-perturbed
    input, with each component perturbed by at most `c * u`. -/
def isVectorBackwardStable (fp : FPModel) (n m : ℕ)
    (f : (Fin n → ℝ) → (Fin m → ℝ))
    (alg : (Fin n → ℝ) → (Fin m → ℝ))
    (c : ℝ) : Prop :=
  ∀ a : Fin n → ℝ, backwardErrorBoundedVec n m f a (alg a) (c * fp.u)

-- ============================================================
-- §1.9  Condition number of a scalar problem
-- ============================================================

/-- The condition number of a differentiable scalar problem `f` at input `a`.

    Defined as the relative change in output per unit relative change in input:
      κ(f, a) = |a * f'(a) / f(a)|

    A large condition number means the problem is ill-conditioned: small relative
    changes in input cause large relative changes in output, independently of
    the algorithm used.

    The derivative `f'` must be supplied by the caller (as a function `df`).
    Meaningful only when `f(a) ≠ 0`; the caller must enforce this. -/
noncomputable def condNumber (f df : ℝ → ℝ) (a : ℝ) : ℝ :=
  |a * df a / f a|

/-- A problem `f` is **well-conditioned** at `a` if its condition number is
    at most `κ_max`.  The threshold `κ_max` is problem- and context-dependent;
    typical values are O(1) to O(1/u) where u is the unit roundoff. -/
def isWellConditioned (f df : ℝ → ℝ) (a κ_max : ℝ) : Prop :=
  condNumber f df a ≤ κ_max

-- ============================================================
-- §1.7  Forward error from backward error + condition number
-- ============================================================

/-- **Fundamental theorem of backward error analysis** (Higham §1.7).

    If the computed result `xhat` has absolute backward error at most ε, i.e.,
      ∃ Δa, |Δa| ≤ ε ∧ f(a + Δa) = xhat,
    and `f` satisfies the linearisation bound
      ∀ Δa, |Δa| ≤ ε → |f(a + Δa) - f(a)| ≤ |df(a)| · |Δa|,
    then the relative forward error satisfies:
      relError xhat (f a) ≤ condNumber f df a · (ε / |a|).

    The linearisation hypothesis `hlin` encodes the first-order sensitivity of
    `f`: it holds exactly when `f` is linear, and (to first order in ε) for any
    smooth `f` via Taylor's theorem.

    Proof: let Δa witness the backward error.  Then
      |f(a+Δa) - f(a)| ≤ |df(a)| · |Δa| ≤ |df(a)| · ε.
    Dividing by |f(a)| and noting condNumber f df a · (ε/|a|) = |df(a)|·ε/|f(a)|
    (since condNumber = |a·df(a)/f(a)|) gives the result. -/
lemma forward_from_backward (f df : ℝ → ℝ) (a ε xhat : ℝ)
    (ha  : a ≠ 0)
    (hf  : f a ≠ 0)
    (hback : backwardErrorBounded f a xhat ε)
    (hlin  : ∀ Δa : ℝ, |Δa| ≤ ε → |f (a + Δa) - f a| ≤ |df a| * |Δa|) :
    relError xhat (f a) ≤ condNumber f df a * (ε / |a|) := by
    sorry

end LeanFpAnalysis.FP
