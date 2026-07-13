-- Algorithms/PNormPowerMethod.lean
--
-- Chapter 15 §15.2:  The p-norm power method (Boyd 1974) and Lemma 15.2.
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM,
-- 2002), Chapter 15 "Condition Number Estimation":
--   * §15.2, Algorithm 15.1 (p-norm power method), p. 289.  Given A and x₀,
--     iterate  y = A x,  z = Aᵀ dualp(y),  (test),  x = dualq(z),  producing
--     γ and x with γ ≤ ‖A‖_p and ‖A x‖_p = γ ‖x‖_p.
--   * §15.2, Lemma 15.2, p. 290-291.  For the kth-iteration vectors:
--       (a)  zₖᵀ xₖ = ‖yₖ‖_p,
--       (b)  ‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p ≤ ‖A‖_p     (1/p + 1/q = 1).
--     The first inequality in (b) is strict if convergence is not obtained on
--     the kth iteration.
--   * §15.2, p. 291: "the scalars γₖ = ‖yₖ‖_p form an increasing and convergent
--     sequence."  Here `‖A‖_p` is the operator p-norm, so each γₖ is a genuine
--     lower bound on it.
--
-- The `dualp` operator (Higham §15.2, p. 289) denotes any vector of unit
-- q-norm attaining equality in the Hölder inequality xᵀy ≤ ‖x‖_p ‖y‖_q, i.e.
--   dualp(x)ᵀ x = ‖x‖_p  and  ‖dualp(x)‖_q = 1.
--
-- HONEST STRENGTH.  Lemma 15.2 is proved here at exactly its printed strength.
-- Its proof (Higham p. 291) uses only: the two `dualp`/`dualq` attainment /
-- unit-norm relations, the Hölder inequality, and operator-norm
-- submultiplicativity ‖A x‖_p ≤ ‖A‖_p ‖x‖_p.  We capture *precisely* these
-- printed properties in the bundle `PNormPair` (never the conclusion itself —
-- the chain inequality is derived, not assumed) and prove Lemma 15.2 (a), (b),
-- the monotone increasing property of γₖ, its upper bound ‖A‖_p, and the strict
-- form of the first inequality of (b).  We then discharge every abstract
-- hypothesis for the concrete norms p = 1 and p = 2, exhibiting non-vacuous
-- instances (`pNormPair_two`, `pNormPair_one`), so the concrete Lemma 15.2 and
-- the genuine operator-norm lower bounds `gammaSeq_le_opP` hold unconditionally.
--
-- General-p residual.  For arbitrary real p ∈ (1, ∞) Mathlib currently lacks a
-- packaged mixed-p vector dual norm together with its operator p-norm and the
-- general Hölder duality with attained `dualp`.  The abstract tier is stated so
-- that supplying that data (the four printed dual/Hölder/operator facts) yields
-- the full Lemma 15.2 immediately; the two endpoint instances p = 1, 2 are
-- built here from repository/Mathlib tooling.  This residual is *only* the
-- construction of the general-p `dualp`, not any part of Lemma 15.2's logic.
--
-- IMPORT-ONLY.  This file adds correctly Chapter-15-labelled theorems.  It
-- reuses (never edits) `Algorithms/CondEstimation.lean` (its `oneNormVec`,
-- `signVec`, `basisVec`, `argmaxAbs`, `oneNormVec_matVec_le`, ...) and
-- `Analysis/MatrixAlgebra.lean` (`vecNorm2`, `opNorm2`, Cauchy-Schwarz,
-- `matMulVec`, ...).  The existing condition-estimation modules carry the same
-- underlying mathematics but mislabel §15.2/§15.3 material as "Chapter 14";
-- this module gives the §15.2 statements their correct labels.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.CondEstimation

namespace LeanFpAnalysis.FP
namespace Ch15

open scoped BigOperators

-- ============================================================
-- §15.2  Abstract dual-norm data for Algorithm 15.1
-- ============================================================

/-- **Dual-norm data for the p-norm power method** (Higham §15.2, p. 289).

    Bundles a square matrix `A` together with the p-norm `pN = ‖·‖_p`, the dual
    q-norm `qN = ‖·‖_q` (`1/p + 1/q = 1`), the operator p-norm `opP = ‖A‖_p`, and
    the two dual maps `dp = dualp`, `dq = dualq`, subject to *exactly* the
    printed properties that Lemma 15.2's proof invokes (Higham p. 289-291):

    * `pN_nonneg`  — `‖·‖_p` is a nonnegative functional;
    * `dp_attains` — `dualp(v)ᵀ v = ‖v‖_p`   (Hölder equality for `dualp`);
    * `dp_qunit`   — `‖dualp(v)‖_q ≤ 1`       (unit q-norm normalization; `≤`
                     suffices for the proof and is weaker than Higham's `= 1`);
    * `dq_attains` — `dualq(w)ᵀ w = ‖w‖_q`   (Hölder equality for `dualq`);
    * `dq_punit`   — `‖dualq(w)‖_p = 1`       (the iterates have unit p-norm);
    * `holder`     — `uᵀ v ≤ ‖u‖_q ‖v‖_p`     (Hölder inequality);
    * `op_bound`   — `‖A v‖_p ≤ ‖A‖_p ‖v‖_p`  (operator-norm submultiplicativity).

    None of these fields is the Lemma 15.2 chain; the chain is derived below. -/
structure PNormPair (n : ℕ) where
  /-- The matrix `A ∈ ℝ^{n×n}` whose p-norm is being estimated. -/
  A     : Fin n → Fin n → ℝ
  /-- The vector p-norm `‖·‖_p`. -/
  pN    : (Fin n → ℝ) → ℝ
  /-- The dual vector q-norm `‖·‖_q` (`1/p + 1/q = 1`). -/
  qN    : (Fin n → ℝ) → ℝ
  /-- The operator p-norm `‖A‖_p`. -/
  opP   : ℝ
  /-- The dual map `dualp`: unit q-norm, attaining Hölder equality. -/
  dp    : (Fin n → ℝ) → (Fin n → ℝ)
  /-- The dual map `dualq`: unit p-norm, attaining Hölder equality. -/
  dq    : (Fin n → ℝ) → (Fin n → ℝ)
  /-- `‖·‖_p` is nonnegative. -/
  pN_nonneg   : ∀ v, 0 ≤ pN v
  /-- Higham §15.2, p. 289: `dualp(v)ᵀ v = ‖v‖_p`. -/
  dp_attains  : ∀ v, (∑ i : Fin n, dp v i * v i) = pN v
  /-- Higham §15.2, p. 289: `‖dualp(v)‖_q = 1` (here weakened to `≤ 1`). -/
  dp_qunit    : ∀ v, qN (dp v) ≤ 1
  /-- Dual attainment for `dualq`: `dualq(w)ᵀ w = ‖w‖_q`. -/
  dq_attains  : ∀ w, (∑ i : Fin n, dq w i * w i) = qN w
  /-- The iterate `x = dualq(z)` has unit p-norm: `‖dualq(w)‖_p = 1`. -/
  dq_punit    : ∀ w, pN (dq w) = 1
  /-- Hölder inequality: `uᵀ v ≤ ‖u‖_q ‖v‖_p`. -/
  holder      : ∀ u v, (∑ i : Fin n, u i * v i) ≤ qN u * pN v
  /-- Operator-norm bound: `‖A v‖_p ≤ ‖A‖_p ‖v‖_p`. -/
  op_bound    : ∀ v, pN (fun i => ∑ j : Fin n, A i j * v j) ≤ opP * pN v

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

/-- `y = A x` (Algorithm 15.1, first line of the loop). -/
noncomputable def yof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, P.A i j * x j

/-- `z = Aᵀ dualp(y)` (Algorithm 15.1, second line of the loop):
    `zⱼ = ∑ᵢ Aᵢⱼ dualp(y)ᵢ`. -/
noncomputable def zof (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => ∑ i : Fin n, P.A i j * P.dp (P.yof x) i

/-- The next iterate `x = dualq(z)` (Algorithm 15.1, last line of the loop). -/
noncomputable def xnext (x : Fin n → ℝ) : Fin n → ℝ := P.dq (P.zof x)

/-- State carried by Algorithm 15.1: the current iterate `x` and the running
    estimate `γ` (Higham §15.2, p. 289). -/
structure State (n : ℕ) where
  /-- Current iterate `x` (kept at unit p-norm). -/
  x : Fin n → ℝ
  /-- Running lower-bound estimate `γ`. -/
  γ : ℝ

/-- **One step of Algorithm 15.1** (Higham §15.2, p. 289), the p-norm power
    method loop body.  Given the current `x`:

      `y = A x;  z = Aᵀ dualp(y);  γ = ‖y‖_p;`
      `if ‖z‖_q ≤ zᵀ x then (converged, return x)  else x = dualq(z)`.

    Returns the updated state together with the convergence flag.  The estimate
    `γ = ‖y‖_p` is set on every step (as in Higham's code, where `γ = ‖y‖_p` is
    recorded before the test). -/
noncomputable def powerStep (st : State n) : State n × Bool :=
  let y := P.yof st.x
  let z := fun j => ∑ i : Fin n, P.A i j * P.dp y i
  let γ := P.pN y
  let zTx := ∑ j : Fin n, z j * st.x j
  if P.qN z ≤ zTx then
    (⟨st.x, γ⟩, true)
  else
    (⟨P.dq z, γ⟩, false)

/-- The estimate returned by `powerStep` is always `γ = ‖A x‖_p`, whichever
    branch is taken (Algorithm 15.1 records `γ = ‖y‖_p`). -/
lemma powerStep_gamma_eq (st : State n) :
    (P.powerStep st).1.γ = P.pN (P.yof st.x) := by
  simp only [powerStep]
  split_ifs <;> rfl

/-- **Algorithm 15.1 postcondition — lower bound** (Higham §15.2, p. 289:
    "computes γ … such that γ ≤ ‖A‖_p").

    If the current iterate has unit p-norm, the estimate returned by one step of
    Algorithm 15.1 satisfies `γ ≤ ‖A‖_p`. -/
theorem powerStep_gamma_le_opP (st : State n) (hx : P.pN st.x = 1) :
    (P.powerStep st).1.γ ≤ P.opP := by
  rw [P.powerStep_gamma_eq st]
  have hb := P.op_bound st.x
  rw [hx, mul_one] at hb
  simpa [yof] using hb

/-- **Algorithm 15.1 postcondition — the scaling identity** (Higham §15.2,
    p. 289: "computes γ … such that … ‖A x‖_p = γ ‖x‖_p").

    With the current iterate at unit p-norm, the returned estimate satisfies
    `‖A x‖_p = γ · ‖x‖_p` (both sides equal `γ = ‖A x‖_p`). -/
theorem powerStep_scaling (st : State n) (hx : P.pN st.x = 1) :
    P.pN (P.yof st.x) = (P.powerStep st).1.γ * P.pN st.x := by
  rw [P.powerStep_gamma_eq st, hx, mul_one]

/-- **Adjoint identity** for the transpose step (Algorithm 15.1).

    `zᵀ v = dualp(y)ᵀ (A v)`, i.e. `(Aᵀ u)ᵀ v = uᵀ (A v)`.  This is the pure
    algebraic fact underlying `z = Aᵀ dualp(y)`; it is proved, not assumed. -/
lemma z_dot (x v : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * v j)
      = ∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * v j) := by
  unfold zof
  have h1 : ∀ j : Fin n, (∑ i : Fin n, P.A i j * P.dp (P.yof x) i) * v j
      = ∑ i : Fin n, (P.A i j * P.dp (P.yof x) i) * v j :=
    fun j => by rw [Finset.sum_mul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Lemma 15.2 (a)** (Higham §15.2, p. 290).

    `zₖᵀ xₖ = ‖yₖ‖_p`.

    Proof (Higham p. 291): `zₖᵀ xₖ = dualp(yₖ)ᵀ A xₖ = dualp(yₖ)ᵀ yₖ = ‖yₖ‖_p`,
    the last step by the `dualp` attainment relation. -/
theorem lemma152a (x : Fin n → ℝ) :
    (∑ j : Fin n, P.zof x j * x j) = P.pN (P.yof x) := by
  rw [P.z_dot x x]
  have hyof : (∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * x j))
       = ∑ i : Fin n, P.dp (P.yof x) i * P.yof x i := rfl
  rw [hyof, P.dp_attains]

/-- **Lemma 15.2 (b)** (Higham §15.2, p. 290-291), the increasing chain.

    For an iterate `x` with `‖x‖_p = 1`,
      `‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p ≤ ‖A‖_p`.

    Proof (Higham p. 291):
      `‖yₖ‖_p = zₖᵀ xₖ ≤ ‖zₖ‖_q ‖xₖ‖_p = ‖zₖ‖_q`      (a) + Hölder + ‖xₖ‖_p = 1
             `= zₖᵀ xₖ₊₁ ≤ ‖dualp(yₖ)‖_q ‖A xₖ₊₁‖_p ≤ ‖yₖ₊₁‖_p`   dualq attains,
                                                                    Hölder,
                                                                    ‖dualp‖_q ≤ 1
             `≤ ‖A‖_p`.                                         operator bound. -/
theorem lemma152b (x : Fin n → ℝ) (hx : P.pN x = 1) :
    P.pN (P.yof x) ≤ P.qN (P.zof x) ∧
    P.qN (P.zof x) ≤ P.pN (P.yof (P.xnext x)) ∧
    P.pN (P.yof (P.xnext x)) ≤ P.opP := by
  -- (i)  ‖yₖ‖_p = zᵀxₖ ≤ ‖zₖ‖_q ‖xₖ‖_p = ‖zₖ‖_q
  have step1 : P.pN (P.yof x) ≤ P.qN (P.zof x) := by
    rw [← P.lemma152a x]
    calc (∑ j : Fin n, P.zof x j * x j)
        ≤ P.qN (P.zof x) * P.pN x := P.holder _ _
      _ = P.qN (P.zof x) := by rw [hx, mul_one]
  -- ‖zₖ‖_q = zₖᵀ xₖ₊₁  (xₖ₊₁ = dualq(zₖ) attains the dual norm of zₖ)
  have hz_xnext : (∑ j : Fin n, P.zof x j * P.xnext x j) = P.qN (P.zof x) := by
    unfold xnext
    rw [show (∑ j : Fin n, P.zof x j * P.dq (P.zof x) j)
          = ∑ j : Fin n, P.dq (P.zof x) j * P.zof x j from
        Finset.sum_congr rfl (fun j _ => by ring)]
    exact P.dq_attains _
  -- (ii)  ‖zₖ‖_q = zₖᵀ xₖ₊₁ = dualp(yₖ)ᵀ (A xₖ₊₁) ≤ ‖dualp(yₖ)‖_q ‖yₖ₊₁‖_p ≤ ‖yₖ₊₁‖_p
  have step2 : P.qN (P.zof x) ≤ P.pN (P.yof (P.xnext x)) := by
    rw [← hz_xnext, P.z_dot x (P.xnext x)]
    calc (∑ i : Fin n, P.dp (P.yof x) i * (∑ j : Fin n, P.A i j * P.xnext x j))
        ≤ P.qN (P.dp (P.yof x)) *
            P.pN (fun i => ∑ j : Fin n, P.A i j * P.xnext x j) := P.holder _ _
      _ ≤ 1 * P.pN (P.yof (P.xnext x)) :=
          mul_le_mul_of_nonneg_right (P.dp_qunit _) (P.pN_nonneg _)
      _ = P.pN (P.yof (P.xnext x)) := one_mul _
  -- (iii)  ‖yₖ₊₁‖_p = ‖A xₖ₊₁‖_p ≤ ‖A‖_p ‖xₖ₊₁‖_p = ‖A‖_p   (‖xₖ₊₁‖_p = 1)
  have step3 : P.pN (P.yof (P.xnext x)) ≤ P.opP := by
    have hb := P.op_bound (P.xnext x)
    have hxn : P.pN (P.xnext x) = 1 := P.dq_punit _
    rw [hxn, mul_one] at hb
    exact hb
  exact ⟨step1, step2, step3⟩

/-- **Convergence-test equality** (Higham §15.2, p. 291).

    Because `‖yₖ‖_p = zₖᵀ xₖ ≤ ‖zₖ‖_q` always holds (Lemma 15.2(a) + Hölder,
    with `‖xₖ‖_p = 1`), the algorithm's test `‖zₖ‖_q ≤ zₖᵀ xₖ` is equivalent to
    the equality `‖zₖ‖_q = zₖᵀ xₖ`.  This is the observation Higham uses to note
    that the scalar convergence test is really testing the vector equation. -/
theorem convergence_test_iff (x : Fin n → ℝ) (hx : P.pN x = 1) :
    P.qN (P.zof x) ≤ (∑ j : Fin n, P.zof x j * x j)
      ↔ P.qN (P.zof x) = (∑ j : Fin n, P.zof x j * x j) := by
  have hle : (∑ j : Fin n, P.zof x j * x j) ≤ P.qN (P.zof x) := by
    rw [P.lemma152a x]
    exact (P.lemma152b x hx).1
  constructor
  · intro h; exact le_antisymm h hle
  · intro h; exact le_of_eq h

-- ============================================================
-- §15.2  The estimate sequence γₖ = ‖yₖ‖_p: increasing, bounded by ‖A‖_p
-- ============================================================

/-- The iterate sequence of Algorithm 15.1 (functional iteration of `xnext`):
    `x₀` given, `xₖ₊₁ = dualq(zₖ)`.  Each iterate after the start has unit
    p-norm; see `xseq_punit`. -/
noncomputable def xseq (x0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => P.xnext (xseq x0 k)

/-- Every iterate has unit p-norm, `‖xₖ‖_p = 1` (given `‖x₀‖_p = 1`).

    Higham normalizes `x₀ = x₀/‖x₀‖_p` and each `xₖ₊₁ = dualq(zₖ)` has unit
    p-norm by construction. -/
lemma xseq_punit (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.pN (P.xseq x0 k) = 1 := by
  cases k with
  | zero => simpa [xseq] using hx0
  | succ k => simpa [xseq] using P.dq_punit _

/-- The estimate sequence `γₖ = ‖yₖ‖_p = ‖A xₖ‖_p` (Higham §15.2, p. 291). -/
noncomputable def gammaSeq (x0 : Fin n → ℝ) (k : ℕ) : ℝ :=
  P.pN (P.yof (P.xseq x0 k))

/-- **Increasing sequence of norm approximations** (Higham §15.2, p. 291).

    `γₖ ≤ γₖ₊₁`.  "For all values of p the power method has the desirable
    property of generating an increasing sequence of norm approximations."
    Immediate from Lemma 15.2(b): `‖yₖ‖_p ≤ ‖zₖ‖_q ≤ ‖yₖ₊₁‖_p`. -/
theorem gammaSeq_mono (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.gammaSeq x0 (k + 1) := by
  have hk := P.xseq_punit x0 hx0 k
  have hb := P.lemma152b (P.xseq x0 k) hk
  have h13 : P.pN (P.yof (P.xseq x0 k)) ≤ P.pN (P.yof (P.xnext (P.xseq x0 k))) :=
    le_trans hb.1 hb.2.1
  simpa [gammaSeq, xseq] using h13

/-- **Genuine lower bound on the operator p-norm** (Higham §15.2, p. 290-291).

    `γₖ ≤ ‖A‖_p` for every `k`: each estimate under-estimates the true operator
    p-norm.  This is the guarantee `γ ≤ ‖A‖_p` promised by Algorithm 15.1. -/
theorem gammaSeq_le_opP (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 k ≤ P.opP := by
  cases k with
  | zero =>
    have hb := P.op_bound (P.xseq x0 0)
    rw [show P.xseq x0 0 = x0 from rfl, hx0, mul_one] at hb
    simpa [gammaSeq, yof] using hb
  | succ k =>
    have hk := P.xseq_punit x0 hx0 k
    have hb := P.lemma152b (P.xseq x0 k) hk
    simpa [gammaSeq, xseq] using hb.2.2

/-- **Monotone from the start** (Higham §15.2, p. 291): `γ₀ ≤ γₖ` for all `k`. -/
theorem gammaSeq_ge_start (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1) (k : ℕ) :
    P.gammaSeq x0 0 ≤ P.gammaSeq x0 k := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => exact le_trans ih (P.gammaSeq_mono x0 hx0 k)

end PNormPair

-- ============================================================
-- §15.2  Strict first inequality of Lemma 15.2(b)
-- ============================================================

/-- **Strictness in Lemma 15.2(b)** (Higham §15.2, p. 291).

    "The first inequality in (b) is strict if convergence is not obtained on the
    kth iteration."  Higham identifies (p. 291) the convergence test
    `‖zₖ‖_q ≤ zₖᵀ xₖ`, equivalently `‖zₖ‖_q ≤ ‖yₖ‖_p` by (a).  Its negation,
    `‖yₖ‖_p < ‖zₖ‖_q`, is precisely the strict first inequality.  We state this
    as the honest equivalence: non-convergence (`¬ ‖zₖ‖_q ≤ ‖yₖ‖_p`) is exactly
    the strict inequality `‖yₖ‖_p < ‖zₖ‖_q`.  Combined with
    `convergence_test_iff` (which, using `‖xₖ‖_p = 1`, identifies the test
    `‖zₖ‖_q ≤ zₖᵀ xₖ` with `‖zₖ‖_q ≤ ‖yₖ‖_p`), this is Higham's remark that the
    first inequality of (b) is strict precisely when the kth step does not
    converge. -/
theorem lemma152b_strict {n : ℕ} (P : PNormPair n) (x : Fin n → ℝ) :
    (¬ P.qN (P.zof x) ≤ P.pN (P.yof x)) ↔ P.pN (P.yof x) < P.qN (P.zof x) := by
  constructor
  · intro h; exact lt_of_not_ge h
  · intro h; exact not_le.mpr h

-- ============================================================
-- §15.2  Concrete instance p = 2 (Euclidean / spectral norm)
-- ============================================================

/-- Fixed unit vector `e₀` (used as the `dualq`/`dualp` value at the zero vector,
    Higham's "extreme point of the unit ball" convention). -/
noncomputable def e0Vec {n : ℕ} (hn : 0 < n) : Fin n → ℝ :=
  fun i => if i = ⟨0, hn⟩ then 1 else 0

lemma vecNorm2_e0 {n : ℕ} (hn : 0 < n) : vecNorm2 (e0Vec hn) = 1 := by
  unfold vecNorm2 vecNorm2Sq e0Vec
  have hsum : (∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) ^ 2) = 1 := by
    have hcongr : (∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) ^ 2)
        = ∑ i : Fin n, (if i = ⟨0, hn⟩ then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> norm_num
    rw [hcongr]; simp
  rw [hsum]; exact Real.sqrt_one

lemma vecNorm2_pos_of_ne {n : ℕ} (v : Fin n → ℝ) (h : ¬ v = 0) :
    0 < vecNorm2 v := by
  rcases lt_or_eq_of_le (vecNorm2_nonneg v) with hlt | heq
  · exact hlt
  · exfalso; apply h; funext i
    exact (vecNorm2_eq_zero_iff v).mp heq.symm i

/-- The `dualp = dualq` map for `p = 2`: `v ↦ v/‖v‖₂` (a fixed unit vector at
    `v = 0`).  For the Euclidean norm the dual pair is `q = 2`, and the unique
    unit-norm Hölder-equality vector is the normalized `v`. -/
noncomputable def normalize2 {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) : Fin n → ℝ :=
  if v = 0 then e0Vec hn else fun i => (vecNorm2 v)⁻¹ * v i

lemma normalize2_unit {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    vecNorm2 (normalize2 hn v) = 1 := by
  unfold normalize2
  split_ifs with h
  · exact vecNorm2_e0 hn
  · exact vecNorm2_inv_smul_self_of_pos v (vecNorm2_pos_of_ne v h)

lemma normalize2_attains {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    (∑ i : Fin n, normalize2 hn v i * v i) = vecNorm2 v := by
  unfold normalize2
  split_ifs with h
  · subst h
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    symm
    have hz : (0 : Fin n → ℝ) = (fun _ : Fin n => (0:ℝ)) := rfl
    rw [hz, vecNorm2_zero]
  · exact vecInnerProduct_inv_smul_self_eq_norm v (vecNorm2_pos_of_ne v h)

/-- Cauchy-Schwarz as the Hölder inequality for `p = q = 2` (one-sided):
    `uᵀ v ≤ ‖u‖₂ ‖v‖₂`. -/
lemma holder_two {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ vecNorm2 u * vecNorm2 v :=
  le_trans (le_abs_self _) (abs_vecInnerProduct_le_vecNorm2_mul u v)

/-- The `p = 2` operator bound in the `yof`-shape:
    `‖A v‖₂ ≤ ‖A‖₂ ‖v‖₂`, with `‖A‖₂ = opNorm2 A` the exact ℓ² operator norm. -/
lemma opBound_two {n : ℕ} (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    vecNorm2 (fun i => ∑ j : Fin n, A i j * v j) ≤ opNorm2 A * vecNorm2 v := by
  simpa [matMulVec] using opNorm2Le_opNorm2 A v

/-- **The 2-norm power method as a `PNormPair`** (Higham §15.2, `p = 2`).

    For `p = 2` the algorithm "reduces to the usual power method applied to
    AᵀA" (Higham p. 289).  Here `‖·‖_p = ‖·‖_q = ‖·‖₂` and `‖A‖_p = opNorm2 A`
    is the exact ℓ² (spectral) operator norm from `MatrixAlgebra`.  All seven
    dual/Hölder/operator hypotheses are discharged from repository lemmas, so
    Lemma 15.2, `gammaSeq_mono`, and `gammaSeq_le_opP` hold for this concrete
    instance — a non-vacuous witness. -/
noncomputable def pNormPair_two {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := vecNorm2
  qN := vecNorm2
  opP := opNorm2 A
  dp := normalize2 hn
  dq := normalize2 hn
  pN_nonneg := vecNorm2_nonneg
  dp_attains := normalize2_attains hn
  dp_qunit := fun v => le_of_eq (normalize2_unit hn v)
  dq_attains := normalize2_attains hn
  dq_punit := normalize2_unit hn
  holder := holder_two
  op_bound := opBound_two A

/-- **Lemma 15.2 for `p = 2`** (Higham §15.2, p. 290-291), stated directly in
    the 2-norm.  For a unit vector `x` (`‖x‖₂ = 1`):
      `‖A x‖₂ ≤ ‖z‖₂ ≤ ‖A xₖ₊₁‖₂ ≤ ‖A‖₂`,
    where `z = Aᵀ (Ax/‖Ax‖₂)` and `xₖ₊₁ = normalize₂(z)`, together with
    `(a) zᵀ x = ‖A x‖₂`.  Genuinely non-vacuous: it is `lemma152b` at the
    concrete instance `pNormPair_two`. -/
theorem lemma152_two {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (hx : vecNorm2 x = 1) :
    (∑ j : Fin n, (pNormPair_two hn A).zof x j * x j)
        = vecNorm2 ((pNormPair_two hn A).yof x) ∧
    vecNorm2 ((pNormPair_two hn A).yof x) ≤ vecNorm2 ((pNormPair_two hn A).zof x) ∧
    vecNorm2 ((pNormPair_two hn A).zof x)
        ≤ vecNorm2 ((pNormPair_two hn A).yof ((pNormPair_two hn A).xnext x)) ∧
    vecNorm2 ((pNormPair_two hn A).yof ((pNormPair_two hn A).xnext x))
        ≤ opNorm2 A :=
  ⟨(pNormPair_two hn A).lemma152a x, (pNormPair_two hn A).lemma152b x hx⟩

/-- **2-norm estimate is a lower bound on `‖A‖₂`** (Higham §15.2, p. 291).

    Every estimate `γₖ = ‖A xₖ‖₂` produced by the 2-norm power method
    under-estimates the exact spectral norm `opNorm2 A`. -/
theorem gammaSeq_two_le_opNorm2 {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) (k : ℕ) :
    (pNormPair_two hn A).gammaSeq x0 k ≤ opNorm2 A :=
  (pNormPair_two hn A).gammaSeq_le_opP x0 hx0 k

/-- **2-norm estimates increase** (Higham §15.2, p. 291): `γₖ ≤ γₖ₊₁`. -/
theorem gammaSeq_two_mono {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : vecNorm2 x0 = 1) (k : ℕ) :
    (pNormPair_two hn A).gammaSeq x0 k ≤ (pNormPair_two hn A).gammaSeq x0 (k + 1) :=
  (pNormPair_two hn A).gammaSeq_mono x0 hx0 k

-- ============================================================
-- §15.2  Concrete instance p = 1 (1-norm / ∞-norm dual)
-- ============================================================

/-- `dualp` for `p = 1` is the sign vector (unit ∞-norm, attaining `‖·‖₁`).
    Reuses `signVec` from `Algorithms/CondEstimation`. -/
lemma sign_attains_one {n : ℕ} (v : Fin n → ℝ) :
    (∑ i : Fin n, signVec v i * v i) = oneNormVec v := by
  unfold oneNormVec
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]; exact mul_signVec_eq_abs v i

lemma sign_qunit_one {n : ℕ} (v : Fin n → ℝ) : infNormVec (signVec v) ≤ 1 := by
  apply infNormVec_le_of_abs_le
  · intro i; rw [abs_signVec]
  · exact zero_le_one

/-- `dualq` for `p = 1`: `sign(w_J) · e_J` where `J` is the (smallest) index
    with `|w_J| = ‖w‖_∞`.  This is Higham's `x = ±e_j` extreme-point choice
    (Algorithm 15.1, `dualq(z)` for `p = 1`); the sign makes it attain `‖w‖_∞`
    rather than merely `|w_J|`, and it has unit 1-norm. -/
noncomputable def dualq_one {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => signVec w (argmaxAbs hn w) * basisVec (argmaxAbs hn w) i

lemma dualq_one_punit {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    oneNormVec (dualq_one hn w) = 1 := by
  unfold oneNormVec dualq_one
  have hs : |signVec w (argmaxAbs hn w)| = 1 := abs_signVec w _
  calc (∑ i : Fin n, |signVec w (argmaxAbs hn w) * basisVec (argmaxAbs hn w) i|)
      = ∑ i : Fin n, |basisVec (argmaxAbs hn w) i| := by
        apply Finset.sum_congr rfl; intro i _
        rw [abs_mul, hs, one_mul]
    _ = oneNormVec (basisVec (argmaxAbs hn w)) := rfl
    _ = 1 := oneNormVec_basisVec _

lemma dualq_one_attains {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    (∑ i : Fin n, dualq_one hn w i * w i) = infNormVec w := by
  unfold dualq_one
  set J := argmaxAbs hn w with hJdef
  have hstep : (∑ i : Fin n, signVec w J * basisVec J i * w i)
      = signVec w J * w J := by
    rw [show (∑ i : Fin n, signVec w J * basisVec J i * w i)
          = ∑ i : Fin n, signVec w J * (basisVec J i * w i) from
        Finset.sum_congr rfl (fun i _ => by ring)]
    rw [← Finset.mul_sum]
    congr 1
    unfold basisVec
    rw [show (∑ i : Fin n, (if i = J then (1:ℝ) else 0) * w i)
          = ∑ i : Fin n, (if i = J then w i else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)]
    rw [Finset.sum_ite_eq' Finset.univ J w]
    simp
  rw [hstep, mul_comm, mul_signVec_eq_abs]
  -- |w J| = ‖w‖_∞ since J is the argmax of |·|
  apply le_antisymm
  · exact abs_le_infNormVec w J
  · apply infNormVec_le_of_abs_le
    · intro i; exact argmaxAbs_spec hn w i
    · exact abs_nonneg _

/-- Hölder for `p = 1`, `q = ∞`: `uᵀ v ≤ ‖u‖_∞ ‖v‖₁`. -/
lemma holder_one {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ infNormVec u * oneNormVec v := by
  calc (∑ i : Fin n, u i * v i)
      ≤ ∑ i : Fin n, |u i * v i| := Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ = ∑ i : Fin n, |u i| * |v i| := by
        apply Finset.sum_congr rfl; intro i _; exact abs_mul _ _
    _ ≤ ∑ i : Fin n, infNormVec u * |v i| := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (abs_le_infNormVec u i) (abs_nonneg _)
    _ = infNormVec u * oneNormVec v := by
        unfold oneNormVec; rw [Finset.mul_sum]

/-- **The 1-norm power method as a `PNormPair`** (Higham §15.2, `p = 1`).

    For `p = 1` the dual is `q = ∞`; here `‖·‖_p = oneNormVec`,
    `‖·‖_q = infNormVec`, `‖A‖_p = oneNorm A` (max column sum), `dualp = signVec`
    and `dualq(z) = ±e_j` at the largest-magnitude entry.  All hypotheses are
    discharged from `CondEstimation`/`MatrixAlgebra` lemmas (the operator bound
    is `oneNormVec_matVec_le`), so Lemma 15.2 and the lower bound
    `gammaSeq_le_opP` hold for this concrete instance too. -/
noncomputable def pNormPair_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := oneNormVec
  qN := infNormVec
  opP := oneNorm A
  dp := signVec
  dq := dualq_one hn
  pN_nonneg := oneNormVec_nonneg
  dp_attains := sign_attains_one
  dp_qunit := sign_qunit_one
  dq_attains := dualq_one_attains hn
  dq_punit := dualq_one_punit hn
  holder := holder_one
  op_bound := fun v => oneNormVec_matVec_le hn A v

/-- **Lemma 15.2 for `p = 1`** (Higham §15.2, p. 290-291), stated in the
    1-norm.  For a unit vector `x` (`‖x‖₁ = 1`):
      `(a) zᵀ x = ‖A x‖₁`  and
      `‖A x‖₁ ≤ ‖z‖_∞ ≤ ‖A xₖ₊₁‖₁ ≤ ‖A‖₁`,
    where `z = Aᵀ sign(Ax)` and `xₖ₊₁ = ±e_j`.  This is the mathematics
    behind the LAPACK 1-norm estimator (Algorithm 15.3 = specialization).
    Non-vacuous: `lemma152b` at `pNormPair_one`. -/
theorem lemma152_one {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (hx : oneNormVec x = 1) :
    (∑ j : Fin n, (pNormPair_one hn A).zof x j * x j)
        = oneNormVec ((pNormPair_one hn A).yof x) ∧
    oneNormVec ((pNormPair_one hn A).yof x)
        ≤ infNormVec ((pNormPair_one hn A).zof x) ∧
    infNormVec ((pNormPair_one hn A).zof x)
        ≤ oneNormVec ((pNormPair_one hn A).yof ((pNormPair_one hn A).xnext x)) ∧
    oneNormVec ((pNormPair_one hn A).yof ((pNormPair_one hn A).xnext x))
        ≤ oneNorm A :=
  ⟨(pNormPair_one hn A).lemma152a x, (pNormPair_one hn A).lemma152b x hx⟩

/-- **1-norm estimate is a lower bound on `‖A‖₁`** (Higham §15.2, p. 291;
    cf. Algorithm 15.1's guarantee `γ ≤ ‖A‖_p`). -/
theorem gammaSeq_one_le_oneNorm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : oneNormVec x0 = 1) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 k ≤ oneNorm A :=
  (pNormPair_one hn A).gammaSeq_le_opP x0 hx0 k

/-- **1-norm estimates increase** (Higham §15.2, p. 291): `γₖ ≤ γₖ₊₁`. -/
theorem gammaSeq_one_mono {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (x0 : Fin n → ℝ) (hx0 : oneNormVec x0 = 1) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 k ≤ (pNormPair_one hn A).gammaSeq x0 (k + 1) :=
  (pNormPair_one hn A).gammaSeq_mono x0 hx0 k

end Ch15
end LeanFpAnalysis.FP
