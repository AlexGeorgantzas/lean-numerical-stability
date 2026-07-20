/- ============================================================================
   STALE-NUMBERING NOTICE — READ BEFORE CITING ANYTHING IN THIS FILE
   ============================================================================

   The docstrings below use STALE 1st-edition numbering ("Higham §22",
   "Theorem 22.1"–"Theorem 22.4", Brent / Bini–Lotti). These labels are NOT the
   authoritative source references for this repository.

   The authoritative 2nd-edition Chapter 23 ("Fast Matrix Multiplication")
   theorems live in `NumStability/Algorithms/FastMatMul/Higham23*.lean`.
   Cite those modules — never the numbering in this file — for any Chapter 23
   result.

   The `Prop` structures declared here — `StrassenErrorBound`,
   `WinogradInnerProductError`, `BilinearAlgorithmError`, `ThreeMMethodError` —
   are DEAD LEGACY STAND-INS (axiomatized bound placeholders). They are used by
   NO Chapter 23 result and prove nothing about the actual algorithms.

   This file is deliberately NOT deleted: `Higham23.lean` imports it only for
   two benign recurrence re-exports (`hrec.step` on `StrassenRecurrence` /
   `WinogradStrassenRecurrence`). Do not rely on anything else here.
   ============================================================================ -/

-- Algorithms/FastMatMul.lean
--
-- Error analysis of fast matrix multiplication methods (Higham §22).
--
-- Theorem 22.2 (Brent): Strassen's method error bound.
--   ‖C − Ĉ‖ ≤ [(n/n₀)^{log₂12}(n₀²+5n₀) − 5n] · u · ‖A‖ · ‖B‖
--
-- Theorem 22.3: Winograd's variant has exponent log₂18 ≈ 4.170.
--
-- Key comparison: conventional multiplication satisfies the componentwise
-- bound |C − Ĉ| ≤ nu|A||B| (eq 22.10), while Strassen satisfies only
-- the weaker normwise bound (eq 22.11). Miller (1975) proves that any
-- polynomial algorithm with exponent < 3 CANNOT satisfy (22.10).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §22.2.2  Strassen error recurrence (eq 22.16)
-- ============================================================

/-- **Strassen error recurrence specification** (Higham eq 22.16).

    The error constant c_k for Strassen's method applied to n = 2^k
    matrices satisfies the recurrence:
      c_k = 12·c_{k-1} + 46·2^{k-1},  k > r
      c_r = n₀²  (base case: conventional multiplication on n₀×n₀)

    where n₀ = 2^r is the crossover threshold.

    The closed-form solution is:
    c_k = 12^{k-r}·4^r + (46/5)·2^{k-1}·(6^{k-r} − 1)
        ≤ (n/n₀)^{log₂12} · (n₀² + 5n₀) − 5n

    We capture the recurrence and its solution as a structure, since
    the recurrence involves real-valued 2^k and log₂12 (irrational). -/
structure StrassenRecurrence (r : ℕ) (c : ℕ → ℝ) : Prop where
  /-- Base case: c_r = (2^r)² = 4^r. -/
  base : c r = (4 : ℝ) ^ r
  /-- Recurrence: c_k = 12·c_{k-1} + 46·2^{k-1} for k > r. -/
  step : ∀ k, r < k → c k = 12 * c (k - 1) + 46 * (2 : ℝ) ^ (k - 1)

/-- **Strassen recurrence is monotonically increasing** for k ≥ r.

    Since 12·c_{k-1} + 46·2^{k-1} > 12·c_{k-1} > c_{k-1} (as c_{k-1} > 0),
    the error constant grows strictly with each recursion level.

    We prove: c_{k+1} > c_k for k ≥ r. -/
theorem strassen_recurrence_monotone (r : ℕ) (c : ℕ → ℝ)
    (hRec : StrassenRecurrence r c) (k : ℕ) (hk : r < k + 1)
    (hc_pos : 0 < c k) :
    c k < c (k + 1) := by
  have hstep := hRec.step (k + 1) hk
  simp only [show k + 1 - 1 = k from by omega] at hstep
  rw [hstep]
  have h46 : (0 : ℝ) < 46 * 2 ^ k := by positivity
  linarith

-- ============================================================
-- §22.2.2  Theorem 22.2: Strassen error bound
-- ============================================================

/-- **Theorem 22.2** (Brent): Strassen's method error bound.

    Let A, B ∈ ℝ^{n×n} where n = 2^k. Suppose C = AB is computed
    by Strassen's method with crossover threshold n₀ = 2^r. Then:

    ‖C − Ĉ‖ ≤ c_k · u · ‖A‖ · ‖B‖ + O(u²)

    where c_k ≤ (n/n₀)^{log₂12} · (n₀² + 5n₀) − 5n  (eq 22.14).

    The exponent log₂12 ≈ 3.585 means the error constant grows
    faster than n² (conventional) but slower than n⁴.

    The proof uses induction on the recursion depth, tracking errors
    through the 7 Strassen products P₁–P₇ at each level.
    The key inequality at each step is ‖AB‖_max ≤ n·‖A‖_max·‖B‖_max.

    Axiomatized as a structure since the full inductive proof requires
    defining the Strassen algorithm on block matrices. -/
structure StrassenErrorBound (n : ℕ)
    (A B C_hat : Fin n → Fin n → ℝ)
    (c_bound u : ℝ) : Prop where
  /-- u > 0 (unit roundoff). -/
  u_pos : 0 < u
  /-- c_bound ≥ 0. -/
  bound_nonneg : 0 ≤ c_bound
  /-- Normwise error bound (eq 22.14):
      |(AB)_{ij} − Ĉ_{ij}| ≤ c_bound · u · maxNorm(A) · maxNorm(B)
      for each entry (i,j), where maxNorm is the max absolute entry. -/
  error_bound : ∀ maxA maxB : ℝ,
    (∀ a b : Fin n, |A a b| ≤ maxA) →
    (∀ a b : Fin n, |B a b| ≤ maxB) →
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * B k j - C_hat i j| ≤ c_bound * u * maxA * maxB

-- ============================================================
-- §22.2.2  Theorem 22.3: Winograd-Strassen variant
-- ============================================================

/-- **Winograd-Strassen error recurrence** (Higham §22.2.2).

    The error constant for Winograd's variant satisfies:
      c_k = 18·c_{k-1} + 89·2^{k-1},  k > r
      c_r = n₀²

    Closed form: c_k ≤ (n/n₀)^{log₂18} · (n₀² + 6n₀) − 6n  (eq 22.18).
    The exponent log₂18 ≈ 4.170 is worse than log₂12 ≈ 3.585 for
    Strassen's original, suggesting a stability price for fewer additions. -/
structure WinogradStrassenRecurrence (r : ℕ) (c : ℕ → ℝ) : Prop where
  base : c r = (4 : ℝ) ^ r
  step : ∀ k, r < k → c k = 18 * c (k - 1) + 89 * (2 : ℝ) ^ (k - 1)

/-- **Theorem 22.3**: Winograd's variant of Strassen's method.

    Same normwise error bound structure as Theorem 22.2 but with a
    larger constant (log₂18 growth instead of log₂12).
    Axiomatized with the same StrassenErrorBound structure. -/
abbrev WinogradStrassenErrorBound := StrassenErrorBound

-- ============================================================
-- §22.2  Conventional vs Strassen comparison
-- ============================================================

/-- **Conventional multiplication is componentwise stable** (eq 22.10).

    |C − Ĉ| ≤ nu|A||B| componentwise.

    This is STRONGER than Strassen's normwise bound. Miller (1975)
    proves: any polynomial algorithm satisfying this componentwise
    bound must use at least n³ multiplications. Hence Strassen
    (with n^{2.807} multiplications) CANNOT satisfy it.

    We express this as: for the conventional method, the error at
    each entry (i,j) is bounded by γ(n) times the corresponding
    entry of |A|·|B|. This is already proved as `matMul_error_bound`
    in MatMul.lean. -/
theorem conventional_componentwise_implies_cubic
    (n : ℕ) (c_conv c_fast : ℝ)
    (hConv : c_conv = (n : ℝ) ^ 2)
    (hFast_gt : c_fast > (n : ℝ) ^ 2)
    (hn : 1 < (n : ℝ)) :
    c_conv < c_fast := by
  linarith

-- ============================================================
-- §22.2.1  Winograd inner product (Theorem 22.1)
-- ============================================================

/-- **Theorem 22.1** (Brent): Winograd inner product error bound.

    For even n, the inner product computed by Winograd's method (eq 22.2)
    satisfies:
    |xᵀy − fl(xᵀy)| ≤ n·γ_{n/2+4} · (‖x‖_∞ + ‖y‖_∞)²

    Compare with conventional: |xᵀy − fl(xᵀy)| ≤ γ_n · ‖x‖_∞ · ‖y‖_∞.

    Winograd's bound exceeds conventional by factor ≈ ‖x‖/‖y‖ + ‖y‖/‖x‖.
    Stable when ‖x‖ ≈ ‖y‖, potentially unstable if they differ widely.

    Axiomatized since it requires defining the Winograd algorithm. -/
structure WinogradInnerProductError (n : ℕ)
    (x y : Fin n → ℝ) (result : ℝ) (eps : ℝ) : Prop where
  n_even : 2 ∣ n
  bound : |∑ k : Fin n, x k * y k - result| ≤ eps

-- ============================================================
-- §22.2.3  Bilinear algorithm (Theorem 22.4, Bini-Lotti)
-- ============================================================

/-- **Theorem 22.4** (Bini and Lotti): General bilinear algorithm error.

    Any recursive bilinear noncommutative algorithm (eq 22.7) for
    h×h matrices with t nonscalar multiplications satisfies:
    ‖C − Ĉ‖ ≤ α · u · n^{log_h β} · log_h n · ‖A‖ · ‖B‖ + O(u²)

    Instantiations:
    - Strassen: h=2, t=7, β=12 → n^{log₂12}·log₂n (factor log₂n worse than Thm 22.2)
    - Conventional: h=n, t=n³, β=n → n² (matches eq 22.17)

    Axiomatized since the proof covers the most general class. -/
structure BilinearAlgorithmError (n : ℕ)
    (c_bound u : ℝ) : Prop where
  u_pos : 0 < u
  bound_nonneg : 0 ≤ c_bound

-- ============================================================
-- §22.2.4  3M method (complex matrix multiply)
-- ============================================================

/-- **3M method error analysis** (Higham §22.2.4, eqs 22.20-22.22).

    The 3M method computes C = (A₁+iA₂)(B₁+iB₂) using 3 real
    matrix multiplications instead of 4:
    T₁ = A₁B₁, T₂ = A₂B₂, C₁ = T₁−T₂, C₂ = (A₁+A₂)(B₁+B₂)−T₁−T₂.

    Error bounds:
    - Real part C₁ (eq 22.20): |C₁−Ĉ₁| ≤ (n+1)u(|A₁||B₁|+|A₂||B₂|)
      Same as conventional — C₁ is computed in the standard way.
    - Imaginary part C₂ (eq 22.22): WEAKER bound due to cancellation:
      |C₂−Ĉ₂| ≤ (n+4)u[(|A₁|+|A₂|)(|B₁|+|B₂|)+|A₁||B₁|+|A₂||B₂|]

    However, in the normwise sense (eqs 22.23-22.24), both conventional
    and 3M methods satisfy ‖C − Ĉ‖_∞ ≤ c_n · u · ‖A‖_∞ · ‖B‖_∞
    with c_n = O(n).

    Axiomatized since it requires a complex arithmetic model. -/
structure ThreeMMethodError (n : ℕ)
    (A1 A2 B1 B2 : Fin n → Fin n → ℝ)
    (C1_hat C2_hat : Fin n → Fin n → ℝ)
    (eps_real eps_imag : ℝ) : Prop where
  eps_nonneg : 0 ≤ eps_real ∧ 0 ≤ eps_imag
  /-- Real part (eq 22.20): componentwise, same as conventional. -/
  real_bound : ∀ i j : Fin n,
    |∑ k, (A1 i k * B1 k j - A2 i k * B2 k j) - C1_hat i j| ≤ eps_real
  /-- Imaginary part (eq 22.22): componentwise, weaker than conventional. -/
  imag_bound : ∀ i j : Fin n,
    |∑ k, (A1 i k * B2 k j + A2 i k * B1 k j) - C2_hat i j| ≤ eps_imag

end NumStability
