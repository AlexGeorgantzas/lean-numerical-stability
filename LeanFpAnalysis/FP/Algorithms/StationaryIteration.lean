-- Algorithms/StationaryIteration.lean
--
-- Higham Chapter 17: Error analysis of stationary iterative methods.
--
-- Covers §17.2 (forward error analysis) and §17.3 (backward/residual error
-- analysis) for iterations of the form  Mx_{k+1} = Nx_k + b  where A = M − N.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §17.2  Splitting specification and iteration matrices
-- ============================================================

/-- A splitting A = M − N with M invertible. -/
structure SplittingSpec (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ) : Prop where
  splitting : ∀ i j, A i j = M i j - N i j
  inv_left : IsLeftInverse n M M_inv
  inv_right : IsRightInverse n M M_inv

/-- Iteration matrix G = M⁻¹N. -/
noncomputable def iterMatrix (n : ℕ) (M_inv N : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n M_inv N

/-- Dual iteration matrix H = NM⁻¹. -/
noncomputable def dualIterMatrix (n : ℕ) (N M_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ := matMul n N M_inv

-- ============================================================
-- AG = HA identity
-- ============================================================

/-- **AG = HA**: Since A = M − N, both sides equal N − NM⁻¹N. -/
theorem AG_eq_HA (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A (iterMatrix n M_inv N) =
    matMul n (dualIterMatrix n N M_inv) A := by
  ext i j
  show ∑ k : Fin n, A i k * (∑ l : Fin n, M_inv k l * N l j) =
       ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * A k j
  -- Expand A = M - N on both sides
  simp_rw [hS.splitting]
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  -- Show first terms both = N_{ij}
  have h1 : ∑ k : Fin n, M i k * ∑ l : Fin n, M_inv k l * N l j = N i j := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, M i x_1 * (M_inv x_1 x * N x j) =
        M i x_1 * M_inv x_1 x * N x j from fun _ _ => by ring]
    simp_rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext l; rw [hS.inv_right i l]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  have h2 : ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * M k j = N i j := by
    simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    simp_rw [show ∀ x x_1 : Fin n, N i x * M_inv x x_1 * M x_1 j =
        N i x * (M_inv x x_1 * M x_1 j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    conv_lhs => arg 2; ext l; rw [hS.inv_left l j]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  -- Show second terms match: ∑ N*(M⁻¹N) = ∑ (NM⁻¹)*N
  have h3 : ∑ k : Fin n, N i k * ∑ l : Fin n, M_inv k l * N l j =
      ∑ k : Fin n, (∑ l : Fin n, N i l * M_inv l k) * N k j := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    simp_rw [show ∀ k l : Fin n, N i k * (M_inv k l * N l j) =
        N i k * M_inv k l * N l j from fun _ _ => by ring]
    rw [Finset.sum_comm]
  linarith

/-- **AG^k = H^kA** for all k, by induction. -/
theorem A_matPow_G_eq_matPow_H_A (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) (k : ℕ) :
    matMul n A (matPow n (iterMatrix n M_inv N) k) =
    matMul n (matPow n (dualIterMatrix n N M_inv) k) A := by
  induction k with
  | zero =>
    simp only [matPow]; rw [matMul_id_right, matMul_id_left]
  | succ k ih =>
    show matMul n A (matMul n (iterMatrix n M_inv N)
      (matPow n (iterMatrix n M_inv N) k)) =
      matMul n (matMul n (dualIterMatrix n N M_inv)
      (matPow n (dualIterMatrix n N M_inv) k)) A
    rw [← matMul_assoc n A, AG_eq_HA n A M N M_inv hS,
        matMul_assoc n _ A, ih, ← matMul_assoc]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.4):
    an exact solution of `Ax = b` is a fixed point of the stationary
    affine map `x ↦ Gx + M⁻¹b`, where `G = M⁻¹N`. -/
theorem stationary_solution_fixed_point (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, x i =
      matMulVec n (iterMatrix n M_inv N) x i + matMulVec n M_inv b i := by
  have hMx : ∀ l, matMulVec n M x l = matMulVec n N x l + b l := by
    intro l
    unfold matMulVec
    have : ∑ j : Fin n, M l j * x j - ∑ j : Fin n, N l j * x j = b l := by
      rw [← Finset.sum_sub_distrib]
      convert hAx l using 1
      congr 1
      ext j
      rw [hS.splitting l j]
      ring
    linarith
  have hApplyLeft : matMulVec n M_inv (matMulVec n M x) = x := by
    ext i
    calc
      matMulVec n M_inv (matMulVec n M x) i
          = matMulVec n (matMul n M_inv M) x i := by
              rw [matMulVec_matMul]
      _ = matMulVec n (idMatrix n) x i := by
          unfold matMulVec matMul idMatrix
          apply Finset.sum_congr rfl
          intro j _hj
          exact congrArg (fun t : ℝ => t * x j) (hS.inv_left i j)
      _ = x i := by
          simp [matMulVec, idMatrix]
  intro i
  calc
    x i = matMulVec n M_inv (matMulVec n M x) i := by
      exact (congrFun hApplyLeft i).symm
    _ = matMulVec n M_inv (fun l => matMulVec n N x l + b l) i := by
      congr 1
      ext l
      exact hMx l
    _ = matMulVec n M_inv (matMulVec n N x) i +
        matMulVec n M_inv b i := by
      simpa using congrFun (matMulVec_add_right n M_inv (matMulVec n N x) b) i
    _ = matMulVec n (iterMatrix n M_inv N) x i + matMulVec n M_inv b i := by
      simp [iterMatrix, matMulVec_matMul]

/-- Finite unrolling of an affine fixed point `x = Gx + c`. -/
theorem affine_fixed_point_unroll (n : ℕ)
    (G : Fin n → Fin n → ℝ) (c x : Fin n → ℝ)
    (hfix : ∀ i, x i = matMulVec n G x i + c i) :
    ∀ m i, x i =
      matMulVec n (matPow n G m) x i +
      ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [matPow, matMulVec, idMatrix]
  | succ m ih =>
      intro i
      have htail :
          matMulVec n (matPow n G m) x i =
            matMulVec n (matPow n G (m + 1)) x i +
              matMulVec n (matPow n G m) c i := by
        have hx :
            x = fun j => matMulVec n G x j + c j := by
          ext j
          exact hfix j
        calc
          matMulVec n (matPow n G m) x i
              = matMulVec n (matPow n G m)
                  (fun j => matMulVec n G x j + c j) i := by
                  exact congrArg (fun y => matMulVec n (matPow n G m) y i) hx
          _ = matMulVec n (matPow n G m) (matMulVec n G x) i +
                matMulVec n (matPow n G m) c i := by
                  simpa using
                    congrFun
                      (matMulVec_add_right n (matPow n G m)
                        (matMulVec n G x) c) i
          _ = matMulVec n (matPow n G (m + 1)) x i +
                matMulVec n (matPow n G m) c i := by
                  congr 1
                  rw [← matMulVec_matMul n (matPow n G m) G x i]
                  rw [← matPow_succ_right n G m]
      calc
        x i = matMulVec n (matPow n G m) x i +
            ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := ih i
        _ = (matMulVec n (matPow n G (m + 1)) x i +
              matMulVec n (matPow n G m) c i) +
            ∑ k ∈ Finset.range m, matMulVec n (matPow n G k) c i := by
              rw [htail]
        _ = matMulVec n (matPow n G (m + 1)) x i +
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G k) c i := by
              rw [Finset.sum_range_succ]
              ring

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.4):
    finite-sum identity for an exact stationary solution, obtained by
    unrolling the affine fixed-point equation. -/
theorem stationary_solution_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (m : ℕ) :
    ∀ i, x i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) x i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv b) i := by
  intro i
  exact affine_fixed_point_unroll n (iterMatrix n M_inv N)
    (matMulVec n M_inv b) x
    (stationary_solution_fixed_point n A M N M_inv hS b x hAx)
    (m + 1) i

/-- Matrix-vector multiplication distributes over a finite sum in the vector
    argument. -/
theorem matMulVec_finset_sum_right {α : Type*} [DecidableEq α] (n : ℕ)
    (A : Fin n → Fin n → ℝ) (s : Finset α) (v : α → Fin n → ℝ) :
    matMulVec n A (fun i => ∑ a ∈ s, v a i) =
      fun i => ∑ a ∈ s, matMulVec n A (v a) i := by
  classical
  induction s using Finset.induction with
  | empty =>
      ext i
      simp [matMulVec]
  | insert a s ha ih =>
      ext i
      simp [ha, matMulVec_add_right, ih]

/-- Finite unrolling of an affine recurrence with a time-varying source term. -/
theorem affine_recurrence_unroll (n : ℕ)
    (G : Fin n → Fin n → ℝ) (d : ℕ → Fin n → ℝ)
    (y : ℕ → Fin n → ℝ)
    (hstep : ∀ k i, y (k + 1) i = matMulVec n G (y k) i + d k i) :
    ∀ m i, y (m + 1) i =
      matMulVec n (matPow n G (m + 1)) (y 0) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n G k) (d (m - k)) i := by
  intro m
  induction m with
  | zero =>
      intro i
      rw [Finset.sum_range_one, matPow_one]
      simpa [matPow_zero, matMulVec, idMatrix] using hstep 0 i
  | succ m ih =>
      intro i
      have hy :
          y (m + 1) =
            fun j => matMulVec n (matPow n G (m + 1)) (y 0) j +
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j := by
        ext j
        exact ih j
      have hlead :
          matMulVec n G
              (matMulVec n (matPow n G (m + 1)) (y 0)) i =
            matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i := by
        rw [← matMulVec_matMul n G (matPow n G (m + 1)) (y 0) i]
        rw [← matPow_succ n G (m + 1)]
      have hsum :
          matMulVec n G
              (fun j => ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j) i =
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
        calc
          matMulVec n G
              (fun j => ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G k) (d (m - k)) j) i
              = ∑ k ∈ Finset.range (m + 1),
                  matMulVec n G
                    (matMulVec n (matPow n G k) (d (m - k))) i := by
                  simpa using
                    congrFun
                      (matMulVec_finset_sum_right n G (Finset.range (m + 1))
                        (fun k => matMulVec n (matPow n G k) (d (m - k)))) i
          _ = ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [← matMulVec_matMul n G (matPow n G k) (d (m - k)) i]
              rw [← matPow_succ n G k]
      have hfull :
          (∑ k ∈ Finset.range ((m + 1) + 1),
            matMulVec n (matPow n G k) (d ((m + 1) - k)) i) =
            d (m + 1) i +
            ∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
        have hzero :
            matMulVec n (matPow n G 0) (d ((m + 1) - 0)) i =
              d (m + 1) i := by
          simp [matPow_zero, matMulVec, idMatrix]
        have htail :
            (∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G (k + 1))
                (d ((m + 1) - (k + 1))) i) =
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [Nat.succ_sub_succ_eq_sub]
        rw [Finset.sum_range_succ']
        rw [hzero, htail]
        ring
      calc
        y ((m + 1) + 1) i =
            matMulVec n G (y (m + 1)) i + d (m + 1) i := hstep (m + 1) i
        _ = matMulVec n G
              (fun j => matMulVec n (matPow n G (m + 1)) (y 0) j +
                ∑ k ∈ Finset.range (m + 1),
                  matMulVec n (matPow n G k) (d (m - k)) j) i +
            d (m + 1) i := by
              rw [hy]
        _ = (matMulVec n G
                (matMulVec n (matPow n G (m + 1)) (y 0)) i +
              matMulVec n G
                (fun j => ∑ k ∈ Finset.range (m + 1),
                  matMulVec n (matPow n G k) (d (m - k)) j) i) +
            d (m + 1) i := by
              rw [congrFun
                (matMulVec_add_right n G
                  (matMulVec n (matPow n G (m + 1)) (y 0))
                  (fun j => ∑ k ∈ Finset.range (m + 1),
                    matMulVec n (matPow n G k) (d (m - k)) j)) i]
        _ = (matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i +
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n G (k + 1)) (d (m - k)) i) +
            d (m + 1) i := by
              rw [hlead, hsum]
        _ = matMulVec n (matPow n G ((m + 1) + 1)) (y 0) i +
            ∑ k ∈ Finset.range ((m + 1) + 1),
              matMulVec n (matPow n G k) (d ((m + 1) - k)) i := by
              rw [hfull]
              ring

-- ============================================================
-- §17.2  Computed iteration and one-step error
-- ============================================================

/-- Computed stationary iteration with local errors, using the repository's
    legacy sign convention `M xhat_{k+1} = N xhat_k + b + xi_k`. -/
structure ComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
         ∑ j : Fin n, N i j * x_hat k j + b i + ξ k i

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    source-sign form of the computed stationary iteration,
    `M xhat_{k+1} = N xhat_k + b - xi_k`. -/
structure SourceComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
         ∑ j : Fin n, N i j * x_hat k j + b i - ξ k i

/-- The source-sign convention in Higham's equation (17.1) is the legacy
    `ComputedIteration` convention with the local error term negated. -/
theorem computedIteration_of_sourceComputedIteration (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ComputedIteration n M N b x_hat (fun k i => -ξ k i) := by
  constructor
  intro k i
  simpa [sub_eq_add_neg] using hIter.step k i

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    applying `M⁻¹` to the source-sign computed iteration gives the affine
    step `xhat_{k+1} = G xhat_k + M⁻¹(b - xi_k)`. -/
theorem sourceComputedIteration_step_affine (n : ℕ)
    (M N M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat ξ : ℕ → Fin n → ℝ)
    (hLeft : IsLeftInverse n M M_inv)
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ∀ k i, x_hat (k + 1) i =
      matMulVec n (iterMatrix n M_inv N) (x_hat k) i +
      matMulVec n M_inv (fun j => b j - ξ k j) i := by
  intro k i
  have hApplyLeft :
      matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) =
        x_hat (k + 1) := by
    ext r
    calc
      matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) r
          = matMulVec n (matMul n M_inv M) (x_hat (k + 1)) r := by
              rw [matMulVec_matMul]
      _ = matMulVec n (idMatrix n) (x_hat (k + 1)) r := by
          unfold matMulVec matMul idMatrix
          apply Finset.sum_congr rfl
          intro j _hj
          exact congrArg (fun t : ℝ => t * x_hat (k + 1) j) (hLeft r j)
      _ = x_hat (k + 1) r := by
          simp [matMulVec, idMatrix]
  calc
    x_hat (k + 1) i =
        matMulVec n M_inv (matMulVec n M (x_hat (k + 1))) i := by
          exact (congrFun hApplyLeft i).symm
    _ = matMulVec n M_inv
          (fun l => matMulVec n N (x_hat k) l + (b l - ξ k l)) i := by
          congr 1
          ext l
          have h := hIter.step k l
          dsimp [matMulVec] at h ⊢
          linarith
    _ = matMulVec n M_inv (matMulVec n N (x_hat k)) i +
        matMulVec n M_inv (fun l => b l - ξ k l) i := by
          simpa using
            congrFun
              (matMulVec_add_right n M_inv (matMulVec n N (x_hat k))
                (fun l => b l - ξ k l)) i
    _ = matMulVec n (iterMatrix n M_inv N) (x_hat k) i +
        matMulVec n M_inv (fun l => b l - ξ k l) i := by
          simp [iterMatrix, matMulVec_matMul]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.3):
    finite-sum closed form for the source-sign computed stationary iteration. -/
theorem sourceComputedIteration_finite_sum (n : ℕ)
    (M N M_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat ξ : ℕ → Fin n → ℝ)
    (hLeft : IsLeftInverse n M M_inv)
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1)) (x_hat 0) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv (fun j => b j - ξ (m - k) j)) i := by
  intro i
  exact affine_recurrence_unroll n (iterMatrix n M_inv N)
    (fun k => matMulVec n M_inv (fun j => b j - ξ k j))
    x_hat
    (sourceComputedIteration_step_affine n M N M_inv b x_hat ξ hLeft hIter)
    m i

/-- One-step error: x_i − x̂_{k+1,i} = ∑_j G_{ij}(x_j − x̂_{k,j}) − ∑_j M⁻¹_{ij} ξ_{k,j}. -/
theorem one_step_error (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, x i - x_hat (k + 1) i =
      ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) -
      ∑ j : Fin n, M_inv i j * ξ k j := by
  intro k i
  have hstep := hIter.step k
  -- Mx = Nx + b
  have hMx : ∀ l, ∑ j : Fin n, M l j * x j =
      ∑ j : Fin n, N l j * x j + b l := by
    intro l
    have : ∑ j : Fin n, M l j * x j - ∑ j : Fin n, N l j * x j = b l := by
      rw [← Finset.sum_sub_distrib]
      convert hAx l using 1; congr 1; ext j; rw [hS.splitting l j]; ring
    linarith
  -- M(x - x̂_{k+1})_l = N(x - x̂_k)_l - ξ_{k,l}
  have hMdiff : ∀ l, ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
      ∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l := by
    intro l
    have h1 : ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) =
        ∑ j, M l j * x j - ∑ j, M l j * x_hat (k + 1) j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    have h2 : ∑ j : Fin n, N l j * (x j - x_hat k j) =
        ∑ j, N l j * x j - ∑ j, N l j * x_hat k j := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    rw [h1, h2]; linarith [hstep l, hMx l]
  -- Apply M⁻¹
  have h_start : x i - x_hat (k + 1) i =
      ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j) := by
    symm
    calc ∑ l : Fin n, M_inv i l * ∑ j : Fin n, M l j * (x j - x_hat (k + 1) j)
        = ∑ j : Fin n, (∑ l : Fin n, M_inv i l * M l j) *
            (x j - x_hat (k + 1) j) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          congr 1; ext j; congr 1; ext l; ring
      _ = ∑ j : Fin n, (if i = j then 1 else 0) * (x j - x_hat (k + 1) j) := by
          congr 1; ext j; congr 1; exact hS.inv_left i j
      _ = x i - x_hat (k + 1) i := by
          simp [Finset.sum_ite_eq, Finset.mem_univ]
  rw [h_start]
  -- Replace M·diff with N·diff - ξ
  conv_lhs => arg 2; ext l; rw [hMdiff l]
  -- LHS: ∑_l M⁻¹_{il} * (∑_j N_{lj} (x_j - x̂_{k,j}) - ξ_{k,l})
  -- RHS: ∑_j G_{ij}(x_j-x̂_{k,j}) - ∑_j M⁻¹_{ij}ξ_{k,j}
  -- Both sides equal ∑_l ∑_j M⁻¹_{il}N_{lj}d_j - ∑_l M⁻¹_{il}ξ_l
  -- Transform LHS
  simp_rw [show ∀ l : Fin n, M_inv i l *
      (∑ j : Fin n, N l j * (x j - x_hat k j) - ξ k l) =
      ∑ j : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) -
      M_inv i l * ξ k l from fun l => by rw [mul_sub, Finset.mul_sum]]
  rw [Finset.sum_sub_distrib]
  congr 1
  -- ∑_l ∑_j M⁻¹_{il}*(N_{lj}*d_j) = ∑_j G_{ij}*d_j
  rw [Finset.sum_comm]
  congr 1; ext j
  simp_rw [show ∀ l : Fin n, M_inv i l * (N l j * (x j - x_hat k j)) =
      M_inv i l * N l j * (x j - x_hat k j) from fun l => by ring]
  rw [← Finset.sum_mul]; rfl

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.1):
    one-step error recurrence for the source-sign local error convention. -/
theorem one_step_error_source (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ) :
    ∀ k i, x i - x_hat (k + 1) i =
      ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) +
      ∑ j : Fin n, M_inv i j * ξ k j := by
  intro k i
  have hOld := one_step_error n A M N M_inv hS b x hAx x_hat
    (fun k i => -ξ k i)
    (computedIteration_of_sourceComputedIteration n M N b x_hat ξ hIter) k i
  calc
    x i - x_hat (k + 1) i =
        ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) -
        ∑ j : Fin n, M_inv i j * (-ξ k j) := hOld
    _ = ∑ j : Fin n, (iterMatrix n M_inv N) i j * (x j - x_hat k j) +
        ∑ j : Fin n, M_inv i j * ξ k j := by
        rw [sub_eq_add_neg]
        congr 1
        simp_rw [mul_neg]
        rw [Finset.sum_neg_distrib, neg_neg]

/-- Higham, 2nd ed., Chapter 17, Section 17.2, equation (17.5):
    finite-sum forward-error recurrence for the source-sign computed
    stationary iteration. -/
theorem sourceComputedIteration_error_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (iterMatrix n M_inv N) k)
          (matMulVec n M_inv (ξ (m - k))) i := by
  intro i
  exact affine_recurrence_unroll n (iterMatrix n M_inv N)
    (fun k => matMulVec n M_inv (ξ k))
    (fun k j => x j - x_hat k j)
    (by
      intro k j
      simpa [matMulVec] using
        one_step_error_source n A M N M_inv hS b x hAx x_hat ξ hIter k j)
    m i

-- ============================================================
-- §17.2  Componentwise forward bound (eq 17.6)
-- ============================================================

/-- **Eq. 17.6 (Componentwise forward bound)**: triangle inequality bound on
    |∑_j G^{m+1}_{ij} e_{0,j} + ∑_{k=0}^m ∑_j G^k_{ij} w_{m-k,j}|. -/
theorem componentwise_forward_bound (n : ℕ)
    (G : Fin n → Fin n → ℝ) (e₀ : Fin n → ℝ) (m : ℕ)
    (w : ℕ → (Fin n → ℝ)) (μ : ℕ → (Fin n → ℝ))
    (hw : ∀ k i, |w k i| ≤ μ k i)
    (_hμ : ∀ k i, 0 ≤ μ k i) :
    ∀ i, |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, matPow n G k i j * w (m - k) j| ≤
      ∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j| +
      ∑ k ∈ Finset.range (m + 1),
        ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
  intro i
  calc |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j|
      ≤ |∑ j : Fin n, matPow n G (m + 1) i j * e₀ j| +
        |∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, matPow n G k i j * w (m - k) j| := abs_add_le _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j * e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          |∑ j : Fin n, matPow n G k i j * w (m - k) j| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ (Finset.univ : Finset (Fin n)))
          (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j * w (m - k) j| := by
        gcongr with j _
        · exact le_of_eq (abs_mul _ _)
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ j : Fin n, |matPow n G (m + 1) i j| * |e₀ j|) +
        ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, |matPow n G k i j| * μ (m - k) j := by
        gcongr with k _ j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hw _ _) (abs_nonneg _)

-- ============================================================
-- §17.2  Local error bound and simplification (eqs 17.2, 17.10)
-- ============================================================

/-- Eq. 17.2: local rounding error bound. -/
def LocalErrorBound (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ))
    (ξ : ℕ → (Fin n → ℝ)) (cn_u : ℝ) : Prop :=
  ∀ k i, |ξ k i| ≤ cn_u * (∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
                              ∑ j : Fin n, |N i j| * |x_hat k j| + |b i|)

/-- **Eq. 17.10**: |ξ_k,i| ≤ c_n u(1+θ_x) ∑_j (|M_{ij}|+|N_{ij}|)|x_j|. -/
theorem local_error_simplified (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (_hθ : 0 ≤ θ_x)
    (hx_bound : ∀ k i, |x_hat k i| ≤ θ_x * |x i|)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u) :
    ∀ k i, |ξ k i| ≤ cn_u * (1 + θ_x) *
      ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
  intro k i
  have hL := hLocal k i
  have hb : |b i| ≤ ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    calc |b i| = |∑ j, (M i j - N i j) * x j| := by rw [hAx]
      _ ≤ ∑ j, |(M i j - N i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |M i j - N i j| * |x j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (|M i j| + |N i j|) * |x j| := by
          gcongr with j _
          calc |M i j - N i j| = |M i j + (-(N i j))| := by ring_nf
            _ ≤ |M i j| + |-(N i j)| := abs_add_le _ _
            _ = |M i j| + |N i j| := by rw [abs_neg]
  have hM_bound : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| ≤
      θ_x * ∑ j : Fin n, |M i j| * |x j| :=
    calc ∑ j, |M i j| * |x_hat (k + 1) j|
        ≤ ∑ j, |M i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |M i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hN_bound : ∑ j : Fin n, |N i j| * |x_hat k j| ≤
      θ_x * ∑ j : Fin n, |N i j| * |x j| :=
    calc ∑ j, |N i j| * |x_hat k j|
        ≤ ∑ j, |N i j| * (θ_x * |x j|) := by
          gcongr with j _; exact hx_bound _ _
      _ = θ_x * ∑ j, |N i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  have hSum : ∑ j : Fin n, |M i j| * |x_hat (k + 1) j| +
      ∑ j : Fin n, |N i j| * |x_hat k j| + |b i| ≤
      (1 + θ_x) * ∑ j : Fin n, (|M i j| + |N i j|) * |x j| := by
    have split_sum : ∑ j : Fin n, (|M i j| + |N i j|) * |x j| =
        ∑ j : Fin n, |M i j| * |x j| + ∑ j : Fin n, |N i j| * |x j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    rw [split_sum]; nlinarith
  calc |ξ k i|
      ≤ cn_u * (∑ j, |M i j| * |x_hat (k + 1) j| +
                ∑ j, |N i j| * |x_hat k j| + |b i|) := hL
    _ ≤ cn_u * ((1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j|) := by
        apply mul_le_mul_of_nonneg_left hSum hcn
    _ = cn_u * (1 + θ_x) * ∑ j, (|M i j| + |N i j|) * |x j| := by ring

-- ============================================================
-- §17.2  c(A) constant and main bound (eqs 17.12–17.13)
-- ============================================================

/-- Partial sum bound (eq 17.12): ∑_{k=0}^m |G^k M⁻¹|_{ij} ≤ cA · |A⁻¹_{ij}|. -/
def PartialSumBound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (cA : ℝ) (m : ℕ) : Prop :=
  ∀ i j, ∑ k ∈ Finset.range (m + 1),
    ∑ l : Fin n, |matPow n G k i l| * |M_inv l j| ≤ cA * |A_inv i j|

-- ============================================================
-- §17.2.1  Jacobi specialization
-- ============================================================

/-- **Eq. 17.16 (Jacobi)**: |M| + |N| = |A| for M = diag(A), N = diag(A) − A. -/
theorem jacobi_splitting_abs (n : ℕ) (A : Fin n → Fin n → ℝ)
    (M N : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j) :
    ∀ i j, |M i j| + |N i j| = |A i j| := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hM i i, if_pos rfl, hN i i, hM i i, if_pos rfl, sub_self, abs_zero, add_zero]
  · rw [hM i j, if_neg hij, hN i j, hM i j, if_neg hij, zero_sub, abs_zero, zero_add, abs_neg]

-- ============================================================
-- §17.2.2  SOR specialization
-- ============================================================

/-- **Eq. 17.17 (SOR)**: |M| + |N| ≤ f(ω)|A| where f(ω) = (1+|1−ω|)/ω. -/
theorem sor_splitting_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (ω : ℝ) (hω_pos : 0 < ω)
    (D L U : Fin n → Fin n → ℝ)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (M_sor N_sor : Fin n → Fin n → ℝ)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j)) :
    ∀ i j, |M_sor i j| + |N_sor i j| ≤ ((1 + |1 - ω|) / ω) * |A i j| := by
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  have hfω : 1 ≤ (1 + |1 - ω|) / ω := by
    rw [le_div_iff₀ hω_pos]
    by_cases h : ω ≤ 1
    · have : |1 - ω| = 1 - ω := abs_of_nonneg (by linarith)
      nlinarith
    · push_neg at h
      have h1 : (1 : ℝ) - ω < 0 := by linarith
      have : |1 - ω| = -(1 - ω) := abs_of_neg h1
      linarith
  intro i j
  by_cases hij : i = j
  · -- Diagonal case: L_{ii} = U_{ii} = 0
    have hLii := hL i i (le_refl _)
    have hUii := hU i i (le_refl _)
    have hAii : A i i = D i i := by
      have := hDecomp i i; rw [hLii, hUii] at this; linarith
    subst hij
    have hMval : M_sor i i = D i i / ω := by
      rw [hM, hLii, mul_zero, add_zero]; field_simp
    have hNval : N_sor i i = (1 - ω) * D i i / ω := by
      rw [hN, hUii, mul_zero, sub_zero]; field_simp
    rw [hMval, hNval, ← hAii]
    rw [abs_div, abs_div, abs_mul, ← add_div, abs_of_pos hω_pos, div_mul_eq_mul_div]
    ring_nf; rfl
  · -- Off-diagonal: D_{ij} = 0
    have hDij := hD i j hij
    have hMval : M_sor i j = L i j := by
      rw [hM, hDij, zero_add]; field_simp
    have hNval : N_sor i j = -(U i j) := by
      rw [hN, hDij, mul_zero, zero_sub]; field_simp
    rw [hMval, hNval, abs_neg]
    have hAij : A i j = L i j + U i j := by
      have := hDecomp i j; rw [hDij] at this; linarith
    by_cases hlj : j.val < i.val
    · have hUij := hU i j (le_of_lt hlj)
      rw [hUij, abs_zero, add_zero, hAij, hUij, add_zero]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω
    · push_neg at hlj
      have hji : i.val < j.val := by
        rcases hlj.eq_or_lt with heq | hlt
        · exact absurd (Fin.ext heq.symm) (Ne.symm hij)
        · exact hlt
      have hLij := hL i j (le_of_lt hji)
      rw [hLij, abs_zero, zero_add, hAij, hLij, zero_add]
      exact le_mul_of_one_le_left (abs_nonneg _) hfω

-- ============================================================
-- §17.3  Backward error — residual identity and sigma bound
-- ============================================================

/-- The residual r_k = b − Ax̂_k equals A(x − x̂_k). -/
theorem residual_eq_A_error (n : ℕ) (A : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : Fin n → ℝ) :
    ∀ i, b i - ∑ j : Fin n, A i j * x_hat j =
      ∑ j : Fin n, A i j * (x j - x_hat j) := by
  intro i
  rw [← hAx i, ← Finset.sum_sub_distrib]
  congr 1; ext j; ring

/-- Geometric series partial sum bound: ∑_{k=0}^m q^k ≤ 1/(1-q) for 0 ≤ q < 1. -/
private theorem geom_partial_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), q ^ k ≤ 1 / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  rw [le_div_iff₀ hq1']
  calc (∑ k ∈ Finset.range (m + 1), q ^ k) * (1 - q)
      = ∑ k ∈ Finset.range (m + 1), (q ^ k - q ^ (k + 1)) := by
        rw [Finset.sum_mul]; congr 1; ext k; ring
    _ = 1 - q ^ (m + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ]; linarith
    _ ≤ 1 := by linarith [pow_nonneg hq (m + 1)]

/-- **σ bound** (§17.3): ∑_{k=0}^m ‖H^k(I−H)‖∞ ≤ ‖I−H‖∞/(1−q) when ‖H‖∞ ≤ q < 1. -/
theorem sigma_bound (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm H ≤ q) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      infNorm (matMul n (matPow n H k) (matSub_id n H)) ≤
    infNorm (matSub_id n H) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  calc ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n H k) (matSub_id n H))
      ≤ ∑ k ∈ Finset.range (m + 1),
        (q ^ k * infNorm (matSub_id n H)) := by
        gcongr with k _
        calc infNorm (matMul n (matPow n H k) (matSub_id n H))
            ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
              infNorm_matMul_le hn _ _
          _ ≤ q ^ k * infNorm (matSub_id n H) := by
              apply mul_le_mul_of_nonneg_right _ (infNorm_nonneg _)
              exact (infNorm_matPow_le hn H k).trans (pow_le_pow_left₀ (infNorm_nonneg H) hH k)
    _ = (∑ k ∈ Finset.range (m + 1), q ^ k) * infNorm (matSub_id n H) := by
        rw [Finset.sum_mul]
    _ ≤ (1 / (1 - q)) * infNorm (matSub_id n H) := by
        apply mul_le_mul_of_nonneg_right (geom_partial_sum_le q hq hq1 m) (infNorm_nonneg _)
    _ = infNorm (matSub_id n H) / (1 - q) := by
        rw [one_div, mul_comm, div_eq_mul_inv]

-- ============================================================
-- §17.3  Residual recurrence: r_{k+1} = Hr_k − (I−H)ξ_k
-- ============================================================

/-- AM⁻¹ = I − H: since A = M − N, AM⁻¹ = MM⁻¹ − NM⁻¹ = I − H. -/
theorem A_matMul_Minv_eq_sub (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv) :
    matMul n A M_inv = matSub_id n (dualIterMatrix n N M_inv) := by
  ext i j
  show ∑ k, A i k * M_inv k j = idMatrix n i j - ∑ k, N i k * M_inv k j
  simp_rw [hS.splitting, sub_mul, Finset.sum_sub_distrib]
  have hMM := hS.inv_right i j; unfold idMatrix at *; linarith

/-- **One-step residual recurrence** (eq 17.18 base case): r_{k+1} = Hr_k − (I−H)ξ_k.
    Obtained by left-multiplying e_{k+1} = Ge_k − M⁻¹ξ_k by A
    and using AG = HA, AM⁻¹ = I − H. -/
theorem one_step_residual (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) :
    ∀ k i, (b i - ∑ j, A i j * x_hat (k + 1) j) =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i -
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i := by
  intro k i
  -- r_{k+1,i} = ∑_j A_{ij}(x_j − x̂_{k+1,j})
  rw [residual_eq_A_error n A b x hAx (x_hat (k + 1)) i]
  -- Substitute one_step_error
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  conv_lhs => arg 2; ext j; rw [hstep j, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- A·(G·e_k) = H·r_k  via  A(Gd) = (AG)d = (HA)d = H(Ad) = H·r_k
    show matMulVec n A (matMulVec n (iterMatrix n M_inv N)
        (fun l => x l - x_hat k l)) i =
      matMulVec n (dualIterMatrix n N M_inv)
        (fun j => b j - ∑ l, A j l * x_hat k l) i
    rw [← matMulVec_matMul, AG_eq_HA n A M N M_inv hS, matMulVec_matMul]
    suffices h : matMulVec n A (fun l => x l - x_hat k l) =
        fun j => b j - ∑ l, A j l * x_hat k l by rw [h]
    ext j; exact (residual_eq_A_error n A b x hAx (x_hat k) j).symm
  · -- A·(M⁻¹·ξ_k) = (I−H)·ξ_k  via  AM⁻¹ = I − H
    show matMulVec n A (matMulVec n M_inv (ξ k)) i =
      matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
    rw [← matMulVec_matMul, A_matMul_Minv_eq_sub n A M N M_inv hS]

/-- Higham, 2nd ed., Chapter 17, Section 17.3, equation (17.18):
    finite-sum residual recurrence
    `r_{m+1} = H^(m+1) r_0 - sum_{k=0}^m H^k (I-H) ξ_{m-k}`. -/
theorem residual_finite_sum (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    ∀ i, b i - ∑ j : Fin n, A i j * x_hat (m + 1) j =
      matMulVec n (matPow n (dualIterMatrix n N M_inv) (m + 1))
        (fun j => b j - ∑ l : Fin n, A j l * x_hat 0 l) i -
      ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n (dualIterMatrix n N M_inv) k)
          (matMulVec n (matSub_id n (dualIterMatrix n N M_inv))
            (ξ (m - k))) i := by
  intro i
  let H := dualIterMatrix n N M_inv
  let C := matSub_id n H
  let R : ℕ → Fin n → ℝ :=
    fun k j => b j - ∑ l : Fin n, A j l * x_hat k l
  have hsource :
      (∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n H k)
          (fun j => -matMulVec n C (ξ (m - k)) j) i) =
      - ∑ k ∈ Finset.range (m + 1),
        matMulVec n (matPow n H k)
          (matMulVec n C (ξ (m - k))) i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    unfold matMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hunroll := affine_recurrence_unroll n H
    (fun k j => -matMulVec n C (ξ k) j)
    R
    (by
      intro k j
      have hres := one_step_residual n A M N M_inv hS b x hAx x_hat ξ hIter k j
      simpa [R, H, C, sub_eq_add_neg] using hres)
    m i
  rw [hsource] at hunroll
  simpa [R, H, C, sub_eq_add_neg] using hunroll

/-- Finite sigma-form residual bound following from the closed residual
    recurrence: the propagated initial residual plus the finite sum of
    `||H^k(I-H)||∞ * ||ξ_{m-k}||∞` controls `||r_{m+1}||∞`. -/
theorem normwise_residual_sigma_finite_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (m : ℕ) :
    infNormVec (fun i => b i - ∑ j : Fin n, A i j * x_hat (m + 1) j) ≤
      infNorm (matPow n (dualIterMatrix n N M_inv) (m + 1)) *
        infNormVec (fun i => b i - ∑ j : Fin n, A i j * x_hat 0 j) +
      ∑ k ∈ Finset.range (m + 1),
        infNorm (matMul n (matPow n (dualIterMatrix n N M_inv) k)
          (matSub_id n (dualIterMatrix n N M_inv))) *
        infNormVec (ξ (m - k)) := by
  let H := dualIterMatrix n N M_inv
  let C := matSub_id n H
  let r0 : Fin n → ℝ :=
    fun i => b i - ∑ j : Fin n, A i j * x_hat 0 j
  apply infNormVec_le_of_abs_le
  · intro i
    have hres := residual_finite_sum n A M N M_inv hS b x hAx x_hat ξ hIter m i
    have hlead :
        |matMulVec n (matPow n H (m + 1)) r0 i| ≤
          infNorm (matPow n H (m + 1)) * infNormVec r0 := by
      exact (abs_le_infNormVec (matMulVec n (matPow n H (m + 1)) r0) i).trans
        (infNormVec_matMulVec_le hn (matPow n H (m + 1)) r0)
    have hsum :
        |∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| ≤
        ∑ k ∈ Finset.range (m + 1),
          infNorm (matMul n (matPow n H k) C) * infNormVec (ξ (m - k)) := by
      calc
        |∑ k ∈ Finset.range (m + 1),
          matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i|
            ≤ ∑ k ∈ Finset.range (m + 1),
                |matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (m + 1),
              infNorm (matMul n (matPow n H k) C) * infNormVec (ξ (m - k)) := by
            apply Finset.sum_le_sum
            intro k _hk
            calc
              |matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i|
                  = |matMulVec n (matMul n (matPow n H k) C)
                      (ξ (m - k)) i| := by
                    rw [matMulVec_matMul n (matPow n H k) C (ξ (m - k)) i]
              _ ≤ infNormVec
                    (matMulVec n (matMul n (matPow n H k) C) (ξ (m - k))) :=
                  abs_le_infNormVec _ i
              _ ≤ infNorm (matMul n (matPow n H k) C) *
                    infNormVec (ξ (m - k)) :=
                  infNormVec_matMulVec_le hn _ _
    calc
      |b i - ∑ j : Fin n, A i j * x_hat (m + 1) j|
          = |matMulVec n (matPow n H (m + 1)) r0 i -
              ∑ k ∈ Finset.range (m + 1),
                matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| := by
              rw [hres]
      _ ≤ |matMulVec n (matPow n H (m + 1)) r0 i| +
            |∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n H k) (matMulVec n C (ξ (m - k))) i| :=
          (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ infNorm (matPow n H (m + 1)) * infNormVec r0 +
            ∑ k ∈ Finset.range (m + 1),
              infNorm (matMul n (matPow n H k) C) *
                infNormVec (ξ (m - k)) :=
          add_le_add hlead hsum
  · exact add_nonneg
      (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
      (Finset.sum_nonneg (fun k _hk =>
        mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _)))

-- ============================================================
-- §17.2  Normwise one-step bound and forward bound (eqs 17.5, 17.8)
-- ============================================================

/-- Normwise one-step error bound from `one_step_error`:
    ‖e_{k+1}‖∞ ≤ ‖G‖∞·‖e_k‖∞ + ‖M⁻¹‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_bound (n : ℕ) (_hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec (fun i => x i - x_hat (k + 1) i) ≤
      infNorm (iterMatrix n M_inv N) *
        infNormVec (fun i => x i - x_hat k i) +
      infNorm M_inv * infNormVec (ξ k) := by
  have hstep := one_step_error n A M N M_inv hS b x hAx x_hat ξ hIter k
  -- Suffices to show for each component i
  suffices h : ∀ i : Fin n, |x i - x_hat (k + 1) i| ≤
      infNorm (iterMatrix n M_inv N) *
        infNormVec (fun i => x i - x_hat k i) +
      infNorm M_inv * infNormVec (ξ k) by
    apply infNormVec_le_of_abs_le
    · exact h
    · exact add_nonneg
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
  intro i; rw [hstep i]
  -- |∑ G_{ij}(x_j - x̂_{k,j}) - ∑ M⁻¹_{ij}ξ_{k,j}| ≤ ‖G‖·‖e_k‖ + ‖M⁻¹‖·‖ξ_k‖
  -- Step 1: triangle inequality
  set a := ∑ j, iterMatrix n M_inv N i j * (x j - x_hat k j) with ha_def
  set b := ∑ j, M_inv i j * ξ k j with hb_def
  have htri : |a - b| ≤ |a| + |b| :=
    (abs_add_le a (-b)).trans (by rw [abs_neg])
  -- Step 2: bound each absolute sum
  have ha_bound : |a| ≤ ∑ j, |iterMatrix n M_inv N i j| * |x j - x_hat k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  have hb_bound : |b| ≤ ∑ j, |M_inv i j| * |ξ k j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => le_of_eq (abs_mul _ _)))
  -- Step 3: bound sums using infNormVec
  have ha2 : ∑ j : Fin n, |iterMatrix n M_inv N i j| * |x j - x_hat k j| ≤
      (∑ j, |iterMatrix n M_inv N i j|) *
        infNormVec (fun i => x i - x_hat k i) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact abs_le_infNormVec (fun i => x i - x_hat k i) j
  have hb2 : ∑ j : Fin n, |M_inv i j| * |ξ k j| ≤
      (∑ j, |M_inv i j|) * infNormVec (ξ k) := by
    rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact abs_le_infNormVec (ξ k) j
  -- Combine
  calc |a - b| ≤ |a| + |b| := htri
    _ ≤ (∑ j, |iterMatrix n M_inv N i j|) *
          infNormVec (fun i => x i - x_hat k i) +
        (∑ j, |M_inv i j|) * infNormVec (ξ k) := by
        linarith [ha_bound.trans ha2, hb_bound.trans hb2]
    _ ≤ infNorm (iterMatrix n M_inv N) *
          infNormVec (fun i => x i - x_hat k i) +
        infNorm M_inv * infNormVec (ξ k) := by
        apply add_le_add <;>
          exact mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)

/-- **Eq. 17.8 (Normwise forward bound)**: ‖e_{m+1}‖∞ ≤ q^{m+1}·‖e₀‖∞ + μ·‖M⁻¹‖∞/(1−q)
    where q ≥ ‖G‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Proved by induction
    from `normwise_one_step_bound` using geometric contraction. -/
theorem normwise_forward_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hG : infNorm (iterMatrix n M_inv N) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec (fun i => x i - x_hat (m + 1) i) ≤
      q ^ (m + 1) * infNormVec (fun i => x i - x_hat 0 i) +
      μ * infNorm M_inv / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hMn : 0 ≤ infNorm M_inv := infNorm_nonneg _
  have he₀ := infNormVec_nonneg (fun i => x i - x_hat 0 i)
  induction m with
  | zero =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter 0
    calc infNormVec (fun i => x i - x_hat 1 i)
        ≤ infNorm (iterMatrix n M_inv N) *
            infNormVec (fun i => x i - x_hat 0 i) +
          infNorm M_inv * infNormVec (ξ 0) := hone
      _ ≤ q * infNormVec (fun i => x i - x_hat 0 i) +
          infNorm M_inv * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hG (infNormVec_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hMn
      _ = q ^ 1 * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv := by rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv / (1 - q) := by
          have hnn : 0 ≤ μ * infNorm M_inv := mul_nonneg hμ hMn
          have hdiv : μ * infNorm M_inv ≤ μ * infNorm M_inv / (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_bound n hn A M N M_inv hS b x hAx x_hat ξ hIter (m + 1)
    calc infNormVec (fun i => x i - x_hat (m + 2) i)
        ≤ infNorm (iterMatrix n M_inv N) *
            infNormVec (fun i => x i - x_hat (m + 1) i) +
          infNorm M_inv * infNormVec (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) * infNormVec (fun i => x i - x_hat 0 i) +
            μ * infNorm M_inv / (1 - q)) +
          infNorm M_inv * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hG (infNormVec_nonneg _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hMn
      _ = q ^ (m + 2) * infNormVec (fun i => x i - x_hat 0 i) +
          (q * (μ * infNorm M_inv / (1 - q)) + μ * infNorm M_inv) := by ring
      _ = q ^ (m + 2) * infNormVec (fun i => x i - x_hat 0 i) +
          μ * infNorm M_inv / (1 - q) := by
          congr 1
          field_simp
          ring

-- ============================================================
-- §17.2  Main forward bound (eq 17.13)
-- ============================================================

/-- **Eq. 17.13 (Main componentwise forward bound)**: Composes the componentwise
    forward bound (eq 17.6) with local error simplification (eq 17.10) and the
    partial-sum bound c(A) (eq 17.12).  Given as hypotheses rather than
    re-deriving; this is a straightforward composition. -/
theorem main_forward_bound (n : ℕ) (G M_inv A_inv : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (M N : Fin n → Fin n → ℝ)
    (cn_u θ_x cA : ℝ) (hcn : 0 ≤ cn_u) (_hcA : 0 ≤ cA) (hθ : 0 ≤ θ_x) (m : ℕ)
    (hPartial : PartialSumBound n G M_inv A_inv cA m) :
    ∀ i, ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l : Fin n, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p : Fin n, (|M j p| + |N j p|) * |x p|) ≤
      cn_u * (1 + θ_x) * cA *
        ∑ j : Fin n, |A_inv i j| *
          ∑ p : Fin n, (|M j p| + |N j p|) * |x p| := by
  intro i
  have hcoeff : 0 ≤ cn_u * (1 + θ_x) := mul_nonneg hcn (by linarith)
  calc ∑ k ∈ Finset.range (m + 1),
      ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
        (cn_u * (1 + θ_x) * ∑ p, (|M j p| + |N j p|) * |x p|)
      = cn_u * (1 + θ_x) * ∑ k ∈ Finset.range (m + 1),
          ∑ j : Fin n, (∑ l, |matPow n G k i l| * |M_inv l j|) *
            ∑ p, (|M j p| + |N j p|) * |x p| := by
        rw [Finset.mul_sum]; congr 1; ext k
        rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ cn_u * (1 + θ_x) * (cA * ∑ j : Fin n, |A_inv i j| *
          ∑ p, (|M j p| + |N j p|) * |x p|) := by
        apply mul_le_mul_of_nonneg_left _ hcoeff
        rw [Finset.sum_comm]; rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro j _
        rw [← Finset.sum_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hPartial i j) (Finset.sum_nonneg (fun p _ =>
          mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)))
    _ = cn_u * (1 + θ_x) * cA *
          ∑ j, |A_inv i j| * ∑ p, (|M j p| + |N j p|) * |x p| := by ring

-- ============================================================
-- §17.3  Normwise residual bound (eq 17.19)
-- ============================================================

/-- Normwise one-step residual bound from `one_step_residual`:
    ‖r_{k+1}‖∞ ≤ ‖H‖∞·‖r_k‖∞ + ‖I−H‖∞·‖ξ_k‖∞. -/
theorem normwise_one_step_residual_bound (n : ℕ) (_hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ) (k : ℕ) :
    infNormVec (fun i => b i - ∑ j, A i j * x_hat (k + 1) j) ≤
      infNorm (dualIterMatrix n N M_inv) *
        infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec (ξ k) := by
  have hres := one_step_residual n A M N M_inv hS b x hAx x_hat ξ hIter
  suffices h : ∀ i : Fin n, |b i - ∑ j, A i j * x_hat (k + 1) j| ≤
      infNorm (dualIterMatrix n N M_inv) *
        infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) +
      infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
        infNormVec (ξ k) by
    apply infNormVec_le_of_abs_le
    · exact h
    · exact add_nonneg
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
        (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))
  intro i; rw [hres k i]
  -- |Hr_k - (I-H)ξ_k| ≤ |Hr_k| + |(I-H)ξ_k| ≤ ‖H‖·‖r_k‖ + ‖I-H‖·‖ξ_k‖
  set a := matMulVec n (dualIterMatrix n N M_inv)
      (fun j => b j - ∑ l, A j l * x_hat k l) i
  set c := matMulVec n (matSub_id n (dualIterMatrix n N M_inv)) (ξ k) i
  have htri : |a - c| ≤ |a| + |c| := (abs_add_le a (-c)).trans (by rw [abs_neg])
  have ha : |a| ≤ infNorm (dualIterMatrix n N M_inv) *
      infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
    change |∑ j : Fin n, dualIterMatrix n N M_inv i j *
        (b j - ∑ l, A j l * x_hat k l)| ≤ _
    calc |∑ j, dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)|
        ≤ ∑ j, |dualIterMatrix n N M_inv i j *
            (b j - ∑ l, A j l * x_hat k l)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |dualIterMatrix n N M_inv i j| *
            |b j - ∑ l, A j l * x_hat k l| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |dualIterMatrix n N M_inv i j| *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_le_infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) j
      _ = (∑ j, |dualIterMatrix n N M_inv i j|) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) := by
          rw [Finset.sum_mul]
      _ ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat k j) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)
  have hc : |c| ≤ infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
      infNormVec (ξ k) := by
    change |∑ j : Fin n, matSub_id n (dualIterMatrix n N M_inv) i j *
        ξ k j| ≤ _
    calc |∑ j, matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j|
        ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j * ξ k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| * |ξ k j| := by
          congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j| *
            infNormVec (ξ k) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_le_infNormVec (ξ k) j
      _ = (∑ j, |matSub_id n (dualIterMatrix n N M_inv) i j|) *
            infNormVec (ξ k) := by rw [Finset.sum_mul]
      _ ≤ infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ k) :=
          mul_le_mul_of_nonneg_right (row_sum_le_infNorm _ i)
            (infNormVec_nonneg _)
  linarith

/-- **Eq. 17.19 (Normwise residual bound)**: ‖r_{m+1}‖∞ ≤ q^{m+1}·‖r₀‖∞ + μ·‖I−H‖∞/(1−q)
    where q ≥ ‖H‖∞ and μ ≥ ‖ξ_k‖∞ for all k.  Derived by induction
    from `normwise_one_step_residual_bound` using geometric contraction. -/
theorem normwise_residual_bound (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : ComputedIteration n M N b x_hat ξ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hH : infNorm (dualIterMatrix n N M_inv) ≤ q)
    (μ : ℝ) (hμ : 0 ≤ μ) (hξ_bound : ∀ k, infNormVec (ξ k) ≤ μ)
    (m : ℕ) :
    infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) ≤
      q ^ (m + 1) * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
      μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) / (1 - q) := by
  have hq1' : (0 : ℝ) < 1 - q := by linarith
  have hImH := infNorm_nonneg (matSub_id n (dualIterMatrix n N M_inv))
  induction m with
  | zero =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter 0
    calc infNormVec (fun i => b i - ∑ j, A i j * x_hat 1 j)
        ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ 0) := hone
      _ ≤ q * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hH (infNormVec_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hξ_bound 0) hImH
      _ = q ^ 1 * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) := by
          rw [pow_one]; ring
      _ ≤ q ^ 1 * infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          have hnn : 0 ≤ μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) :=
            mul_nonneg hμ hImH
          have hdiv : μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) ≤
              μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
                (1 - q) := by
            rw [le_div_iff₀ hq1']; nlinarith
          linarith
  | succ m ih =>
    have hone := normwise_one_step_residual_bound n hn A M N M_inv hS b x hAx
        x_hat ξ hIter (m + 1)
    calc infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 2) j)
        ≤ infNorm (dualIterMatrix n N M_inv) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat (m + 1) j) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) *
            infNormVec (ξ (m + 1)) := hone
      _ ≤ q * (q ^ (m + 1) *
              infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
            μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
              (1 - q)) +
          infNorm (matSub_id n (dualIterMatrix n N M_inv)) * μ := by
          apply add_le_add
          · exact le_trans (mul_le_mul_of_nonneg_right hH (infNormVec_nonneg _))
              (mul_le_mul_of_nonneg_left ih hq)
          · exact mul_le_mul_of_nonneg_left (hξ_bound _) hImH
      _ = q ^ (m + 2) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          (q * (μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q)) +
           μ * infNorm (matSub_id n (dualIterMatrix n N M_inv))) := by
          ring
      _ = q ^ (m + 2) *
            infNormVec (fun i => b i - ∑ j, A i j * x_hat 0 j) +
          μ * infNorm (matSub_id n (dualIterMatrix n N M_inv)) /
            (1 - q) := by
          congr 1; field_simp; ring

end LeanFpAnalysis.FP
