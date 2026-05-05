import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LeanFpAnalysis.FP

open scoped BigOperators

structure FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)
  model_sub :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_sub x y = (x - y) * (1 + δ)
  model_mul :
    ∀ x y, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_mul x y = (x * y) * (1 + δ)
  model_div :
    ∀ x y, y ≠ 0 →
      ∃ δ : ℝ,
        |δ| ≤ u ∧
        fl_div x y = (x / y) * (1 + δ)

noncomputable def gamma (fp : FPModel) (n : ℕ) : ℝ :=
  (n * fp.u) / (1 - n * fp.u)

def gammaValid (fp : FPModel) (n : ℕ) : Prop :=
  (n : ℝ) * fp.u < 1

noncomputable def fl_dotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0      => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def fl_matVec (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => fl_dotProduct fp n (A i) x

noncomputable def fl_residual (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_sub (b i) (fl_matVec fp n n A x i)

noncomputable def fl_forwardSub (_fp : FPModel) (n : ℕ)
    (_L : Fin n → Fin n → ℝ) (_b : Fin n → ℝ) : Fin n → ℝ :=
  fun _ => 0

noncomputable def fl_backSub (_fp : FPModel) (n : ℕ)
    (_U : Fin n → Fin n → ℝ) (_b : Fin n → ℝ) : Fin n → ℝ :=
  fun _ => 0

noncomputable def matMul (n : ℕ) (A B : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def matMulVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, A i j * v j

noncomputable def idMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 1 else 0

noncomputable def matSub_id (n : ℕ) (M : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - M i j

noncomputable def infNormVec {n : ℕ} (_hn : 0 < n) (_v : Fin n → ℝ) : ℝ :=
  0

noncomputable def infNorm {n : ℕ} (_hn : 0 < n) (_A : Fin n → Fin n → ℝ) : ℝ :=
  0

structure LUBackwardError (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) : Prop where
  L_diag : ∀ i : Fin n, L_hat i i = 1
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, L_hat i k * U_hat k j - A i j| ≤
      ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|

structure CholeskyBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) : Prop where
  R_upper : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, R_hat k i * R_hat k j - A i j| ≤
      ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j|

structure SplittingSpec (n : ℕ) (A M N M_inv : Fin n → Fin n → ℝ) : Prop where
  splitting : ∀ i j, A i j = M i j - N i j
  inv_left : ∀ i j : Fin n, ∑ k : Fin n, M_inv i k * M k j = idMatrix n i j
  inv_right : ∀ i j : Fin n, ∑ k : Fin n, M i k * M_inv k j = idMatrix n i j

noncomputable def dualIterMatrix (n : ℕ) (N M_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n N M_inv

structure ComputedIteration (n : ℕ) (M N : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ)) : Prop where
  step : ∀ k i, ∑ j : Fin n, M i j * x_hat (k + 1) j =
    ∑ j : Fin n, N i j * x_hat k j + b i + ξ k i

end LeanFpAnalysis.FP
