-- Algorithms/Sylvester/Higham16Psi.lean
--
-- Concrete realizations of the structured Sylvester condition number Psi for
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16.3, equations (16.23)-(16.24).
--
-- The certificate predicate `SylvesterPsiFirstOrderBound` (in
-- `SylvesterPerturbation.lean`) is the theorem-facing form of the (16.24)
-- structured first-order bound: a real `Psi` that dominates the structured
-- inverse first-order Sylvester perturbation map, so that the printed relative
-- bound (16.23) `||dX||_F / ||X||_F <= sqrt 3 * Psi * eps` follows through
-- `sylvester_relative_first_order_bound_of_psi`.
--
-- This file constructs concrete `Psi` witnesses that INSTANTIATE that
-- predicate:
--
--   * `sylvesterPsi_of_inverseOpBound` / `_isPsiFirstOrderBound` -- the honest
--     GENERAL certificate instantiation.  Higham writes
--     `Psi = ||P^{-1}[ alpha (X^T kron I) - beta (I kron X) - gamma I ]||_2 / ||vec X||_2`
--     where `P = I kron A - B^T kron I`.  The exact operator-norm construction
--     of `||P^{-1}||` from `A, B` needs an SVD / operator-norm API that is not
--     present here, so we take the inverse-operator Frobenius bound `M`
--     (an upper bound on `||P^{-1}||_2`, i.e. `1 / sep(A,B)`) as SUPPLIED data,
--     exactly as the book writes `Psi` in terms of `||P^{-1}||`.  From `M` we
--     build the closed-form `Psi = M * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`
--     and prove it satisfies the certificate.
--
--   * `sylvesterPsiDiagonal` / `_isPsiFirstOrderBound` -- the concrete DIAGONAL
--     case.  With `A = diag a`, `B = diag b` and an entrywise separation lower
--     bound `s <= |a_i - b_j|` (so `s > 0` is a lower bound on `sep` and
--     `1/s` bounds every entry of the explicit inverse
--     `sylvesterDiagonalVecCoeffInv`, whose entries are `(a_i - b_j)^{-1}`),
--     the inverse-operator bound `M = 1/s` is explicit, and
--     `sylvesterPsiDiagonal = (1/s) * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`.
--     This closes (16.24) for the diagonalizable / distinct-eigenvalue case
--     that the diagonal foundation of `Higham16.lean` already covers.
--
--   * `H16_eq16_24_structured_condition_diagonal` -- the labeled (16.24)/(16.23)
--     wrapper tying the diagonal `Psi` to the printed relative first-order
--     perturbation bound via `sylvester_relative_first_order_bound_of_psi`.
--
-- Honest scope.  The DIAGONAL witness is fully self-contained (no supplied
-- operator-norm data beyond the entrywise separation `s`, which is elementary
-- for diagonal matrices).  It therefore covers exactly the case where `A` and
-- `B` are diagonal with separated diagonal entries -- i.e. the diagonalizable
-- Sylvester operator with distinct eigenvalues expressed in eigencoordinates.
-- The GENERAL witness takes the `||P^{-1}||`-type bound `M` as data, matching
-- how Higham states `Psi`; instantiating `M` for a nondiagonal `A, B` from the
-- entries of `A, B` alone is precisely the missing SVD/operator-norm step.

import LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterPerturbation
import LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Triple-norm single-block bounds (from eq (16.23))
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.23) (p. 313):
    each normalized perturbation block is bounded by the stacked triple norm.
    Since `sylvesterScaledPerturbationTripleNorm` is the square root of a sum of
    the three nonnegative normalized squared blocks, a single block is bounded
    by the whole square root, giving `||dA||_F <= alpha * tripleNorm`. -/
theorem frobNorm_le_alpha_mul_tripleNorm (n : ℕ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ : ℝ) (hα : 0 < α) :
    frobNorm ΔA ≤
      α * sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
  have hterm :
      (frobNorm ΔA / α) ^ 2 ≤
        frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
          frobNormSq ΔC / γ ^ 2 := by
    have hB : 0 ≤ frobNormSq ΔB / β ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔB) (sq_nonneg β)
    have hC : 0 ≤ frobNormSq ΔC / γ ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔC) (sq_nonneg γ)
    have heq : (frobNorm ΔA / α) ^ 2 = frobNormSq ΔA / α ^ 2 := by
      rw [div_pow, frobNorm_sq]
    rw [heq]; linarith
  have hnn : 0 ≤ frobNorm ΔA / α :=
    div_nonneg (frobNorm_nonneg ΔA) (le_of_lt hα)
  have hsqrt :
      frobNorm ΔA / α ≤
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
    unfold sylvesterScaledPerturbationTripleNorm
    calc frobNorm ΔA / α
        = Real.sqrt ((frobNorm ΔA / α) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
            frobNormSq ΔC / γ ^ 2) := Real.sqrt_le_sqrt hterm
  rw [div_le_iff₀ hα] at hsqrt
  linarith [hsqrt]

/-- Higham, 2nd ed., §16.3, eq (16.23) (p. 313): the `dB/beta` block. -/
theorem frobNorm_le_beta_mul_tripleNorm (n : ℕ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ : ℝ) (hβ : 0 < β) :
    frobNorm ΔB ≤
      β * sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
  have hterm :
      (frobNorm ΔB / β) ^ 2 ≤
        frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
          frobNormSq ΔC / γ ^ 2 := by
    have hA : 0 ≤ frobNormSq ΔA / α ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔA) (sq_nonneg α)
    have hC : 0 ≤ frobNormSq ΔC / γ ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔC) (sq_nonneg γ)
    have heq : (frobNorm ΔB / β) ^ 2 = frobNormSq ΔB / β ^ 2 := by
      rw [div_pow, frobNorm_sq]
    rw [heq]; linarith
  have hnn : 0 ≤ frobNorm ΔB / β :=
    div_nonneg (frobNorm_nonneg ΔB) (le_of_lt hβ)
  have hsqrt :
      frobNorm ΔB / β ≤
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
    unfold sylvesterScaledPerturbationTripleNorm
    calc frobNorm ΔB / β
        = Real.sqrt ((frobNorm ΔB / β) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
            frobNormSq ΔC / γ ^ 2) := Real.sqrt_le_sqrt hterm
  rw [div_le_iff₀ hβ] at hsqrt
  linarith [hsqrt]

/-- Higham, 2nd ed., §16.3, eq (16.23) (p. 313): the `dC/gamma` block. -/
theorem frobNorm_le_gamma_mul_tripleNorm (n : ℕ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ : ℝ) (hγ : 0 < γ) :
    frobNorm ΔC ≤
      γ * sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
  have hterm :
      (frobNorm ΔC / γ) ^ 2 ≤
        frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
          frobNormSq ΔC / γ ^ 2 := by
    have hA : 0 ≤ frobNormSq ΔA / α ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔA) (sq_nonneg α)
    have hB : 0 ≤ frobNormSq ΔB / β ^ 2 :=
      div_nonneg (frobNormSq_nonneg ΔB) (sq_nonneg β)
    have heq : (frobNorm ΔC / γ) ^ 2 = frobNormSq ΔC / γ ^ 2 := by
      rw [div_pow, frobNorm_sq]
    rw [heq]; linarith
  have hnn : 0 ≤ frobNorm ΔC / γ :=
    div_nonneg (frobNorm_nonneg ΔC) (le_of_lt hγ)
  have hsqrt :
      frobNorm ΔC / γ ≤
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
    unfold sylvesterScaledPerturbationTripleNorm
    calc frobNorm ΔC / γ
        = Real.sqrt ((frobNorm ΔC / γ) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (frobNormSq ΔA / α ^ 2 + frobNormSq ΔB / β ^ 2 +
            frobNormSq ΔC / γ ^ 2) := Real.sqrt_le_sqrt hterm
  rw [div_le_iff₀ hγ] at hsqrt
  linarith [hsqrt]

-- ============================================================
-- Linearized right-hand side bound (from eq (16.22))
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.22)/(16.23) (p. 313):
    the linearized first-order right-hand side
    `R = dC - dA X + X dB` has Frobenius norm bounded by
    `((alpha + beta) ||X||_F + gamma) * tripleNorm`.

    This is the structured analogue of the triangle-inequality step in
    `residual_bound`, but expressed through the stacked triple norm of the
    normalized data blocks rather than a single scalar budget `eps`. -/
theorem sylvester_first_order_rhs_frobNorm_le (n : ℕ)
    (X ΔA ΔB ΔC : Fin n → Fin n → ℝ) (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    frobNorm (fun i j => ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) ≤
      ((α + β) * frobNorm X + γ) *
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
  set T := sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ with hT
  -- Block bounds from (16.23).
  have hA := frobNorm_le_alpha_mul_tripleNorm n ΔA ΔB ΔC α β γ hα
  have hB := frobNorm_le_beta_mul_tripleNorm n ΔA ΔB ΔC α β γ hβ
  have hC := frobNorm_le_gamma_mul_tripleNorm n ΔA ΔB ΔC α β γ hγ
  -- Submultiplicativity for the two product blocks.
  have hAX : frobNorm (matMul n ΔA X) ≤ (α * T) * frobNorm X :=
    le_trans (frobNorm_matMul_le ΔA X)
      (mul_le_mul_of_nonneg_right hA (frobNorm_nonneg X))
  have hXB : frobNorm (matMul n X ΔB) ≤ frobNorm X * (β * T) :=
    le_trans (frobNorm_matMul_le X ΔB)
      (mul_le_mul_of_nonneg_left hB (frobNorm_nonneg X))
  -- Rewrite `dC - dA X + X dB = dC + (X dB - dA X)` and apply triangle twice.
  have h_rw :
      (fun i j => ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) =
        (fun i j => ΔC i j + (matMul n X ΔB i j - matMul n ΔA X i j)) := by
    ext i j; ring
  rw [h_rw]
  have htri1 :=
    frobNorm_add_le ΔC (fun i j => matMul n X ΔB i j - matMul n ΔA X i j)
  have htri2 := frobNorm_sub_le (matMul n X ΔB) (matMul n ΔA X)
  -- Combine all bounds.
  have hbudget :
      frobNorm ΔC + (frobNorm (matMul n X ΔB) + frobNorm (matMul n ΔA X)) ≤
        ((α + β) * frobNorm X + γ) * T := by
    have hXnn := frobNorm_nonneg X
    nlinarith [hA, hB, hC, hAX, hXB]
  calc
    frobNorm (fun i j => ΔC i j + (matMul n X ΔB i j - matMul n ΔA X i j))
        ≤ frobNorm ΔC +
            frobNorm (fun i j => matMul n X ΔB i j - matMul n ΔA X i j) := htri1
    _ ≤ frobNorm ΔC +
          (frobNorm (matMul n X ΔB) + frobNorm (matMul n ΔA X)) := by
            linarith [htri2]
    _ ≤ ((α + β) * frobNorm X + γ) * T := hbudget

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dA / alpha` block bound. -/
alias H16_eq16_23_frobNorm_le_alpha_mul_tripleNorm :=
  frobNorm_le_alpha_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dB / beta` block bound. -/
alias H16_eq16_23_frobNorm_le_beta_mul_tripleNorm :=
  frobNorm_le_beta_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dC / gamma` block bound. -/
alias H16_eq16_23_frobNorm_le_gamma_mul_tripleNorm :=
  frobNorm_le_gamma_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the first-order Sylvester right-hand-side
    Frobenius bound. -/
alias H16_eq16_23_sylvester_first_order_rhs_frobNorm_le :=
  sylvester_first_order_rhs_frobNorm_le

-- ============================================================
-- General certificate instantiation from a supplied inverse-operator bound
-- (eq (16.24), the `||P^{-1}||`-structured Psi taken as data)
-- ============================================================

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    an inverse-operator Frobenius bound for the Sylvester operator `T(Y) = AY - YB`.
    `M` bounds the norm of the inverse map, i.e. `M >= 1 / sep(A,B)`; in the
    vec/Kronecker picture this is the `||P^{-1}||_2`-type quantity, with
    `P = I kron A - B^T kron I` (eq (16.2)).  We take it as SUPPLIED data:
    the closed-form construction of `||P^{-1}||` from `A, B` needs an
    SVD/operator-norm API not available here. -/
def SylvesterInverseOpBound (n : ℕ) (A B : Fin n → Fin n → ℝ) (M : ℝ) : Prop :=
  ∀ Y : Fin n → Fin n → ℝ,
    frobNorm Y ≤ M * frobNorm (sylvesterOp n A B Y)

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered abbreviation for the supplied inverse-operator bound
    underlying the structured condition number `Psi`. -/
abbrev H16_eq16_24_SylvesterInverseOpBound :=
  SylvesterInverseOpBound

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    a `SepLowerBound` supplies an inverse-operator bound with `M = 1 / sigma`.
    This records that `SylvesterInverseOpBound` is exactly the `||P^{-1}||`
    (= `1 / sep`) data the book uses to define `Psi`. -/
theorem sylvesterInverseOpBound_of_sepLowerBound (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hSep : SepLowerBound n A B σ) :
    SylvesterInverseOpBound n A B (1 / σ) := by
  intro Y
  by_cases hY : frobNormSq Y = 0
  · -- `Y = 0`, both sides vanish.
    have hYnorm : frobNorm Y = 0 := by
      rw [frobNorm_eq_sqrt_frobNormSq, Real.sqrt_eq_zero (frobNormSq_nonneg Y)]
      exact hY
    rw [hYnorm]
    have : 0 ≤ 1 / σ * frobNorm (sylvesterOp n A B Y) :=
      mul_nonneg (by positivity) (frobNorm_nonneg _)
    linarith
  · -- `sigma * ||Y|| <= ||T(Y)||`, then divide by sigma.
    have hbnd := hSep.2 Y hY
    rw [← frobNorm_sq, ← frobNorm_sq] at hbnd
    have hσ_nn : 0 ≤ σ := le_of_lt hσ
    have hstep : σ * frobNorm Y ≤ frobNorm (sylvesterOp n A B Y) := by
      nlinarith [sq_nonneg (σ * frobNorm Y - frobNorm (sylvesterOp n A B Y)),
        frobNorm_nonneg (sylvesterOp n A B Y), frobNorm_nonneg Y]
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hσ, mul_comm]
    exact hstep

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    the concrete structured condition number built from a supplied
    inverse-operator bound `M` and the data weights `alpha, beta, gamma`,
    matching the printed `Psi = ||P^{-1}[ ... ]|| / ||vec X||`:
      `Psi = M * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`.
    (The `/ ||X||_F` is exactly the book's normalization by `||vec X||`.) -/
noncomputable def sylvesterPsi_of_inverseOpBound (n : ℕ)
    (X : Fin n → Fin n → ℝ) (α β γ M : ℝ) : ℝ :=
  M * ((α + β) * frobNorm X + γ) / frobNorm X

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered abbreviation for the supplied-inverse-bound structured
    condition number value. -/
noncomputable abbrev H16_eq16_24_sylvesterPsi_of_inverseOpBound :=
  sylvesterPsi_of_inverseOpBound

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    the supplied-`M` structured condition number satisfies the certificate
    predicate `SylvesterPsiFirstOrderBound`.  This turns the (16.24) certificate
    into a usable theorem for any Sylvester operator equipped with an
    inverse-operator (i.e. `||P^{-1}||`) bound. -/
theorem sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound (n : ℕ)
    (A B X : Fin n → Fin n → ℝ) (α β γ M : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hX : 0 < frobNorm X)
    (hInv : SylvesterInverseOpBound n A B M) :
    SylvesterPsiFirstOrderBound n A B X α β γ
      (sylvesterPsi_of_inverseOpBound n X α β γ M) := by
  intro ΔA ΔB ΔC ΔX hLin
  set T := sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ with hT
  -- `T(dX) = R` pointwise, so `||T(dX)|| = ||R||`.
  have hopeq :
      frobNorm (sylvesterOp n A B ΔX) =
        frobNorm (fun i j => ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) := by
    congr 1; ext i j; exact hLin i j
  -- Inverse-operator bound applied to `dX`.
  have hInvX := hInv ΔX
  rw [hopeq] at hInvX
  -- Structured RHS bound.
  have hrhs :=
    sylvester_first_order_rhs_frobNorm_le n X ΔA ΔB ΔC α β γ hα hβ hγ
  have hTnn : 0 ≤ T := by
    rw [hT]; unfold sylvesterScaledPerturbationTripleNorm; exact Real.sqrt_nonneg _
  -- Chain: ||dX|| <= M ||R|| <= M ((a+b)||X|| + g) T.
  have hchain :
      frobNorm ΔX ≤ M * (((α + β) * frobNorm X + γ) * T) := by
    calc
      frobNorm ΔX
          ≤ M * frobNorm
              (fun i j => ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) := hInvX
      _ ≤ M * (((α + β) * frobNorm X + γ) * T) :=
            mul_le_mul_of_nonneg_left hrhs hM
  -- Rewrite the certificate RHS `Psi * ||X|| * T` into `M ((a+b)||X||+g) T`.
  have hpsi :
      sylvesterPsi_of_inverseOpBound n X α β γ M * frobNorm X * T =
        M * (((α + β) * frobNorm X + γ) * T) := by
    unfold sylvesterPsi_of_inverseOpBound
    field_simp
  rw [hpsi]
  exact hchain

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    a positive `SepLowerBound` certificate instantiates the structured
    condition-number predicate with the safe inverse-operator constant
    `M = 1 / sigma`. This is a source-facing sep-based realization of `Psi`;
    it is not the exact displayed operator norm when that norm is sharper. -/
theorem sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound (n : ℕ)
    (A B X : Fin n → Fin n → ℝ) (α β γ sigma : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma) :
    SylvesterPsiFirstOrderBound n A B X α β γ
      (sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma)) := by
  have hInv := sylvesterInverseOpBound_of_sepLowerBound n A B sigma hsigma hSep
  have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
  exact sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound n A B X α β γ
    (1 / sigma) hα hβ hγ hMnn hX hInv

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.23)-(16.24):
    a positive lower bound on the exact infimum model of `sep(A,B)`
    instantiates the structured first-order `Psi` certificate through the safe
    reciprocal condition value `1 / sigma`. -/
theorem sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound (n : Nat)
    (A B X : Fin n -> Fin n -> Real) (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B) :
    SylvesterPsiFirstOrderBound n A B X alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma)) := by
  exact
    sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound n A B X
      alpha beta gamma sigma halpha hbeta hgamma hsigma hX
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., §16.3, eq (16.24) (p. 313):
    source-facing sep-based first-order Sylvester bound before the
    `sqrt 3 * eps` relative wrapper. This simply applies the structured `Psi`
    certificate instantiated by `sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound`
    to a supplied linearized perturbation equation. -/
theorem sylvester_first_order_bound_of_sepLowerBound (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ sigma : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hLin : ∀ i j,
      sylvesterOp n A B ΔX i j =
        ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX ≤
      sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n ΔA ΔB ΔC α β γ := by
  exact
    sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound n
      A B X α β γ sigma hα hβ hγ hsigma hX hSep
      ΔA ΔB ΔC ΔX hLin

/-- Higham, 2nd ed., §16.3-§16.4, equations (16.23)-(16.24):
    source-facing first-order Sylvester bound from a positive lower bound on
    the exact infimum model of `sep(A,B)`, exposed before the relative
    `sqrt 3 * eps` wrapper. -/
theorem sylvester_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound n
      A B X alpha beta gamma sigma halpha hbeta hgamma hsigma hX hle
      DeltaA DeltaB DeltaC DeltaX hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for turning a positive separation lower bound into
    supplied inverse-operator data. -/
alias H16_eq16_24_sylvesterInverseOpBound_of_sepLowerBound :=
  sylvesterInverseOpBound_of_sepLowerBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the supplied-inverse-bound structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound :=
  sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the sep-lower-bound structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound :=
  sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the exact-infimum structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound :=
  sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the sep-lower-bound first-order Sylvester endpoint. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hSep hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the exact-infimum first-order Sylvester endpoint. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hle hLin

/-- Higham, 2nd ed., §16.3, eqs. (16.23)-(16.24) (p. 313):
    sep-based structured first-order perturbation bound. If
    `SepLowerBound A B sigma` holds, then the printed relative bound follows
    with the safe condition-number value
    `sylvesterPsi_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied sep lower-bound
    certificate. It does not compute the sharper nondiagonal operator norm
    `||P^{-1}[...]||`. -/
theorem H16_eq16_24_structured_condition_of_sepLowerBound (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ sigma ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsigma : 0 < sigma) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      sylvesterOp n A B ΔX i j =
        ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma) * ε := by
  have hPsi :=
    sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound n A B X α β γ sigma
      hα hβ hγ hsigma hX hSep
  have hΨnn : 0 ≤ sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma) := by
    unfold sylvesterPsi_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ (α + β) * frobNorm X + γ := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt hα, le_of_lt hβ, le_of_lt hγ, hXnn]
    positivity
  exact sylvester_relative_first_order_bound_of_psi n
    A B X ΔA ΔB ΔC ΔX α β γ
    (sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma)) ε
    hPsi hX hΨnn hα hβ hγ hε hΔA hΔB hΔC hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.23)-(16.24):
    structured first-order perturbation bound from a positive lower bound on
    the exact infimum model of `sep(A,B)`.  This is the same safe Psi value as
    the `SepLowerBound` route, exposed directly through `sylvesterSepInf`.

    Scope: this is an exact-arithmetic lower-bound certificate route. It does
    not assert the sharper displayed nondiagonal operator norm when that norm is
    smaller than the reciprocal sep bound. -/
theorem H16_eq16_24_structured_condition_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equations (16.23)-(16.24):
    sep-based relative first-order Sylvester perturbation bound with the safe
    condition value `sylvesterPsi_of_inverseOpBound ... (1 / sigma)`. -/
theorem sylvester_relative_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.23)-(16.24):
    relative first-order Sylvester perturbation bound from a positive lower
    bound on the exact infimum model of `sep(A,B)`. -/
theorem sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hle
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the sep-lower-bound relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    sylvester_relative_first_order_bound_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the exact-infimum relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hle
      hDeltaA hDeltaB hDeltaC hLin

-- ============================================================
-- Diagonal-case Psi realization (eq (16.24), diagonal / distinct-eigenvalue)
-- ============================================================

/-- Higham, 2nd ed., §16.1, eqs (16.1)-(16.3), diagonal case (p. 306):
    in diagonal coordinates the Sylvester operator `AY - YB` acts entrywise as
    multiplication by `a_i - b_j`.  Bridges the rectangular diagonal-apply lemma
    of `Higham16.lean` to the square legacy `sylvesterOp` used by the
    certificate. -/
theorem sylvesterOp_diagonal_apply (n : ℕ)
    (a b : Fin n → ℝ) (Y : Fin n → Fin n → ℝ) (i j : Fin n) :
    sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) Y i j =
      (a i - b j) * Y i j := by
  have h := sylvesterOpRect_diagonal_apply n n a b Y i j
  rw [sylvesterOpRect_square_eq_sylvesterOp] at h
  exact h

/-- Higham, 2nd ed., §16.1, eq (16.3), diagonal case (p. 306):
    from an entrywise separation lower bound `s <= |a_i - b_j|` (with `s > 0`,
    the explicit inverse `sylvesterDiagonalVecCoeffInv` has every entry bounded
    by `1/s`), the diagonal Sylvester operator satisfies the inverse-operator
    bound with `M = 1/s`.  This is the concrete `||P^{-1}||`-type constant for
    the separated diagonal case: no SVD is needed. -/
theorem sylvesterInverseOpBound_diagonal (n : ℕ)
    (a b : Fin n → ℝ) (s : ℝ) (hs : 0 < s)
    (hsep : ∀ i j, s ≤ |a i - b j|) :
    SylvesterInverseOpBound n (Matrix.diagonal a) (Matrix.diagonal b) (1 / s) := by
  intro Y
  -- entrywise: |Y i j| <= (1/s) * |T(Y) i j|.
  have hentry : ∀ i j : Fin n,
      |Y i j| ≤ (1 / s) * |sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) Y i j| := by
    intro i j
    have happ := sylvesterOp_diagonal_apply n a b Y i j
    rw [happ, abs_mul]
    -- goal: |Y i j| <= (1/s) * (|a_i - b_j| * |Y i j|).
    have hYnn : 0 ≤ |Y i j| := abs_nonneg _
    have hlow : s ≤ |a i - b j| := hsep i j
    rw [one_div, ← mul_assoc]
    -- reduce to 1 * |Y| <= (s⁻¹ |a-b|) * |Y| using s⁻¹|a-b| >= 1.
    have hcoeff : (1 : ℝ) ≤ s ⁻¹ * |a i - b j| := by
      rw [le_inv_mul_iff₀ hs, mul_one]; exact hlow
    calc |Y i j| = 1 * |Y i j| := (one_mul _).symm
      _ ≤ (s ⁻¹ * |a i - b j|) * |Y i j| :=
            mul_le_mul_of_nonneg_right hcoeff hYnn
  -- Frobenius from entrywise via the library helper.
  have hMnn : (0 : ℝ) ≤ 1 / s := by positivity
  exact frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le Y
    (sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) Y) hMnn hentry

/-- Higham, 2nd ed., §16.3, eq (16.24), diagonal case (p. 313):
    the concrete structured condition number for the separated diagonal
    Sylvester operator, with the explicit inverse-operator constant `1/s`
    coming from `sylvesterDiagonalVecCoeffInv` (entries `(a_i - b_j)^{-1}`,
    each bounded by `1/s`):
      `sylvesterPsiDiagonal = (1/s) * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`. -/
noncomputable def sylvesterPsiDiagonal (n : ℕ)
    (X : Fin n → Fin n → ℝ) (α β γ s : ℝ) : ℝ :=
  sylvesterPsi_of_inverseOpBound n X α β γ (1 / s)

/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered abbreviation for the explicit diagonal structured
    condition number value. -/
noncomputable abbrev H16_eq16_24_sylvesterPsiDiagonal :=
  sylvesterPsiDiagonal

/-- Higham, 2nd ed., §16.3, eq (16.24), diagonal case (p. 313):
    the diagonal structured condition number `sylvesterPsiDiagonal` satisfies the
    certificate predicate `SylvesterPsiFirstOrderBound` for the separated
    diagonal Sylvester operator `A = diag a`, `B = diag b`.  This CLOSES (16.24)
    for the diagonalizable / distinct-eigenvalue case (eigenvalues `a_i` of `A`,
    `b_j` of `B`, all separated by `s`). -/
theorem sylvesterPsiDiagonal_isPsiFirstOrderBound (n : ℕ)
    (a b : Fin n → ℝ) (X : Fin n → Fin n → ℝ) (α β γ s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : 0 < s)
    (hX : 0 < frobNorm X)
    (hsep : ∀ i j, s ≤ |a i - b j|) :
    SylvesterPsiFirstOrderBound n (Matrix.diagonal a) (Matrix.diagonal b) X
      α β γ (sylvesterPsiDiagonal n X α β γ s) := by
  have hInv := sylvesterInverseOpBound_diagonal n a b s hs hsep
  have hMnn : (0 : ℝ) ≤ 1 / s := by positivity
  unfold sylvesterPsiDiagonal
  exact sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound n
    (Matrix.diagonal a) (Matrix.diagonal b) X α β γ (1 / s)
    hα hβ hγ hMnn hX hInv

/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered alias for the diagonal structured-condition certificate. -/
alias H16_eq16_24_sylvesterPsiDiagonal_isPsiFirstOrderBound :=
  sylvesterPsiDiagonal_isPsiFirstOrderBound

-- ============================================================
-- Labeled (16.24)/(16.23) wrapper for the diagonal case
-- ============================================================

/-- Higham, 2nd ed., §16.3, eqs (16.23)-(16.24), diagonal case (p. 313):
    the printed structured relative first-order perturbation bound
      `||dX||_F / ||X||_F <= sqrt 3 * Psi * eps`
    with the CONCRETE diagonal condition number `Psi = sylvesterPsiDiagonal`.

    Hypotheses: `A = diag a`, `B = diag b` with entrywise separation `s`, data
    weights `alpha, beta, gamma`, normwise data budgets `||dA|| <= eps*alpha`,
    `||dB|| <= eps*beta`, `||dC|| <= eps*gamma`, and the linearized first-order
    equation `A dX - dX B = dC - dA X + X dB`.

    Honest scope: this is the (16.23)/(16.24) closure for the separated diagonal
    (equivalently: distinct-eigenvalue, diagonalized) Sylvester equation. -/
theorem H16_eq16_24_structured_condition_diagonal (n : ℕ)
    (a b : Fin n → ℝ) (X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ s ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hsep : ∀ i j, s ≤ |a i - b j|)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) ΔX i j =
        ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 3 * sylvesterPsiDiagonal n X α β γ s * ε := by
  have hPsi :=
    sylvesterPsiDiagonal_isPsiFirstOrderBound n a b X α β γ s
      hα hβ hγ hs hX hsep
  have hΨnn : 0 ≤ sylvesterPsiDiagonal n X α β γ s := by
    unfold sylvesterPsiDiagonal sylvesterPsi_of_inverseOpBound
    have h1 : (0 : ℝ) ≤ 1 / s := by positivity
    have h2 : 0 ≤ (α + β) * frobNorm X + γ := by
      have := frobNorm_nonneg X; nlinarith
    positivity
  exact sylvester_relative_first_order_bound_of_psi n
    (Matrix.diagonal a) (Matrix.diagonal b) X ΔA ΔB ΔC ΔX
    α β γ (sylvesterPsiDiagonal n X α β γ s) ε
    hPsi hX hΨnn hα hβ hγ hε hΔA hΔB hΔC hLin

/-- Higham, 2nd ed., Section 16.3, equations (16.23)-(16.24), diagonal case:
    relative first-order Sylvester perturbation bound with the concrete
    diagonal condition number `sylvesterPsiDiagonal`. -/
theorem sylvester_relative_first_order_bound_diagonal (n : Nat)
    (a b : Fin n -> Real) (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma s eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 * sylvesterPsiDiagonal n X alpha beta gamma s * eps := by
  exact
    H16_eq16_24_structured_condition_diagonal n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma s eps
      halpha hbeta hgamma hs heps hX hsep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered alias for the diagonal relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_diagonal (n : Nat)
    (a b : Fin n -> Real) (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma s eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 * sylvesterPsiDiagonal n X alpha beta gamma s * eps := by
  exact
    sylvester_relative_first_order_bound_diagonal n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma s eps
      halpha hbeta hgamma hs heps hX hsep
      hDeltaA hDeltaB hDeltaC hLin

end LeanFpAnalysis.FP
