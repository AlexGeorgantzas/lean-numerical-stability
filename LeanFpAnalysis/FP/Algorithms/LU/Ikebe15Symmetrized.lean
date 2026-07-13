-- Algorithms/LU/Ikebe15Symmetrized.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- PROBLEM 15.7 (p. 305).  Intended Appendix A solution: "symmetrize the
-- matrix".
--
-- Problem statement (verbatim intent):
--   "The representation of Theorem 15.9 for the inverse of nonsingular,
--    tridiagonal, and irreducible A ∈ ℝⁿˣⁿ involves 4n parameters, yet A
--    depends only on 3n−2 parameters.  Obtain an alternative representation
--    that involves only 3n−2 parameters.  (Hint: symmetrize the matrix.)"
--
-- Theorem 15.9 (Ikebe) gives (A⁻¹)_{ij} = xᵢyⱼ (i ≤ j), = pᵢqⱼ (i ≥ j) with
-- FOUR vectors x,y,p,q (4n numbers).  This file carries out the symmetrization
-- reduction to an (x, y, D) representation:
--
--   (a) `symmetrized_isSymmetric` — for an irreducible tridiagonal `A` and a
--       nonzero diagonal `D` whose entries satisfy the adjacent symmetrizing
--       relation `dᵢ² a_{i,i+1} = d_{i+1}² a_{i+1,i}`, the similar matrix
--       `B := D A D⁻¹` is symmetric.
--   (a′) `symmetrizerDiag` / `symmetrizerDiag_symmetrizes` /
--        `symmetrizerDiag_ne_zero` — a CONSTRUCTION of such a `D` from the
--        ratios of the super-/sub-diagonal entries (via square roots), valid
--        when those ratios are positive.
--   (b) `symmetrized_inv_symmetric` / `inv_scaling_relation` — `B⁻¹` is
--       symmetric, giving the collapse identity `dᵢ² (A⁻¹)_{ij} =
--       dⱼ² (A⁻¹)_{ji}`.
--   (c) `ikebe_symmetrized_representation` /
--       `ikebe_symmetrized_representation_constructive` — combining Ikebe with
--       the collapse identity, `A⁻¹` is represented, for ALL i,j, by
--         (A⁻¹)_{ij} = (dⱼ / dᵢ) · u_{min(i,j)} · v_{max(i,j)}
--       with the two vectors `u_i = dᵢ xᵢ`, `v_i = yᵢ / dᵢ` and the diagonal
--       `D`.  The lower factors p,q are ELIMINATED.
--
-- PARAMETER COUNT (partly proved, partly documented residual).
--   Proved ingredients: only x,y (2n numbers, via u,v) and D enter the
--   conclusion (`ikebe_symmetrized_representation`); and `D₀ = 1` is fixed
--   (`symmetrizerDiag_zero`), so D contributes only its n−1 step ratios.
--   Documented arithmetic: u,v carry 2n numbers with one common scaling
--   redundancy ((u,v) ↦ (λu, v/λ) leaves the off-diagonal product fixed),
--   i.e. 2n−1 free; with D's n−1 ratios this gives (2n−1)+(n−1) = 3n−2,
--   matching the 3n−2 parameters of A.  The literal free-parameter *count*
--   (a statement about the dimension of the parametrization modulo the
--   scaling quotient) is left as a documented residual — see final note.
--
-- IMPORT-ONLY: reuses `ikebe_tridiag_inv_structure` and the diagonal-scaling /
-- inverse-predicate lemmas from the base modules; no existing file is edited.
--
-- Cite: Higham, 2nd ed., Problem 15.7; Theorem 15.9 (Ikebe 1979).

import LeanFpAnalysis.FP.Algorithms.LU.TridiagonalCond
import LeanFpAnalysis.FP.Algorithms.LU.TridiagonalCondCh15
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP.Ch15

open scoped BigOperators
open LeanFpAnalysis.FP

-- ============================================================
-- (a′)  Explicit construction of the symmetrizer from entry ratios
-- ============================================================

/-- Square-root of the super/sub-diagonal ratio at natural index `m`
    (the multiplicative step of the symmetrizer).  Out of range it is `1`. -/
noncomputable def sqrtRatioStep {n : ℕ} (A : Fin n → Fin n → ℝ) (m : ℕ) : ℝ :=
  if h : m + 1 < n then
    Real.sqrt (A ⟨m, by omega⟩ ⟨m + 1, h⟩ / A ⟨m + 1, h⟩ ⟨m, by omega⟩)
  else 1

/-- Raw (ℕ-indexed) symmetrizer diagonal:
    `dfun 0 = 1`, `dfun (k+1) = dfun k · sqrtRatioStep k`.
    So `dfun k = ∏_{m<k} √(a_{m,m+1}/a_{m+1,m})`. -/
noncomputable def symmDiagRaw {n : ℕ} (A : Fin n → Fin n → ℝ) : ℕ → ℝ
  | 0 => 1
  | (k + 1) => symmDiagRaw A k * sqrtRatioStep A k

/-- **Problem 15.7 (a′): the explicit symmetrizing diagonal `D`.**

    `Dᵢ = ∏_{m<i} √(a_{m,m+1} / a_{m+1,m})`, i.e. `D₀ = 1` and each step scales
    by the square root of the local super/sub-diagonal ratio.  This is the
    classical symmetrizer for an irreducible tridiagonal matrix. -/
noncomputable def symmetrizerDiag {n : ℕ} (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  symmDiagRaw A i.val

/-- Nonzero-ratio hypothesis: on every adjacent pair the super/sub-diagonal
    ratio is strictly positive (equivalently, `a_{i,i+1}` and `a_{i+1,i}` are
    nonzero and of the SAME sign).  This is exactly the condition under which a
    *real* symmetrizer exists. -/
def PosRatio {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ (m : Fin n) (h : m.val + 1 < n),
    0 < A m ⟨m.val + 1, h⟩ / A ⟨m.val + 1, h⟩ m

/-- The raw symmetrizer is nonzero at every natural index (under `PosRatio`). -/
lemma symmDiagRaw_ne_zero {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hpos : PosRatio A) : ∀ k : ℕ, k ≤ n → symmDiagRaw A k ≠ 0 := by
  intro k
  induction k with
  | zero => intro _; simp [symmDiagRaw]
  | succ m ih =>
      intro hm
      have hm' : m ≤ n := by omega
      have hmn : m + 1 ≤ n := hm
      have hstep : sqrtRatioStep A m ≠ 0 := by
        unfold sqrtRatioStep
        by_cases h : m + 1 < n
        · rw [dif_pos h]
          have := hpos ⟨m, by omega⟩ (by simpa using h)
          exact ne_of_gt (Real.sqrt_pos.mpr (by simpa using this))
        · rw [dif_neg h]; norm_num
      simp only [symmDiagRaw]
      exact mul_ne_zero (ih hm') hstep

/-- `Dᵢ ≠ 0` for the explicit symmetrizer (under `PosRatio`). -/
lemma symmetrizerDiag_ne_zero {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hpos : PosRatio A) : ∀ i : Fin n, symmetrizerDiag A i ≠ 0 := by
  intro i
  exact symmDiagRaw_ne_zero A hpos i.val (le_of_lt i.isLt)

/-- **Normalization `D₀ = 1`.**  The symmetrizer is fixed to `1` at index `0`,
    so it contributes only its `n − 1` step ratios as free data (not `n`):
    this is the `−1` in the `(2n − 1) + (n − 1) = 3n − 2` count. -/
lemma symmetrizerDiag_zero {n : ℕ} (A : Fin n → Fin n → ℝ) (h0 : 0 < n) :
    symmetrizerDiag A ⟨0, h0⟩ = 1 := by
  simp [symmetrizerDiag, symmDiagRaw]

/-- A positive super/sub-diagonal ratio forces a nonzero sub-diagonal entry
    (in Lean `x / 0 = 0`, so `0 < x / (A ⟨m+1⟩ m)` needs `A ⟨m+1⟩ m ≠ 0`). -/
lemma sub_ne_zero_of_posRatio {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hpos : PosRatio A) (m : Fin n) (h : m.val + 1 < n) :
    A ⟨m.val + 1, h⟩ m ≠ 0 := by
  intro hz
  have := hpos m h
  rw [hz, div_zero] at this
  exact lt_irrefl 0 this

/-- **Problem 15.7 (a′): the explicit `D` satisfies the adjacent symmetrizing
    relation** `dᵢ² a_{ij} = dⱼ² a_{ji}` on every adjacent pair, hence (with
    `symmetrized_isSymmetric`) symmetrizes `A`.

    The sub-diagonal is automatically nonzero under `PosRatio`
    (`sub_ne_zero_of_posRatio`), so no extra irreducibility hypothesis is
    needed here.  Core telescoping step: `D_{i+1}² = Dᵢ² · (a_{i,i+1}/a_{i+1,i})`. -/
lemma symmetrizerDiag_symmetrizes {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hpos : PosRatio A) :
    ∀ i j : Fin n, (i.val + 1 = j.val ∨ j.val + 1 = i.val) →
      symmetrizerDiag A i * symmetrizerDiag A i * A i j =
      symmetrizerDiag A j * symmetrizerDiag A j * A j i := by
  -- Core: for j = i+1 (so j.val = i.val+1), the relation holds.
  have core : ∀ (i j : Fin n), i.val + 1 = j.val →
      symmetrizerDiag A i * symmetrizerDiag A i * A i j =
      symmetrizerDiag A j * symmetrizerDiag A j * A j i := by
    intro i j hij
    have hjn : i.val + 1 < n := by have := j.isLt; omega
    -- Rewrite j as ⟨i.val+1, hjn⟩.
    have hjeq : j = ⟨i.val + 1, hjn⟩ := Fin.ext hij.symm
    subst hjeq
    -- D_j = symmDiagRaw A (i.val+1) = symmDiagRaw A i.val * sqrtRatioStep A i.val
    have hDj : symmetrizerDiag A ⟨i.val + 1, hjn⟩
        = symmetrizerDiag A i * sqrtRatioStep A i.val := by
      simp only [symmetrizerDiag, symmDiagRaw]
    -- The step value squared = the ratio (ratio ≥ 0).
    have hstepDef : sqrtRatioStep A i.val
        = Real.sqrt (A i ⟨i.val + 1, hjn⟩ / A ⟨i.val + 1, hjn⟩ i) := by
      unfold sqrtRatioStep
      rw [dif_pos hjn]
    have hratio_nn : 0 ≤ A i ⟨i.val + 1, hjn⟩ / A ⟨i.val + 1, hjn⟩ i :=
      le_of_lt (by simpa using hpos i hjn)
    have hstepSq : sqrtRatioStep A i.val * sqrtRatioStep A i.val
        = A i ⟨i.val + 1, hjn⟩ / A ⟨i.val + 1, hjn⟩ i := by
      rw [hstepDef]; exact Real.mul_self_sqrt hratio_nn
    have hAsub : A ⟨i.val + 1, hjn⟩ i ≠ 0 := sub_ne_zero_of_posRatio A hpos i hjn
    -- Now assemble.
    rw [hDj]
    have hgoal :
        symmetrizerDiag A i * symmetrizerDiag A i * A i ⟨i.val + 1, hjn⟩ =
        (symmetrizerDiag A i * sqrtRatioStep A i.val) *
          (symmetrizerDiag A i * sqrtRatioStep A i.val) *
          A ⟨i.val + 1, hjn⟩ i := by
      have hexp :
          (symmetrizerDiag A i * sqrtRatioStep A i.val) *
            (symmetrizerDiag A i * sqrtRatioStep A i.val) =
          symmetrizerDiag A i * symmetrizerDiag A i *
            (A i ⟨i.val + 1, hjn⟩ / A ⟨i.val + 1, hjn⟩ i) := by
        rw [show (symmetrizerDiag A i * sqrtRatioStep A i.val) *
              (symmetrizerDiag A i * sqrtRatioStep A i.val) =
            symmetrizerDiag A i * symmetrizerDiag A i *
              (sqrtRatioStep A i.val * sqrtRatioStep A i.val) from by ring,
          hstepSq]
      rw [hexp]
      field_simp
    exact hgoal
  -- Now the two adjacency directions.
  intro i j hadj
  rcases hadj with h1 | h2
  · exact core i j h1
  · exact (core j i h2).symm

-- ============================================================
-- (a)  The diagonal symmetrizing similarity
-- ============================================================

/-- The similar matrix `B = D A D⁻¹` where `D = diag d` and `D⁻¹ = diag dinv`.
    Entry form: `B_{ij} = dᵢ · A_{ij} · dinvⱼ`. -/
noncomputable def diagConj (n : ℕ) (d dinv : Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  matMul n (matMul n (diagMatrix d) A) (diagMatrix dinv)

/-- Entrywise value of the conjugated matrix: `(D A D⁻¹)_{ij} = dᵢ A_{ij} dinvⱼ`. -/
lemma diagConj_apply (n : ℕ) (d dinv : Fin n → ℝ) (A : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    diagConj n d dinv A i j = d i * A i j * dinv j := by
  unfold diagConj
  rw [matMul_diagMatrix_right (matMul n (diagMatrix d) A) dinv i j]
  rw [matMul_diagMatrix_left d A i j]

/-- **Problem 15.7 (a): the symmetrizing similarity.**

    Let `A` be tridiagonal and let `D = diag d` be a nonzero diagonal
    (`dinv = 1/d`) whose diagonal satisfies the adjacent symmetrizing
    relation `d i ^2 * A i j = d j ^2 * A j i` on every pair of adjacent
    indices.  Then `B := D A D_inv` is symmetric.

    This is the honest content of the hint "symmetrize the matrix": the only
    non-trivial symmetry constraint is on the super/sub-diagonal pair, and
    that is exactly the stated relation.  For `|i - j| > 1` both entries
    vanish by tridiagonality; on the diagonal it is automatic. -/
theorem symmetrized_isSymmetric (n : ℕ)
    (A : Fin n → Fin n → ℝ) (d dinv : Fin n → ℝ)
    (hTri : IsTridiagonal n A)
    (hdinv : ∀ i : Fin n, dinv i = 1 / d i)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hSym : ∀ i j : Fin n, (i.val + 1 = j.val ∨ j.val + 1 = i.val) →
      d i * d i * A i j = d j * d j * A j i) :
    IsSymmetricFiniteMatrix (diagConj n d dinv A) := by
  intro i j
  rw [diagConj_apply, diagConj_apply, hdinv j, hdinv i]
  -- Goal: d i * A i j * (1/d j) = d j * A j i * (1/d i)
  have hdi : d i ≠ 0 := hd i
  have hdj : d j ≠ 0 := hd j
  rcases lt_trichotomy (i.val + 1) j.val with hlt | heq | hgt
  · -- j.val > i.val + 1 : both entries zero by tridiagonality
    have h1 : A i j = 0 := hTri i j (Or.inl hlt)
    have h2 : A j i = 0 := hTri j i (Or.inr hlt)
    rw [h1, h2]; ring
  · -- j.val = i.val + 1 : adjacent
    have hrel : d i * d i * A i j = d j * d j * A j i :=
      hSym i j (Or.inl heq)
    field_simp
    linear_combination hrel
  · rcases lt_trichotomy (j.val + 1) i.val with hlt2 | heq2 | hgt2
    · -- i.val > j.val + 1 : both entries zero
      have h1 : A i j = 0 := hTri i j (Or.inr hlt2)
      have h2 : A j i = 0 := hTri j i (Or.inl hlt2)
      rw [h1, h2]; ring
    · -- i.val = j.val + 1 : adjacent
      have hrel : d i * d i * A i j = d j * d j * A j i :=
        hSym i j (Or.inr heq2)
      field_simp
      linear_combination hrel
    · -- i.val + 1 > j.val and j.val + 1 > i.val ⟹ i = j
      have hij : i.val = j.val := by omega
      have : i = j := Fin.ext hij
      subst this; ring

/-- **Problem 15.7 (a): existence of the symmetrizing similarity.**

    For an irreducible tridiagonal `A` with positive super/sub-diagonal ratios
    (`PosRatio`), the *explicit* diagonal `D = symmetrizerDiag A` (with
    `D⁻¹ = 1/D`) is nonzero and makes `B = D A D⁻¹` symmetric.  This packages
    (a′) with `symmetrized_isSymmetric` into the constructive statement the
    problem's hint calls for. -/
theorem symmetrizerDiag_isSymmetric (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hTri : IsTridiagonal n A)
    (hpos : PosRatio A) :
    IsSymmetricFiniteMatrix
      (diagConj n (symmetrizerDiag A) (fun i => 1 / symmetrizerDiag A i) A) :=
  symmetrized_isSymmetric n A (symmetrizerDiag A)
    (fun i => 1 / symmetrizerDiag A i) hTri
    (fun _ => rfl)
    (symmetrizerDiag_ne_zero A hpos)
    (symmetrizerDiag_symmetrizes A hpos)

-- ============================================================
-- (b)  The inverse of the symmetrized matrix is symmetric
-- ============================================================

/-- The conjugate of a right inverse is a right inverse of the conjugate:
    if `A A_inv = I` and `D⁻¹ D = I` then `(D A D⁻¹)(D A_inv D⁻¹) = I`.

    Entry computation:
    `∑ₖ (dᵢ A_{ik} dinvₖ)(dₖ A⁻¹_{kj} dinvⱼ) = dᵢ dinvⱼ ∑ₖ A_{ik} A⁻¹_{kj}`
    using `dinvₖ dₖ = 1`, and `∑ₖ A_{ik} A⁻¹_{kj} = δ_{ij}`. -/
theorem diagConj_isRightInverse (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (d dinv : Fin n → ℝ)
    (hdd : ∀ k : Fin n, dinv k * d k = 1)
    (hddi : ∀ i : Fin n, d i * dinv i = 1)
    (hAinv : IsRightInverse n A A_inv) :
    IsRightInverse n (diagConj n d dinv A) (diagConj n d dinv A_inv) := by
  intro i j
  have hstep : ∀ k : Fin n,
      diagConj n d dinv A i k * diagConj n d dinv A_inv k j
        = (d i * dinv j) * (A i k * A_inv k j) := by
    intro k
    rw [diagConj_apply, diagConj_apply]
    have hk : dinv k * d k = 1 := hdd k
    -- (d i * A i k * dinv k) * (d k * A_inv k j * dinv j)
    --   = (d i * dinv j) * (A i k * A_inv k j)  using dinv k * d k = 1
    linear_combination (d i * A i k * A_inv k j * dinv j) * hk
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum]
  have hI : (∑ k : Fin n, A i k * A_inv k j) = if i = j then 1 else 0 := hAinv i j
  rw [hI]
  by_cases hij : i = j
  · subst hij; simp [hddi i]
  · simp [hij]

/-- **Problem 15.7 (b): symmetry of the symmetrized inverse.**

    If `A_inv` is the (two-sided) inverse of `A` and `B := D A D⁻¹` is
    symmetric, then the conjugated inverse `M := D A_inv D⁻¹` is symmetric.

    Proof (elementary, no `Matrix.inv`): `M` is a right inverse of `B`
    (`diagConj_isRightInverse`), hence also a left inverse (Dedekind
    finiteness).  The transpose `Mᵀ` is then *also* a right inverse of `B`
    (using `B = Bᵀ`), and right inverses of a two-sided-invertible matrix are
    unique, so `Mᵀ = M`. -/
theorem symmetrized_inv_symmetric (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (d dinv : Fin n → ℝ)
    (hdd : ∀ k : Fin n, dinv k * d k = 1)
    (hddi : ∀ i : Fin n, d i * dinv i = 1)
    (hAinv : IsRightInverse n A A_inv)
    (hBsym : IsSymmetricFiniteMatrix (diagConj n d dinv A)) :
    IsSymmetricFiniteMatrix (diagConj n d dinv A_inv) := by
  set B := diagConj n d dinv A with hB
  set M := diagConj n d dinv A_inv with hM
  -- (i) M is a right inverse of B, as matMul = idMatrix.
  have hRight : matMul n B M = idMatrix n := by
    funext i j
    have := diagConj_isRightInverse n A A_inv d dinv hdd hddi hAinv i j
    simpa [matMul, idMatrix] using this
  -- (ii) M is a left inverse of B (Dedekind finiteness).
  have hLeft : matMul n M B = idMatrix n := by
    have hpred : IsRightInverse n B M := by
      intro i j
      have := congrFun (congrFun hRight i) j
      simpa [matMul, idMatrix] using this
    have hleftpred : IsLeftInverse n B M :=
      isLeftInverse_of_isRightInverse (B : Matrix (Fin n) (Fin n) ℝ)
        (M : Matrix (Fin n) (Fin n) ℝ) hpred
    funext i j
    have := hleftpred i j
    simpa [matMul, idMatrix] using this
  -- (iii) The transpose Mt of M is also a right inverse of B (uses B symmetric).
  set Mt : Fin n → Fin n → ℝ := fun i j => M j i with hMt
  have hRightT : matMul n B Mt = idMatrix n := by
    funext i j
    show (∑ k : Fin n, B i k * M j k) = idMatrix n i j
    have hsymrw : ∀ k : Fin n, B i k * M j k = M j k * B k i := by
      intro k; rw [hBsym i k]; ring
    rw [Finset.sum_congr rfl (fun k _ => hsymrw k)]
    have := congrFun (congrFun hLeft j) i
    simp only [matMul] at this
    rw [this]
    unfold idMatrix
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h : j = i => hij h.symm)]
  -- (iv) Uniqueness of right inverse: Mt = M.
  have hEq : Mt = M := by
    calc Mt = matMul n (idMatrix n) Mt := (matMul_id_left n Mt).symm
      _ = matMul n (matMul n M B) Mt := by rw [hLeft]
      _ = matMul n M (matMul n B Mt) := matMul_assoc n M B Mt
      _ = matMul n M (idMatrix n) := by rw [hRightT]
      _ = M := matMul_id_right n M
  -- Conclude symmetry of M.
  intro i j
  have := congrFun (congrFun hEq i) j
  simpa [hMt] using this.symm

/-- **Problem 15.7 (b), collapse identity.**

    From symmetry of `M = D A⁻¹ D⁻¹` we read off the *scaling relation*
    `dᵢ² (A⁻¹)_{ij} = dⱼ² (A⁻¹)_{ji}`.  This is the algebraic identity that
    makes the lower-triangle rank-1 factors redundant. -/
theorem inv_scaling_relation (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (d dinv : Fin n → ℝ)
    (hdinv : ∀ i : Fin n, dinv i = 1 / d i)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hdd : ∀ k : Fin n, dinv k * d k = 1)
    (hddi : ∀ i : Fin n, d i * dinv i = 1)
    (hAinv : IsRightInverse n A A_inv)
    (hBsym : IsSymmetricFiniteMatrix (diagConj n d dinv A)) :
    ∀ i j : Fin n, d i * d i * A_inv i j = d j * d j * A_inv j i := by
  have hMsym : IsSymmetricFiniteMatrix (diagConj n d dinv A_inv) :=
    symmetrized_inv_symmetric n A A_inv d dinv hdd hddi hAinv hBsym
  intro i j
  have hij := hMsym i j
  rw [diagConj_apply, diagConj_apply, hdinv j, hdinv i] at hij
  -- hij : d i * A_inv i j * (1 / d j) = d j * A_inv j i * (1 / d i)
  have hdi : d i ≠ 0 := hd i
  have hdj : d j ≠ 0 := hd j
  field_simp at hij
  linear_combination hij

-- ============================================================
-- (c)  Factor collapse: the 3n − 2 representation
-- ============================================================

/-- **Problem 15.7 (c): factor collapse from Ikebe's upper factors alone.**

    Assume the Ikebe hypotheses for `A` (LU structure + explicit bidiagonal
    inverse product formulas), so `A⁻¹` has the rank-1 upper structure
    `(A⁻¹)_{ij} = xᵢ yⱼ` for `i ≤ j`.  Assume in addition that a nonzero
    diagonal `D` symmetrizes `A` (so `B = D A D⁻¹` is symmetric) and that
    `A_inv` is a genuine right inverse of `A`.

    Then, setting the TWO vectors
      `u i = dᵢ · xᵢ`,   `v i = yᵢ / dᵢ`,
    the whole inverse is represented, *for all i and j*, by
      `(A⁻¹)_{ij} = (dⱼ / dᵢ) · u (min i j) · v (max i j)`.

    The lower-triangle rank-1 factors `p, q` of Theorem 15.9 have been
    ELIMINATED: only `x, y` (via `u, v`) and the diagonal `D` remain.

    Parameter count (documented residual — see module notes):
    `u, v` carry `2n` numbers with one common scaling redundancy
    (`(u,v) ↦ (λu, v/λ)` is invariant on the off-diagonal), i.e. `2n − 1`
    free; the symmetrizer `D` is fixed up to an overall scale, contributing
    its `n − 1` independent ratios; total `(2n − 1) + (n − 1) = 3n − 2`,
    matching the `3n − 2` parameters of `A` itself. -/
theorem ikebe_symmetrized_representation (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (L U L_inv U_inv : Fin n → Fin n → ℝ)
    (d dinv : Fin n → ℝ)
    -- symmetrizer data
    (hdinv : ∀ i : Fin n, dinv i = 1 / d i)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hdd : ∀ k : Fin n, dinv k * d k = 1)
    (hddi : ∀ i : Fin n, d i * dinv i = 1)
    (hAinvR : IsRightInverse n A A_inv)
    (hBsym : IsSymmetricFiniteMatrix (diagConj n d dinv A))
    -- Ikebe (Theorem 15.9) data for A
    (hStruct : IsTridiagLU n L U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (hU_inv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0)
    (hL_inv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0)
    (hU_inv_prod : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = cumulProdUpper (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) k /
        (cumulProdUpper (fun m => U m m)
          (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i *
          U k k))
    (hL_inv_prod : ∀ k j : Fin n, j.val ≤ k.val →
      L_inv k j = cumulProdLower
        (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) k /
        cumulProdLower
          (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) j) :
    ∃ (u v : Fin n → ℝ),
      ∀ i j : Fin n,
        A_inv i j = (d j / d i) * u (min i j) * v (max i j) := by
  -- Ikebe's rank-1 structure for A (we only use the upper factors x, y).
  obtain ⟨x, y, p, q, hUpper, _hLower⟩ :=
    ikebe_tridiag_inv_structure n A_inv L U L_inv U_inv
      hStruct hU_diag hA_inv_eq hU_inv_ut hL_inv_lt hU_inv_prod hL_inv_prod
  -- The scaling relation dᵢ² A⁻¹_{ij} = dⱼ² A⁻¹_{ji}.
  have hScale : ∀ i j : Fin n, d i * d i * A_inv i j = d j * d j * A_inv j i :=
    inv_scaling_relation n A A_inv d dinv hdinv hd hdd hddi hAinvR hBsym
  refine ⟨fun i => d i * x i, fun i => y i / d i, ?_⟩
  intro i j
  have hdi : d i ≠ 0 := hd i
  have hdj : d j ≠ 0 := hd j
  rcases le_total i.val j.val with hle | hle
  · -- i ≤ j : min = i, max = j; use upper A⁻¹_{ij} = xᵢ yⱼ
    have hmin : min i j = i := min_eq_left (by exact hle)
    have hmax : max i j = j := max_eq_right (by exact hle)
    rw [hmin, hmax, hUpper i j hle]
    field_simp
  · -- j ≤ i : min = j, max = i; use scaling + upper A⁻¹_{ji} = xⱼ yᵢ
    have hmin : min i j = j := min_eq_right (by exact hle)
    have hmax : max i j = i := max_eq_left (by exact hle)
    rw [hmin, hmax]
    -- A⁻¹_{ij} = (dⱼ²/dᵢ²) A⁻¹_{ji} = (dⱼ²/dᵢ²) xⱼ yᵢ
    have hji : A_inv j i = x j * y i := hUpper j i hle
    have hrel : d i * d i * A_inv i j = d j * d j * (x j * y i) := by
      rw [hScale i j, hji]
    -- solve for A_inv i j and match RHS
    have hAij : A_inv i j = d j * d j * (x j * y i) / (d i * d i) := by
      field_simp at hrel ⊢
      linarith [hrel]
    rw [hAij]
    field_simp

/-- **Problem 15.7: end-to-end `3n − 2` representation (constructive `D`).**

    Fully self-contained form: for a nonsingular, tridiagonal, irreducible `A`
    (irreducibility supplied as `PosRatio`: adjacent super/sub-diagonal ratios
    are positive — the honest condition under which a *real* symmetrizer
    exists; this already forces the sub-diagonal to be nonzero), with `A_inv` a
    right inverse and the Ikebe LU data, the inverse has the representation

      `(A⁻¹)_{ij} = (Dⱼ / Dᵢ) · u (min i j) · v (max i j)`   for all `i, j`,

    where `D = symmetrizerDiag A` is the EXPLICIT symmetrizer built from the
    entry ratios, and `u i = Dᵢ xᵢ`, `v i = yᵢ / Dᵢ` come from Ikebe's upper
    factors `x, y`.  Only `x, y` and `D` appear — the `4n`-parameter Theorem
    15.9 form (`x, y, p, q`) collapses to the `3n − 2`-parameter form. -/
theorem ikebe_symmetrized_representation_constructive (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (L U L_inv U_inv : Fin n → Fin n → ℝ)
    (hTri : IsTridiagonal n A)
    (hpos : PosRatio A)
    (hAinvR : IsRightInverse n A A_inv)
    (hStruct : IsTridiagLU n L U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (hU_inv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0)
    (hL_inv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0)
    (hU_inv_prod : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = cumulProdUpper (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) k /
        (cumulProdUpper (fun m => U m m)
          (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i *
          U k k))
    (hL_inv_prod : ∀ k j : Fin n, j.val ≤ k.val →
      L_inv k j = cumulProdLower
        (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) k /
        cumulProdLower
          (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) j) :
    ∃ (u v : Fin n → ℝ),
      ∀ i j : Fin n,
        A_inv i j =
          (symmetrizerDiag A j / symmetrizerDiag A i) *
            u (min i j) * v (max i j) := by
  have hd : ∀ i : Fin n, symmetrizerDiag A i ≠ 0 := symmetrizerDiag_ne_zero A hpos
  refine ikebe_symmetrized_representation n A A_inv L U L_inv U_inv
    (symmetrizerDiag A) (fun i => 1 / symmetrizerDiag A i)
    (fun _ => rfl) hd
    (fun k => by
      show 1 / symmetrizerDiag A k * symmetrizerDiag A k = 1
      rw [one_div]; exact inv_mul_cancel₀ (hd k))
    (fun k => by
      show symmetrizerDiag A k * (1 / symmetrizerDiag A k) = 1
      rw [one_div]; exact mul_inv_cancel₀ (hd k))
    hAinvR
    (symmetrizerDiag_isSymmetric n A hTri hpos)
    hStruct hU_diag hA_inv_eq hU_inv_ut hL_inv_lt hU_inv_prod hL_inv_prod

end LeanFpAnalysis.FP.Ch15
