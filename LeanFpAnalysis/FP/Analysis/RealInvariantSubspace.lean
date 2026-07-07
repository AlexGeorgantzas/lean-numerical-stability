/-
Analysis/RealInvariantSubspace.lean

The **ℂ→ℝ real invariant-subspace descent**.  Higham, *Accuracy and Stability
of Numerical Algorithms*, 2nd ed., §16.2 (real Schur decomposition (16.4)) and
§17.4 (Householder `[106, Lem 6.9]`, the ℂ→ℝ descent behind semiconvergent
existence).

This module supplies the single primitive that the obstruction blocks of
`Analysis/RealSchurTriangulation.lean` and `Analysis/SemiconvergentExistenceGaps.lean`
named as missing from Mathlib (v4.29.0): a **real invariant subspace of
dimension `1` or `2`** for an arbitrary real square matrix, obtained by
complexifying, taking a complex eigenvector `v`, and forming the real span of
`Re v` and `Im v`.

Concretely, for `A : Matrix (Fin n) (Fin n) ℝ` with `0 < n`:

  `∃ (W : Submodule ℝ (Fin n → ℝ)),
      0 < finrank ℝ W ∧ finrank ℝ W ≤ 2 ∧ ∀ w ∈ W, A.mulVecLin w ∈ W`.

The `2`-dimensional real span of `Re v, Im v` for a genuine complex-conjugate
eigenvalue pair is exactly the invariant subspace behind the `2×2` blocks of the
real quasi-triangular Schur form (16.4); when the eigenvalue is real, `Re v` is a
real eigenvector and the subspace is `1`-dimensional.  This is the "peel-1-or-2"
deflation primitive of the real Schur / real-Jordan reduction.

Mathlib (v4.29.0) has no real Schur form and no ready-made "invariant subspace of
dimension `≤ 2`" primitive; it does have `Module.End.exists_eigenvalue` over an
algebraically closed field and the entry-wise real/imaginary part maps of `ℂ`.
This file assembles the descent from those, honestly and unconditionally (no
extra hypothesis beyond the honest domain `0 < n`, which is genuinely necessary:
the empty matrix has no nonzero subspace at all).

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., §16.2, equation (16.4) (real Schur decomposition); §17.4, Householder
`[106, Lem 6.9]`.  The real invariant-subspace fact is classical, see e.g.
Horn & Johnson, *Matrix Analysis*, §2.3 / Golub & Van Loan, *Matrix
Computations*, §7.4.

Main result:
* `LeanFpAnalysis.FP.exists_real_invariant_subspace_dim_le_two` — every nonempty
  real matrix has a real invariant subspace of dimension `1` or `2`.
-/

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped BigOperators Matrix
open Module

namespace LeanFpAnalysis.FP

namespace RealInvariantSubspaceAux

/-! ### Complexification and the real/imaginary parts of a complex eigenvector -/

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- The complexification `Aᶜ` of a real matrix `A`: apply the coercion `ℝ → ℂ`
    to every entry.  (This is `A.map (algebraMap ℝ ℂ)` up to the coercion.)  First
    step of the ℂ→ℝ descent behind the real Schur decomposition of Higham,
    *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §16.2, eq (16.4);
    §17.4, Householder `[106, Lem 6.9]`. -/
def cplx (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map (fun r : ℝ => (r : ℂ))

/-- Entry of the complexification behind Higham §16.2 (16.4). -/
@[simp] lemma cplx_apply (i j : Fin n) : cplx A i j = ((A i j : ℝ) : ℂ) := rfl

/-- The key entry identity: for a complex vector `v`, the `i`-th coordinate of
    `Aᶜ *ᵥ v` splits into the real matrix acting on the real and imaginary parts,
    `(Aᶜ *ᵥ v) i = ↑((A *ᵥ Re v) i) + ↑((A *ᵥ Im v) i) * I`.  The algebraic core of
    the ℂ→ℝ descent for Higham §16.2 (16.4) / §17.4 `[106, Lem 6.9]`. -/
lemma cplx_mulVec_apply (v : Fin n → ℂ) (i : Fin n) :
    (cplx A *ᵥ v) i
      = (((A *ᵥ (fun k => (v k).re)) i : ℝ) : ℂ)
        + (((A *ᵥ (fun k => (v k).im)) i : ℝ) : ℂ) * Complex.I := by
  simp only [Matrix.mulVec, dotProduct, cplx_apply]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hv : v j = ((v j).re : ℂ) + ((v j).im : ℂ) * Complex.I := (Complex.re_add_im (v j)).symm
  conv_lhs => rw [hv]
  ring

/-- Taking real parts of the eigenvector equation:
    if `Aᶜ *ᵥ v = μ • v` then `A *ᵥ Re v = μ.re • Re v - μ.im • Im v`.  This is the
    real part of the `2×2` block relation of Higham §16.2 (16.4). -/
lemma real_part_eqn {v : Fin n → ℂ} {μ : ℂ} (hv : cplx A *ᵥ v = μ • v) :
    A *ᵥ (fun k => (v k).re)
      = μ.re • (fun k => (v k).re) - μ.im • (fun k => (v k).im) := by
  funext i
  have hi : (cplx A *ᵥ v) i = μ * v i := by
    rw [hv]; simp [Pi.smul_apply, smul_eq_mul]
  rw [cplx_mulVec_apply] at hi
  -- take real parts of both sides
  have hre := congrArg Complex.re hi
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero] at hre
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hre]

/-- Taking imaginary parts of the eigenvector equation:
    if `Aᶜ *ᵥ v = μ • v` then `A *ᵥ Im v = μ.im • Re v + μ.re • Im v`.  This is the
    imaginary part of the `2×2` block relation of Higham §16.2 (16.4). -/
lemma imag_part_eqn {v : Fin n → ℂ} {μ : ℂ} (hv : cplx A *ᵥ v = μ • v) :
    A *ᵥ (fun k => (v k).im)
      = μ.im • (fun k => (v k).re) + μ.re • (fun k => (v k).im) := by
  funext i
  have hi : (cplx A *ᵥ v) i = μ * v i := by
    rw [hv]; simp [Pi.smul_apply, smul_eq_mul]
  rw [cplx_mulVec_apply] at hi
  have him := congrArg Complex.im hi
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero] at him
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [him]
  ring

/-- The complexification acts on a *real* (coerced) vector exactly as the real
    matrix does: `Aᶜ *ᵥ (↑u) = ↑(A *ᵥ u)`.  Auxiliary to the ℂ→ℝ descent of
    Higham §16.2 (16.4) / §17.4 `[106, Lem 6.9]`. -/
lemma cplx_mulVec_ofReal (u : Fin n → ℝ) :
    cplx A *ᵥ (fun k => ((u k : ℝ) : ℂ)) = fun i => (((A *ᵥ u) i : ℝ) : ℂ) := by
  funext i
  rw [cplx_mulVec_apply]
  have hre : (fun k => (((u k : ℝ) : ℂ)).re) = u := by funext k; simp
  have him : (fun k => (((u k : ℝ) : ℂ)).im) = (0 : Fin n → ℝ) := by funext k; simp
  rw [hre, him]
  simp

/-- **A real vector cannot be a complex eigenvector for a non-real eigenvalue.**
    If `u : Fin n → ℝ` is nonzero and `Aᶜ *ᵥ (↑u) = μ • (↑u)`, then `μ.im = 0`.
    (Componentwise, `↑((A *ᵥ u) i) = μ * ↑(u i)` is real, forcing `μ.im * u i = 0`;
    some `u i ≠ 0` gives `μ.im = 0`.)  This is why a genuine complex-conjugate pair
    of Higham §16.2 (16.4) yields a `2`-dimensional (not `1`-dimensional) block. -/
lemma im_eq_zero_of_real_eigenvector {u : Fin n → ℝ} {μ : ℂ} (hune : u ≠ 0)
    (hev : cplx A *ᵥ (fun k => ((u k : ℝ) : ℂ)) = μ • (fun k => ((u k : ℝ) : ℂ))) :
    μ.im = 0 := by
  rw [cplx_mulVec_ofReal] at hev
  -- some coordinate of `u` is nonzero
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push_neg at h; exact hune (funext h)
  have hcoord : (((A *ᵥ u) i : ℝ) : ℂ) = μ * ((u i : ℝ) : ℂ) := by
    have := congrFun hev i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have him := congrArg Complex.im hcoord
  simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add] at him
  -- him : 0 = μ.im * u i
  have : μ.im * u i = 0 := him.symm
  rcases mul_eq_zero.1 this with h1 | h2
  · exact h1
  · exact absurd h2 hi

/-- **Linear independence of `Re v`, `Im v` for a genuine complex-conjugate pair.**
    If `v` is a complex eigenvector of `Aᶜ` with eigenvalue `μ` of nonzero
    imaginary part, then `Re v` and `Im v` are `ℝ`-linearly independent — so their
    real span is genuinely `2`-dimensional (the `2×2` block of the real Schur form
    (16.4)). -/
lemma reIm_linearIndependent_of_im_ne {v : Fin n → ℂ} {μ : ℂ}
    (hv : cplx A *ᵥ v = μ • v) (hvne : v ≠ 0) (hμ : μ.im ≠ 0) :
    LinearIndependent ℝ ![(fun k => (v k).re), (fun k => (v k).im)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  -- the real vector `u = a·Im v − b·Re v`
  set u : Fin n → ℝ := a • (fun k => (v k).im) - b • (fun k => (v k).re) with hu
  -- the complex vector `c • v` with `c = a − b·I` equals `I • ↑u` coordinatewise
  set c : ℂ := (a : ℂ) - (b : ℂ) * Complex.I with hc
  have hcoord : c • v = (fun k => (Complex.I : ℂ) * ((u k : ℝ) : ℂ)) := by
    funext k
    have habk : a * (v k).re + b * (v k).im = 0 := by
      have hk := congrFun hab k
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hk
    simp only [hc, hu, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, Complex.ofReal_sub, Complex.ofReal_mul]
      nlinarith [habk]
    · simp only [Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im, mul_zero, mul_one,
        zero_mul, sub_zero, zero_sub, zero_add, add_zero, Complex.ofReal_sub, Complex.ofReal_mul]
      ring
  -- transport the eigenvector equation along `c • v`
  have hcv : cplx A *ᵥ (c • v) = μ • (c • v) := by
    rw [Matrix.mulVec_smul, hv, smul_comm]
  -- rewrite as an eigenvector equation for the *real* vector `u`, up to the `I` factor
  have hIu : cplx A *ᵥ (fun k => (Complex.I : ℂ) * ((u k : ℝ) : ℂ))
      = μ • (fun k => (Complex.I : ℂ) * ((u k : ℝ) : ℂ)) := by
    rw [← hcoord]; exact hcv
  have hIsmul : (fun k => (Complex.I : ℂ) * ((u k : ℝ) : ℂ))
      = Complex.I • (fun k => ((u k : ℝ) : ℂ)) := by
    funext k; simp [Pi.smul_apply, smul_eq_mul]
  rw [hIsmul, Matrix.mulVec_smul, smul_comm μ Complex.I] at hIu
  have hIne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hu_ev : cplx A *ᵥ (fun k => ((u k : ℝ) : ℂ)) = μ • (fun k => ((u k : ℝ) : ℂ)) :=
    smul_right_injective (Fin n → ℂ) hIne hIu
  -- if `u ≠ 0` then `μ.im = 0`, contradicting `hμ`; hence `u = 0`
  have hu0 : u = 0 := by
    by_contra hune
    exact hμ (im_eq_zero_of_real_eigenvector A hune hu_ev)
  -- then `c • v = 0`, and `v ≠ 0` forces `c = 0`, i.e. `a = 0` and `b = 0`
  have hcv0 : c • v = 0 := by
    rw [hcoord, hu0]; funext k; simp
  have hc0 : c = 0 := by
    rcases smul_eq_zero.1 hcv0 with h | h
    · exact h
    · exact absurd h hvne
  have hre : c.re = 0 := by rw [hc0]; simp
  have him : c.im = 0 := by rw [hc0]; simp
  rw [hc] at hre him
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero] at hre
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one] at him
  constructor
  · linarith [hre]
  · linarith [him]

end RealInvariantSubspaceAux

/-! ### The main theorem -/

/-- A real matrix has no nonzero real eigenline.  This source-side predicate is
    intentionally independent of the Sylvester development, so the real
    quasi-Schur construction can export irreducible `2 x 2` block data without
    creating an import cycle. -/
def MatrixNoRealEigenline {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 -> ¬ ∃ ν : ℝ, A *ᵥ x = ν • x

/-- The canonical real `2 x 2` rotation-scaling block
    `[[alpha,beta],[-beta,alpha]]` with `beta != 0` has no real eigenline. -/
theorem matrixNoRealEigenline_fin_two_of_rotation_scaling_entries
    (B : Matrix (Fin 2) (Fin 2) ℝ) (α β : ℝ)
    (h00 : B 0 0 = α)
    (h01 : B 0 1 = β)
    (h10 : B 1 0 = -β)
    (h11 : B 1 1 = α)
    (hβ : β ≠ 0) :
    MatrixNoRealEigenline B := by
  intro x hx hEig
  rcases hEig with ⟨ν, hν⟩
  have h0 := congrFun hν (0 : Fin 2)
  have h1 := congrFun hν (1 : Fin 2)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h10, h11] at h0 h1
  have hsumsq : β * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
    have h0mul : (α * x 0 + β * x 1) * x 1 = (ν * x 0) * x 1 := by
      rw [h0]
    have h1mul : (-(β * x 0) + α * x 1) * x 0 = (ν * x 1) * x 0 := by
      rw [h1]
    nlinarith [h0mul, h1mul]
  have hsq : x 0 ^ 2 + x 1 ^ 2 = 0 := (mul_eq_zero.mp hsumsq).resolve_left hβ
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hsq]
  have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), hsq]
  apply hx
  funext k
  fin_cases k <;> simp [hx0, hx1]

open RealInvariantSubspaceAux in
/-- **ℂ→ℝ real invariant-subspace descent (dimension `1` or `2`).**

    Every nonempty real square matrix `A` has a real invariant subspace `W` of
    dimension `1` or `2`: `0 < finrank ℝ W ≤ 2` and `A.mulVecLin` maps `W` into
    itself.

    This is the real Schur decomposition of Higham §16.2 (16.4) in
    infinitesimal form — the "peel-1-or-2" deflation primitive.  Complexify `A`;
    the algebraically closed field `ℂ` provides an eigenvector `v` with
    eigenvalue `μ` (`Module.End.exists_eigenvalue`).  If `μ` is real, `Re v` is a
    real eigenvector and `W` is `1`-dimensional; in general the real span
    `W = span_ℝ {Re v, Im v}` is `A`-invariant because
    `A (Re v) = μ.re • Re v - μ.im • Im v` and
    `A (Im v) = μ.im • Re v + μ.re • Im v`, and it is nonzero because `v ≠ 0`
    forces `Re v ≠ 0` or `Im v ≠ 0`.  The dimension is `≤ 2` since `W` is spanned
    by the two vectors `Re v, Im v`.  Unconditional (the hypothesis `0 < n` is
    necessary: the empty matrix has no nonzero subspace). -/
theorem exists_real_invariant_subspace_dim_le_two {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      0 < finrank ℝ W ∧ finrank ℝ W ≤ 2 ∧
        ∀ w ∈ W, A.mulVecLin w ∈ W := by
  -- nonemptiness / nontriviality of the complexified space
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → ℂ) := Function.nontrivial
  -- complex eigenvalue / eigenvector
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin (cplx A))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvne : v ≠ 0 := hv.2
  have hveqn : cplx A *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    simpa [Matrix.mulVecLin_apply] using this
  -- the real and imaginary parts of `v`
  set x : Fin n → ℝ := fun k => (v k).re with hx
  set y : Fin n → ℝ := fun k => (v k).im with hy
  -- the invariance equations
  have hAx : A *ᵥ x = μ.re • x - μ.im • y := real_part_eqn A hveqn
  have hAy : A *ᵥ y = μ.im • x + μ.re • y := imag_part_eqn A hveqn
  -- the candidate subspace
  refine ⟨Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)), ?_, ?_, ?_⟩
  · -- positivity of the dimension: `W ≠ ⊥`
    rw [Module.finrank_pos_iff (R := ℝ)]
    rw [Submodule.nontrivial_iff_ne_bot]
    -- one of x, y is nonzero
    have hxy : x ≠ 0 ∨ y ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨hx0, hy0⟩ := h
      apply hvne
      funext k
      have hxk : (v k).re = 0 := congrFun hx0 k
      have hyk : (v k).im = 0 := congrFun hy0 k
      apply Complex.ext <;> simp [hxk, hyk]
    intro hbot
    rcases hxy with hxne | hyne
    · exact hxne (by
        have : x ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) :=
          Submodule.subset_span (by simp)
        rw [hbot] at this
        simpa using this)
    · exact hyne (by
        have : y ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) :=
          Submodule.subset_span (by simp)
        rw [hbot] at this
        simpa using this)
  · -- dimension `≤ 2`
    have hcard : (Set.range ![x, y]).finrank ℝ ≤ Fintype.card (Fin 2) :=
      finrank_range_le_card ![x, y]
    have hrange : (Set.range ![x, y]) = ({x, y} : Set (Fin n → ℝ)) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hrange] at hcard
    simpa [Set.finrank] using hcard
  · -- invariance
    intro w hw
    -- reduce to generators via `map_span_le`
    have hmap : Submodule.map A.mulVecLin (Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)))
        ≤ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
      rw [Submodule.map_span_le]
      intro m hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · -- A.mulVecLin x = μ.re • x - μ.im • y ∈ span {x,y}
        rw [Matrix.mulVecLin_apply, hAx]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · -- A.mulVecLin y = μ.im • x + μ.re • y ∈ span {x,y}
        rw [Matrix.mulVecLin_apply, hAy]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    exact hmap (Submodule.mem_map_of_mem hw)

/-- **Invariance of a spanned pair.**  If `A *ᵥ x` and `A *ᵥ y` both lie in the
    real span of `{x, y}`, then `A.mulVecLin` maps the whole span into itself.
    The abstract closure step reused by the deflation dichotomy below; it packages
    the `A`-invariance of the `1×1`/`2×2` blocks of Higham §16.2 (16.4). -/
theorem mulVecLin_maps_span_pair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {x y : Fin n → ℝ}
    (hx : A *ᵥ x ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)))
    (hy : A *ᵥ y ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ))) :
    ∀ w ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)),
      A.mulVecLin w ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
  intro w hw
  have hmap : Submodule.map A.mulVecLin (Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)))
      ≤ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
    rw [Submodule.map_span_le]
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · rw [Matrix.mulVecLin_apply]; exact hx
    · rw [Matrix.mulVecLin_apply]; exact hy
  exact hmap (Submodule.mem_map_of_mem hw)

open RealInvariantSubspaceAux in
/-- **The real "peel-1-or-2" dichotomy (explicit form of the real Schur block
    structure (16.4)).**

    Every nonempty real square matrix `A` satisfies exactly one of:

    * (real eigenvalue) there is `μ : ℝ` and a nonzero real vector `x` with
      `A *ᵥ x = μ • x` — a `1`-dimensional real invariant subspace, the `1×1`
      block of (16.4); or

    * (complex-conjugate pair) there are `α β : ℝ` with `β ≠ 0` and two
      `ℝ`-linearly independent real vectors `x, y` with
      `A *ᵥ x = α • x − β • y` and `A *ᵥ y = β • x + α • y` — a genuinely
      `2`-dimensional real invariant subspace on which `A` acts by the real
      rotation-scaling block `[[α, β], [-β, α]]`, the `2×2` block of (16.4)
      (eigenvalues `α ± β i`).

    This is the explicit, deflation-ready content of the ℂ→ℝ descent: complexify,
    take a complex eigenvector `v = Re v + i·Im v` with eigenvalue `μ = α + βi`;
    if `β = 0` one of `Re v, Im v` is a real eigenvector, and if `β ≠ 0` then
    `Re v, Im v` are linearly independent (`reIm_linearIndependent_of_im_ne`) and
    span the invariant `2×2` block.  Unconditional (`0 < n` is necessary). -/
theorem real_peel_one_or_two {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ (μ : ℝ) (x : Fin n → ℝ), x ≠ 0 ∧ A *ᵥ x = μ • x)
      ∨ (∃ (α β : ℝ) (x y : Fin n → ℝ), β ≠ 0 ∧
          LinearIndependent ℝ ![x, y] ∧
          A *ᵥ x = α • x - β • y ∧ A *ᵥ y = β • x + α • y) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → ℂ) := Function.nontrivial
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin (cplx A))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hvne : v ≠ 0 := hv.2
  have hveqn : cplx A *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    simpa [Matrix.mulVecLin_apply] using this
  set x : Fin n → ℝ := fun k => (v k).re with hx
  set y : Fin n → ℝ := fun k => (v k).im with hy
  have hAx : A *ᵥ x = μ.re • x - μ.im • y := real_part_eqn A hveqn
  have hAy : A *ᵥ y = μ.im • x + μ.re • y := imag_part_eqn A hveqn
  -- at least one of x, y is nonzero
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨hx0, hy0⟩ := h
    apply hvne
    funext k
    have hxk : (v k).re = 0 := congrFun hx0 k
    have hyk : (v k).im = 0 := congrFun hy0 k
    apply Complex.ext <;> simp [hxk, hyk]
  by_cases hβ : μ.im = 0
  · -- real eigenvalue: one of x, y is a real eigenvector for μ.re
    left
    rcases hxy with hxne | hyne
    · refine ⟨μ.re, x, hxne, ?_⟩
      rw [hAx, hβ]; simp
    · refine ⟨μ.re, y, hyne, ?_⟩
      rw [hAy, hβ]; simp
  · -- genuine complex-conjugate pair
    right
    exact ⟨μ.re, μ.im, x, y, hβ, reIm_linearIndependent_of_im_ne A hveqn hvne hβ, hAx, hAy⟩

/-- A genuine real rotation-scaling invariant plane has no real eigenline
    inside that plane.  This packages the irreducibility content of the
    nonreal branch of `real_peel_one_or_two` before the Schur deflation step
    forgets the chosen basis. -/
theorem no_real_eigenvector_in_span_of_rotation_scaling {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (α β : ℝ) (x y : Fin n → ℝ)
    (hβ : β ≠ 0)
    (hind : LinearIndependent ℝ ![x, y])
    (hAx : A *ᵥ x = α • x - β • y)
    (hAy : A *ᵥ y = β • x + α • y) :
    ∀ a b : ℝ, (a • x + b • y : Fin n → ℝ) ≠ 0 ->
      ¬ ∃ ν : ℝ, A *ᵥ (a • x + b • y : Fin n → ℝ) =
        ν • (a • x + b • y : Fin n → ℝ) := by
  intro a b hab hEig
  rcases hEig with ⟨ν, hν⟩
  have hνlin :
      A.mulVecLin (a • x + b • y : Fin n → ℝ) =
        ν • (a • x + b • y : Fin n → ℝ) := by
    simpa [Matrix.mulVecLin_apply] using hν
  have hcoeff_eq :
      a • (α • x - β • y) + b • (β • x + α • y) =
        ν • (a • x + b • y : Fin n → ℝ) := by
    calc
      a • (α • x - β • y) + b • (β • x + α • y)
          = A.mulVecLin (a • x + b • y : Fin n → ℝ) := by
            simp [map_add, map_smul, hAx, hAy]
      _ = ν • (a • x + b • y : Fin n → ℝ) := hνlin
  have hzero :
      ((a * α + b * β - ν * a) • x +
        ((-a * β + b * α - ν * b) • y) : Fin n → ℝ) = 0 := by
    funext k
    have hk := congrFun hcoeff_eq k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    calc
      (a * α + b * β - ν * a) * x k + (-a * β + b * α - ν * b) * y k
          = a * (α * x k - β * y k) + b * (β * x k + α * y k) -
              ν * (a * x k + b * y k) := by
            ring
      _ = 0 := by
            rw [hk]
            ring
  rw [LinearIndependent.pair_iff] at hind
  have hcoeff := hind
    (a * α + b * β - ν * a)
    (-a * β + b * α - ν * b) hzero
  have ha_eq : a * α + b * β - ν * a = 0 := hcoeff.1
  have hb_eq : -a * β + b * α - ν * b = 0 := hcoeff.2
  have hsumsq : β * (a ^ 2 + b ^ 2) = 0 := by
    have h1 : (a * α + b * β - ν * a) * b = 0 := by
      rw [ha_eq]
      ring
    have h2 : (-a * β + b * α - ν * b) * a = 0 := by
      rw [hb_eq]
      ring
    nlinarith [h1, h2]
  have habsq : a ^ 2 + b ^ 2 = 0 := by
    exact (mul_eq_zero.mp hsumsq).resolve_left hβ
  have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, habsq]
  have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, habsq]
  apply hab
  simp [ha0, hb0]

/-- **Exact-dimension form of the descent.**  Every nonempty real square matrix
    has a real invariant subspace whose dimension is *exactly* `1` or *exactly*
    `2` — the `1×1` / `2×2` blocks of the real quasi-triangular Schur form
    (16.4).  Sharpens `exists_real_invariant_subspace_dim_le_two` (`≤ 2`) using
    the linear independence of `Re v, Im v` in the conjugate-pair case. -/
theorem exists_real_invariant_subspace_dim_one_or_two {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      (finrank ℝ W = 1 ∨ finrank ℝ W = 2) ∧
        ∀ w ∈ W, A.mulVecLin w ∈ W := by
  rcases real_peel_one_or_two hn A with ⟨μ, x, hxne, hAx⟩ | ⟨α, β, x, y, _hβ, hind, hAx, hAy⟩
  · -- 1-dimensional: W = span {x}, with A x = μ • x
    refine ⟨Submodule.span ℝ {x}, Or.inl (finrank_span_singleton hxne), ?_⟩
    intro w hw
    have hmap : Submodule.map A.mulVecLin (Submodule.span ℝ {x})
        ≤ Submodule.span ℝ {x} := by
      rw [Submodule.map_span_le]
      intro m hm
      simp only [Set.mem_singleton_iff] at hm
      rw [hm, Matrix.mulVecLin_apply, hAx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    exact hmap (Submodule.mem_map_of_mem hw)
  · -- 2-dimensional: W = span {x, y}, linearly independent
    have hrange : (Set.range ![x, y]) = ({x, y} : Set (Fin n → ℝ)) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    refine ⟨Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)), Or.inr ?_, ?_⟩
    · have h2 : finrank ℝ (Submodule.span ℝ (Set.range ![x, y])) = Fintype.card (Fin 2) :=
        finrank_span_eq_card hind
      rw [hrange] at h2
      simpa using h2
    · have hx : A *ᵥ x ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
        rw [hAx]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hy : A *ᵥ y ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
        rw [hAy]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      exact mulVecLin_maps_span_pair A hx hy

/-- **Exact-dimension descent with irreducible two-dimensional branch.**  Every
    nonempty real square matrix has an invariant subspace of dimension `1` or
    `2`; in the `2`-dimensional nonreal branch, the subspace has no nonzero real
    eigenline.  This is the source-side payload that a stronger real
    quasi-Schur export can thread through the deflation recursion. -/
theorem exists_real_invariant_subspace_dim_one_or_two_no_real_eigenline
    {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      (finrank ℝ W = 1 ∨
        (finrank ℝ W = 2 ∧
          ∀ w ∈ W, w ≠ 0 ->
            ¬ ∃ ν : ℝ, A *ᵥ w = ν • w)) ∧
        ∀ w ∈ W, A.mulVecLin w ∈ W := by
  rcases real_peel_one_or_two hn A with
    ⟨μ, x, hxne, hAx⟩ | ⟨α, β, x, y, hβ, hind, hAx, hAy⟩
  · -- 1-dimensional: W = span {x}, with A x = μ • x
    refine ⟨Submodule.span ℝ {x}, Or.inl (finrank_span_singleton hxne), ?_⟩
    intro w hw
    have hmap : Submodule.map A.mulVecLin (Submodule.span ℝ {x})
        ≤ Submodule.span ℝ {x} := by
      rw [Submodule.map_span_le]
      intro m hm
      simp only [Set.mem_singleton_iff] at hm
      rw [hm, Matrix.mulVecLin_apply, hAx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    exact hmap (Submodule.mem_map_of_mem hw)
  · -- 2-dimensional: W = span {x, y}, with no real eigenline
    have hrange : (Set.range ![x, y]) = ({x, y} : Set (Fin n → ℝ)) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    refine ⟨Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)), Or.inr ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h2 : finrank ℝ (Submodule.span ℝ (Set.range ![x, y])) =
            Fintype.card (Fin 2) :=
          finrank_span_eq_card hind
        rw [hrange] at h2
        simpa using h2
      · intro w hw hwne hEig
        rcases (Submodule.mem_span_pair.mp hw) with ⟨a, b, hrepr⟩
        have hcomb_ne : (a • x + b • y : Fin n → ℝ) ≠ 0 := by
          intro hzero
          apply hwne
          rw [← hrepr]
          exact hzero
        exact
          no_real_eigenvector_in_span_of_rotation_scaling
            A α β x y hβ hind hAx hAy a b hcomb_ne
            (by
              rcases hEig with ⟨ν, hν⟩
              exact ⟨ν, by simpa [hrepr] using hν⟩)
    · have hx : A *ᵥ x ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
        rw [hAx]
        exact Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hy : A *ᵥ y ∈ Submodule.span ℝ ({x, y} : Set (Fin n → ℝ)) := by
        rw [hAy]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      exact mulVecLin_maps_span_pair A hx hy

-- ============================================================
-- §16.2 (16.4) / §17.4 [106].  STATUS after this module.
-- ============================================================
--
-- CLOSED (unconditionally, honest domain `0 < n` only):
--   • `exists_real_invariant_subspace_dim_le_two` — the exact primitive the
--     `RealSchurTriangulation.lean` obstruction named as missing from Mathlib
--     v4.29.0 ("no ready-made 'invariant subspace of dimension ≤ 2' primitive"):
--     a real `A`-invariant subspace with `0 < finrank ≤ 2`.
--   • `exists_real_invariant_subspace_dim_one_or_two` — the sharpened
--     `finrank = 1 ∨ finrank = 2` version (the `1×1`/`2×2` blocks of (16.4)).
--   • `exists_real_invariant_subspace_dim_one_or_two_no_real_eigenline` — the
--     same exact-dimension descent with the two-dimensional branch retaining the
--     no-real-eigenline irreducibility certificate.
--   • `real_peel_one_or_two` — the explicit, DEFLATION-READY dichotomy: either a
--     real eigenvalue with a real eigenvector (`1×1` block), or `α ± β i`,
--     `β ≠ 0`, with two `ℝ`-linearly independent real vectors on which `A` acts
--     by the real rotation-scaling block `[[α, β], [-β, α]]` (`2×2` block).  This
--     is precisely the "conjugate-pair recombination into a real invariant
--     subspace" that `SemiconvergentExistenceGaps.lean` GAP (3) recorded as
--     absent from Mathlib.
--
-- RESIDUAL OBSTRUCTION (the full general (16.4)).  Iterating this peel-1-or-2
-- primitive into the FULL real quasi-triangular ORTHOGONAL Schur form
-- `QᵀAQ = R` (block-upper-triangular, `Q` orthogonal) still needs the deflation
-- INDUCTION with a *variable* peel size `d ∈ {1, 2}`: an orthonormal basis of the
-- `d`-dimensional invariant subspace extended to the whole space
-- (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), the resulting
-- orthogonal `Q` with leading `d` columns spanning `W`, the block-triangular
-- structure of `QᵀAQ`, and re-embedding a block-diagonal orthogonal matrix over a
-- `Fin (d + m)` reindexing.  Mathlib v4.29.0 has none of this assembled, and the
-- existing `RealSchurTriangulation.lean` deflation is hard-wired to peel size `1`
-- (`Fin (n+1)` via `Fin.cases`); a variable-`d` orthogonal deflation is the
-- single remaining bottleneck to (16.4) in full generality.  The invariant
-- subspace supplied here is exactly the primitive that induction consumes.

end LeanFpAnalysis.FP
