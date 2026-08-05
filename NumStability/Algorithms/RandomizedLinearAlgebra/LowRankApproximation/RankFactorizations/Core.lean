import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.LowRankApprox`; the historical path re-exports this module.
-/















/-!
# Low-rank approximation foundations for the RandNLA CACM formalization

This file begins the local foundation for the paper's low-rank approximation
claims, including the structural condition around equation (9).  It deliberately
separates exact analysis objects from implementation-facing floating-point
objects: sampling probabilities remain exact mathematical inputs by the current
project convention, while computed projectors/bases are handled in
`Preconditioning.lean` by explicit certificates.
-/

namespace NumStability

open scoped BigOperators

/-- An exact rectangular rank factorization certificate `A = X Y` through an
inner dimension `r`.  This is the local rank vocabulary used before importing a
full rectangular SVD/rank/pseudoinverse library. -/
structure RectRankFactorization (m n r : ℕ) (A : Fin m → Fin n → ℝ) where
  left : Fin m → Fin r → ℝ
  right : Fin r → Fin n → ℝ
  factorization : ∀ i j, A i j = ∑ a : Fin r, left i a * right a j

/-- Repository-local predicate for "rectangular rank at most `r`", represented
by an explicit exact factorization. -/
def RectRankAtMost (m n r : ℕ) (A : Fin m → Fin n → ℝ) : Prop :=
  Nonempty (RectRankFactorization m n r A)

/-- Exact column reindexing along an equivalence between possibly different
finite right-coordinate domains.  This is analysis-object reindexing only; it
does not compute or round any matrix entries. -/
def rectReindexCols {m n p : ℕ} (π : Fin p ≃ Fin n)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => A i (π j)

/-- Exact column-permutation transport for an explicit rectangular rank
factorization.  This is a reindexing adapter only: it does not compute a
permutation or any floating-point quantity. -/
def RectRankFactorization.permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ}
    (fac : RectRankFactorization m n r A) (π : Fin n ≃ Fin n) :
    RectRankFactorization m n r (rectPermuteCols π A) where
  left := fac.left
  right := fun a j => fac.right a (π j)
  factorization := by
    intro i j
    change A i (π j) = ∑ a : Fin r, fac.left i a * fac.right a (π j)
    exact fac.factorization i (π j)

/-- Rank-at-most is preserved by exact column permutation. -/
theorem RectRankAtMost.permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin n ≃ Fin n)
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m n r (rectPermuteCols π A) := by
  rcases hA with ⟨fac⟩
  exact ⟨fac.permuteCols π⟩

/-- Rank-at-most can be transported back across an exact column permutation. -/
theorem RectRankAtMost.of_permuteCols {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin n ≃ Fin n)
    (hA : RectRankAtMost m n r (rectPermuteCols π A)) :
  RectRankAtMost m n r A := by
  rcases hA with ⟨fac⟩
  exact
    ⟨{ left := fac.left
       right := fun a j => fac.right a (π.symm j)
       factorization := by
        intro i j
        have h := fac.factorization i (π.symm j)
        simpa [rectPermuteCols] using h }⟩

/-- Exact column-equivalence transport for an explicit rectangular rank
factorization across possibly different finite right-coordinate domains. -/
def RectRankFactorization.reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ}
    (fac : RectRankFactorization m n r A) (π : Fin p ≃ Fin n) :
    RectRankFactorization m p r (rectReindexCols π A) where
  left := fac.left
  right := fun a j => fac.right a (π j)
  factorization := by
    intro i j
    change A i (π j) = ∑ a : Fin r, fac.left i a * fac.right a (π j)
    exact fac.factorization i (π j)

/-- Rank-at-most is preserved by exact column reindexing across an equivalence
of finite right-coordinate domains. -/
theorem RectRankAtMost.reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin p ≃ Fin n)
    (hA : RectRankAtMost m n r A) :
    RectRankAtMost m p r (rectReindexCols π A) := by
  rcases hA with ⟨fac⟩
  exact ⟨fac.reindexCols π⟩

/-- Rank-at-most transports back across exact column reindexing by an
equivalence of finite right-coordinate domains. -/
theorem RectRankAtMost.of_reindexCols {m n p r : ℕ}
    {A : Fin m → Fin n → ℝ} (π : Fin p ≃ Fin n)
    (hA : RectRankAtMost m p r (rectReindexCols π A)) :
    RectRankAtMost m n r A := by
  rcases hA with ⟨fac⟩
  exact
    ⟨{ left := fac.left
       right := fun a j => fac.right a (π.symm j)
       factorization := by
        intro i j
        have h := fac.factorization i (π.symm j)
        simpa [rectReindexCols] using h }⟩

/-- Exact column reindexing along an equivalence preserves the squared
rectangular Frobenius norm. -/
theorem frobNormSqRect_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (rectReindexCols π A) = frobNormSqRect A := by
  unfold frobNormSqRect rectReindexCols
  congr 1
  ext i
  exact
    Fintype.sum_equiv π
      (fun j : Fin p => A i (π j) ^ 2)
      (fun j : Fin n => A i j ^ 2)
      (fun _ => rfl)

/-- Exact column reindexing along an equivalence preserves the rectangular
Frobenius norm. -/
theorem frobNormRect_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A : Fin m → Fin n → ℝ) :
    frobNormRect (rectReindexCols π A) = frobNormRect A := by
  unfold frobNormRect
  rw [frobNormSqRect_reindexCols π A]

/-- Transport a repository rank-at-most certificate across an explicit equality
of displayed rank parameters. -/
theorem rectRankAtMost_of_eq_rank {m n r k : ℕ}
    {A : Fin m → Fin n → ℝ}
    (h : r = k) (hr : RectRankAtMost m n r A) :
    RectRankAtMost m n k A := by
  subst k
  exact hr

/-- Linear map induced by the right factor in a rectangular rank
factorization.  Its kernel is the right nullspace used by the q-dimensional
Eckart--Young min-max route. -/
def rectRankRightFactorMap {n r : ℕ}
    (right : Fin r → Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := fun x => fun a => ∑ j : Fin n, right a j * x j
  map_add' := by
    intro x y
    ext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext a
    change (∑ j : Fin n, right a j * (c * x j)) =
      c * ∑ j : Fin n, right a j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Euclidean-coordinate version of `rectRankRightFactorMap`.

The repository's matrix entries are plain finite functions, which carry the
linear algebra structure needed by rank-nullity but not the inner-product
instance used by mathlib's orthonormal-basis API in this project setup.  This
map puts only the kernel-selection layer in `EuclideanSpace`, while preserving
the same coordinate formula. -/
def rectRankRightFactorEuclideanMap {n r : ℕ}
    (right : Fin r → Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin r → ℝ) where
  toFun := fun x => fun a => ∑ j : Fin n, right a j * x j
  map_add' := by
    intro x y
    ext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext a
    change (∑ j : Fin n, right a j * (c * x j)) =
      c * ∑ j : Fin n, right a j * x j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The right factor of an `r`-column factorization on `r+q` coordinates has a
right kernel of dimension at least `q`.

This is exact rank-nullity infrastructure for the multi-tail
Eckart--Young route.  It does not select the `q`-dimensional witness family or
prove the tail Frobenius lower bound. -/
theorem rectRankRightFactorMap_ker_finrank_ge {r q : ℕ}
    (right : Fin r → Fin (r + q) → ℝ) :
    q ≤ Module.finrank ℝ (LinearMap.ker (rectRankRightFactorMap right)) := by
  classical
  let Rmap : (Fin (r + q) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    rectRankRightFactorMap right
  have hrange :
      Module.finrank ℝ (LinearMap.range Rmap) ≤ r := by
    calc
      Module.finrank ℝ (LinearMap.range Rmap) ≤
          Module.finrank ℝ (Fin r → ℝ) :=
        (LinearMap.range Rmap).finrank_le
      _ = r := by
        simp
  have hsum :
      Module.finrank ℝ (LinearMap.range Rmap) +
          Module.finrank ℝ (LinearMap.ker Rmap) =
        r + q := by
    simpa using
      (LinearMap.finrank_range_add_finrank_ker
        (K := ℝ) (V := Fin (r + q) → ℝ)
        (V₂ := Fin r → ℝ) Rmap)
  have hle :
      r + q ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) := by
    calc
      r + q =
          Module.finrank ℝ (LinearMap.range Rmap) +
            Module.finrank ℝ (LinearMap.ker Rmap) := hsum.symm
      _ ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) :=
          Nat.add_le_add_right hrange _
  exact Nat.le_of_add_le_add_left hle

/-- Rank-nullity lower bound specialized to an explicit repository
rank-factorization certificate. -/
theorem rectRankFactorization_rightKernel_finrank_ge {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorMap fac.right)) :=
  rectRankRightFactorMap_ker_finrank_ge fac.right

/-- Euclidean-coordinate kernel dimension lower bound for the right factor of
an `r`-column factorization on `r+q` coordinates. -/
theorem rectRankRightFactorEuclideanMap_ker_finrank_ge {r q : ℕ}
    (right : Fin r → Fin (r + q) → ℝ) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorEuclideanMap right)) := by
  classical
  let Rmap : EuclideanSpace ℝ (Fin (r + q)) →ₗ[ℝ] (Fin r → ℝ) :=
    rectRankRightFactorEuclideanMap right
  have hrange :
      Module.finrank ℝ (LinearMap.range Rmap) ≤ r := by
    calc
      Module.finrank ℝ (LinearMap.range Rmap) ≤
          Module.finrank ℝ (Fin r → ℝ) :=
        (LinearMap.range Rmap).finrank_le
      _ = r := by
        simp
  have hsum :
      Module.finrank ℝ (LinearMap.range Rmap) +
          Module.finrank ℝ (LinearMap.ker Rmap) =
        r + q := by
    simpa using
      (LinearMap.finrank_range_add_finrank_ker
        (K := ℝ) (V := EuclideanSpace ℝ (Fin (r + q)))
        (V₂ := Fin r → ℝ) Rmap)
  have hle :
      r + q ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) := by
    calc
      r + q =
          Module.finrank ℝ (LinearMap.range Rmap) +
            Module.finrank ℝ (LinearMap.ker Rmap) := hsum.symm
      _ ≤ r + Module.finrank ℝ (LinearMap.ker Rmap) :=
          Nat.add_le_add_right hrange _
  exact Nat.le_of_add_le_add_left hle

/-- Euclidean-coordinate rank-nullity lower bound specialized to an explicit
repository rank-factorization certificate. -/
theorem rectRankFactorization_euclideanRightKernel_finrank_ge {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    q ≤ Module.finrank ℝ
      (LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)) :=
  rectRankRightFactorEuclideanMap_ker_finrank_ge fac.right

/-- A vector killed by the right factor is killed by the represented matrix.

This is the q-dimensional analogue of the algebra hidden inside the earlier
`r+1` rank-nullity bridge. -/
theorem rectRankFactorization_matrix_rightKernel_of_rightFactor_ker
    {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B)
    {x : Fin (r + q) → ℝ}
    (hx : x ∈ LinearMap.ker (rectRankRightFactorMap fac.right)) :
    ∀ i : Fin m, (∑ j : Fin (r + q), B i j * x j) = 0 := by
  classical
  have hRzero : rectRankRightFactorMap fac.right x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + q), fac.right a j * x j) = 0 := by
    intro a
    simpa [rectRankRightFactorMap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + q), B i j * x j)
        =
          ∑ j : Fin (r + q),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + q), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + q),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + q), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- Euclidean-coordinate right-factor kernel membership still annihilates the
represented matrix entrywise. -/
theorem rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker
    {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B)
    {x : EuclideanSpace ℝ (Fin (r + q))}
    (hx : x ∈ LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)) :
    ∀ i : Fin m, (∑ j : Fin (r + q), B i j * x j) = 0 := by
  classical
  have hRzero : rectRankRightFactorEuclideanMap fac.right x = 0 := by
    simpa [LinearMap.mem_ker] using hx
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + q), fac.right a j * x j) = 0 := by
    intro a
    simpa [rectRankRightFactorEuclideanMap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + q), B i j * x j)
        =
          ∑ j : Fin (r + q),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + q), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + q),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + q), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- Select `q` linearly independent vectors inside the right-factor kernel of
a rank-`r` competitor on `r+q` right coordinates, and push each selected vector
through the stored factorization to get an entrywise right-kernel equation for
the represented matrix.

This is exact-object vector-selection infrastructure for the multi-tail
Eckart--Young route.  It does not prove the tail Frobenius lower bound or any
computed SVD/projector/sketch routine. -/
theorem rectRankFactorization_exists_rightKernelFamily {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q → LinearMap.ker (rectRankRightFactorMap fac.right),
      LinearIndependent ℝ x ∧
        ∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : Fin (r + q) → ℝ) j) = 0 := by
  classical
  have hdim :
      q ≤ Module.finrank ℝ
        (LinearMap.ker (rectRankRightFactorMap fac.right)) :=
    rectRankFactorization_rightKernel_finrank_ge fac
  rcases
      exists_linearIndependent_of_le_finrank
        (R := ℝ)
        (M := LinearMap.ker (rectRankRightFactorMap fac.right))
        hdim with
    ⟨x, hxli⟩
  refine ⟨x, hxli, ?_⟩
  intro c i
  exact
    rectRankFactorization_matrix_rightKernel_of_rightFactor_ker
      fac (x c).property i

/-- Select `q` orthonormal vectors inside the right-factor kernel of a
rank-`r` competitor on `r+q` right coordinates, and push each selected vector
through the stored factorization to get an entrywise right-kernel equation for
the represented matrix.

This strengthens `rectRankFactorization_exists_rightKernelFamily` to the
orthonormal witness shape needed by the multi-tail min--max route.  It remains
exact-object infrastructure: it does not prove the tail Frobenius lower bound
or certify computed SVD/projector/sketch routines. -/
theorem rectRankFactorization_exists_orthonormalRightKernelFamily {m r q : ℕ}
    {B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q → LinearMap.ker (rectRankRightFactorEuclideanMap fac.right),
      Orthonormal ℝ x ∧
        ∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : EuclideanSpace ℝ (Fin (r + q))) j) = 0 := by
  classical
  let K : Type :=
    LinearMap.ker (rectRankRightFactorEuclideanMap fac.right)
  have hdim : q ≤ Module.finrank ℝ K := by
    simpa [K] using rectRankFactorization_euclideanRightKernel_finrank_ge fac
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let x : Fin q → K := fun c => b (Fin.castLE hdim c)
  refine ⟨x, ?_, ?_⟩
  · have hb : Orthonormal ℝ
        (b : Fin (Module.finrank ℝ K) → K) :=
      b.orthonormal
    have hinj :
        Function.Injective
          (Fin.castLE hdim : Fin q → Fin (Module.finrank ℝ K)) :=
      Fin.castLE_injective hdim
    simpa [x, Function.comp_def] using hb.comp (Fin.castLE hdim) hinj
  · intro c i
    exact
      rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker
        fac (x c).property i

/-- A rank-at-most-`r` factorization with `r+1` right coordinates has a
nonzero right-kernel vector.

This is the first rank-nullity foundation for the Eckart--Young route: the
standard min-max lower-bound argument needs a nonzero vector in an
`r+1`-dimensional right subspace that is annihilated by any competing
rank-`r` matrix.  This theorem is exact-object algebra only; it does not prove
the singular-value lower bound or any computed SVD/projector routine. -/
theorem rectRankFactorization_exists_rightKernelVector_succ {m r : ℕ}
    {B : Fin m → Fin (r + 1) → ℝ}
    (fac : RectRankFactorization m (r + 1) r B) :
    ∃ x : Fin (r + 1) → ℝ,
      x ≠ 0 ∧
        ∀ i : Fin m, (∑ j : Fin (r + 1), B i j * x j) = 0 := by
  classical
  let Rmap : (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) := {
    toFun := fun x => fun a => ∑ j : Fin (r + 1), fac.right a j * x j
    map_add' := by
      intro x y
      ext a
      simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      ext a
      simp [Finset.mul_sum, mul_assoc, mul_comm]
  }
  have hdim :
      Module.finrank ℝ (Fin r → ℝ) <
        Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    simp
  have hker : LinearMap.ker Rmap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := Rmap) hdim
  rcases (Submodule.ne_bot_iff (LinearMap.ker Rmap)).1 hker with
    ⟨x, hxmem, hxne⟩
  refine ⟨x, hxne, ?_⟩
  have hRzero : Rmap x = 0 := by
    simpa [LinearMap.mem_ker] using hxmem
  have hright :
      ∀ a : Fin r, (∑ j : Fin (r + 1), fac.right a j * x j) = 0 := by
    intro a
    simpa [Rmap] using congrFun hRzero a
  intro i
  calc
    (∑ j : Fin (r + 1), B i j * x j)
        =
          ∑ j : Fin (r + 1),
            (∑ a : Fin r, fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [fac.factorization i j]
    _ =
          ∑ j : Fin (r + 1), ∑ a : Fin r,
            (fac.left i a * fac.right a j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ a : Fin r, ∑ j : Fin (r + 1),
            (fac.left i a * fac.right a j) * x j := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin r,
            fac.left i a *
              (∑ j : Fin (r + 1), fac.right a j * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by
            simp [hright]

/-- The rank-nullity kernel vector specialized to the repository
`RectRankAtMost` predicate. -/
theorem rectRankAtMost_exists_rightKernelVector_succ {m r : ℕ}
    {B : Fin m → Fin (r + 1) → ℝ}
    (hB : RectRankAtMost m (r + 1) r B) :
    ∃ x : Fin (r + 1) → ℝ,
      x ≠ 0 ∧
        ∀ i : Fin m, (∑ j : Fin (r + 1), B i j * x j) = 0 := by
  rcases hB with ⟨fac⟩
  exact rectRankFactorization_exists_rightKernelVector_succ fac






























































































/-- Canonical order-preserving cast from `Fin n` to mathlib's zero-indexed
Hermitian-eigenvalue domain for matrices indexed by `Fin n`. -/
def finCardIndex (n : ℕ) (j : Fin n) : Fin (Fintype.card (Fin n)) :=
  Fin.cast (by simp) j

/-- The canonical cast preserves the natural `Fin` order. -/
theorem finCardIndex_le {n : ℕ} {i j : Fin n} (hij : i ≤ j) :
    finCardIndex n i ≤ finCardIndex n j := by
  rw [Fin.le_def] at hij ⊢
  simpa [finCardIndex] using hij























































































































































































































































































































































































































































































































































































































































































































































































































































/-- Displayed top-`k` index cast into the ambient right-Gram index type.  The
semantic ordering certificate below uses this to compare the embedding-selected
basis directions with the ordered zero-indexed singular-value sequence. -/
def rectTopIndex {n k : ℕ} (hk : k ≤ n) (a : Fin k) : Fin n :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt hk⟩

/-- The displayed top-index cast preserves the `Fin` order. -/
theorem rectTopIndex_le {n k : ℕ} {hk : k ≤ n}
    {a b : Fin k} (hab : a ≤ b) :
    rectTopIndex hk a ≤ rectTopIndex hk b := by
  rw [Fin.le_def] at hab ⊢
  exact hab





















































































































































/-- Last displayed top index in a nonempty top-`k` block. -/
def rectTopLastIndex {k : ℕ} (hk0 : 0 < k) : Fin k :=
  ⟨k - 1, Nat.pred_lt (Nat.ne_of_gt hk0)⟩

/-- Every displayed top index is at most the last displayed top index. -/
theorem le_rectTopLastIndex {k : ℕ} (hk0 : 0 < k) (a : Fin k) :
    a ≤ rectTopLastIndex hk0 := by
  rw [Fin.le_def]
  exact Nat.le_pred_of_lt a.isLt

/-- The displayed top-index inclusion sends every selected index before the
last selected index. -/
theorem rectTopIndex_le_last {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k)
    (a : Fin k) :
    rectTopIndex hk a ≤ rectTopIndex hk (rectTopLastIndex hk0) :=
  rectTopIndex_le (le_rectTopLastIndex hk0 a)




















































































































































































































































































































































































































































































































/-- The Frobenius residual of a candidate low-rank approximation. -/
noncomputable def lowRankResidualFrob {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) : ℝ :=
  frobNormRect (fun i j => A i j - B i j)

/-- Exact column-permutation invariance of the Frobenius residual when the
same permutation is applied to the source matrix and the competitor. -/
theorem lowRankResidualFrob_permuteCols {m n : ℕ}
    (π : Fin n ≃ Fin n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob (rectPermuteCols π A) (rectPermuteCols π B) =
      lowRankResidualFrob A B := by
  simpa [lowRankResidualFrob, rectPermuteCols] using
    (frobNormRect_permuteCols π (fun i j => A i j - B i j))

/-- Exact column-equivalence invariance of the Frobenius residual across
possibly different finite right-coordinate domains. -/
theorem lowRankResidualFrob_reindexCols {m n p : ℕ}
    (π : Fin p ≃ Fin n) (A B : Fin m → Fin n → ℝ) :
    lowRankResidualFrob (rectReindexCols π A) (rectReindexCols π B) =
      lowRankResidualFrob A B := by
  simpa [lowRankResidualFrob, rectReindexCols] using
    (frobNormRect_reindexCols π (fun i j => A i j - B i j))

/-- If `x` is in the right kernel of `B`, then the residual action `(A-B)x`
is exactly the source action `Ax`.  This is the algebraic bridge used by the
rank-nullity/Eckart--Young min-max route. -/
theorem rectMatMulVec_sub_eq_left_of_rightKernel {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hBx : ∀ i : Fin m, (∑ j : Fin n, B i j * x j) = 0) :
    rectMatMulVec (fun i j => A i j - B i j) x = rectMatMulVec A x := by
  ext i
  unfold rectMatMulVec
  calc
    (∑ j : Fin n, (A i j - B i j) * x j)
        = ∑ j : Fin n, (A i j * x j - B i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = (∑ j : Fin n, A i j * x j) -
          (∑ j : Fin n, B i j * x j) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ j : Fin n, A i j * x j := by
            rw [hBx i, sub_zero]

/-- Finite Bessel/Frobenius domination for an exact orthonormal family of
right probes.  Applying a rectangular matrix to `q` orthonormal right vectors
has total squared output energy at most the rectangular Frobenius square.

This is exact-object residual-energy infrastructure for the multi-tail
equation-(9) min--max route.  It charges no probability-construction error,
and any computed probe/SVD/projector routine remains a separate certificate
obligation. -/
theorem sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal
    {m n q : ℕ}
    (M : Fin m → Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q,
        vecNorm2Sq (rectMatMulVec M
          (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) ≤
      frobNormSqRect M := by
  have hrow : ∀ i : Fin m,
      (∑ c : Fin q,
          (∑ j : Fin n, M i j *
            (x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) ≤
        ∑ j : Fin n, M i j ^ 2 := by
    intro i
    let row : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun j : Fin n => M i j)
    have hb :
        (∑ c : Fin q, ‖inner ℝ (x c) row‖ ^ 2) ≤ ‖row‖ ^ 2 := by
      simpa using
        (hx.sum_inner_products_le
          (x := row) (s := (Finset.univ : Finset (Fin q))))
    simpa [row, PiLp.inner_apply, EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs, sq_abs, mul_comm] using hb
  unfold vecNorm2Sq rectMatMulVec frobNormSqRect
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => hrow i)

/-- Right-kernel residual-energy domination.  If every exact orthonormal probe
lies in the right kernel of the competitor `B`, then the source actions
`A x_c` are exactly residual actions `(A-B)x_c`, and their total squared energy
is bounded by the residual Frobenius square.

This is exact-object min--max infrastructure only.  Sampling probabilities and
sampling laws remain exact mathematical inputs by convention. -/
theorem sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel
    {m n q : ℕ}
    (A B : Fin m → Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x)
    (hBx : ∀ c : Fin q, ∀ i : Fin m,
      (∑ j : Fin n, B i j *
        (x c : EuclideanSpace ℝ (Fin n)) j) = 0) :
    (∑ c : Fin q,
        vecNorm2Sq (rectMatMulVec A
          (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) ≤
      frobNormSqRect (fun i j => A i j - B i j) := by
  have hbase :=
    sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal
      (fun i j => A i j - B i j) x hx
  have heq :
      (∑ c : Fin q,
          vecNorm2Sq (rectMatMulVec A
            (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) =
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec (fun i j => A i j - B i j)
              (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have hres :=
      rectMatMulVec_sub_eq_left_of_rightKernel A B
        (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)
        (hBx c)
    rw [hres]
  rw [heq]
  exact hbase

/-- The LR.1di orthonormal right-kernel family also gives a residual-energy
certificate: for every exact rank-`r` competitor on `r+q` right coordinates
there is an orthonormal `Fin q` family in the Euclidean-coordinate right-factor
kernel, it annihilates the competitor, and the source action on that family is
bounded by the competitor residual Frobenius square.

This is the residual side of the q-dimensional trace/Rayleigh lower-bound
route.  It does not prove the matching source-side tail-energy lower bound,
Ky Fan/Courant--Fischer comparison, Eckart--Young optimality, randomness, or
computed non-probability routine certificates. -/
theorem rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
    {m r q : ℕ}
    {A B : Fin m → Fin (r + q) → ℝ}
    (fac : RectRankFactorization m (r + q) r B) :
    ∃ x : Fin q →
        LinearMap.ker (rectRankRightFactorEuclideanMap fac.right),
      Orthonormal ℝ x ∧
        (∀ c : Fin q, ∀ i : Fin m,
          (∑ j : Fin (r + q), B i j *
            (x c : EuclideanSpace ℝ (Fin (r + q))) j) = 0) ∧
        (∑ c : Fin q,
          vecNorm2Sq (rectMatMulVec A
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j))) ≤
          frobNormSqRect (fun i j => A i j - B i j) := by
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily fac with
    ⟨x, hx, hzero⟩
  refine ⟨x, hx, hzero, ?_⟩
  have hxAmbient :
      Orthonormal ℝ
        (fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))) := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [Submodule.coe_inner] using h
  exact
    sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel
      A B
      (fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q))))
      hxAmbient
      hzero

/-- Scalar head-tail mass-transfer inequality.

If the head weights `lambda` are all above a visible gap `eta`, the tail
weights `mu` are all below it, the nonnegative head coordinate mass balances
the missing tail coordinate mass, and each tail coordinate mass is at most one,
then the weighted head-plus-tail mass dominates the full tail sum.

This is the diagonal Ky Fan algebra used by LR.1dk.  It is exact-object
infrastructure only; ordered singular-value instantiation is a later
source-side obligation. -/
theorem headTail_weighted_tail_sum_le_of_gap {r q : ℕ}
    (lambda : Fin r → ℝ) (mu : Fin q → ℝ)
    (alpha : Fin r → ℝ) (beta : Fin q → ℝ) {eta : ℝ}
    (halpha_nonneg : ∀ a : Fin r, 0 ≤ alpha a)
    (hbeta_le_one : ∀ c : Fin q, beta c ≤ 1)
    (hbalance :
      (∑ a : Fin r, alpha a) =
        ∑ c : Fin q, (1 - beta c))
    (hhead : ∀ a : Fin r, eta ≤ lambda a)
    (htail : ∀ c : Fin q, mu c ≤ eta) :
    (∑ c : Fin q, mu c) ≤
      (∑ a : Fin r, lambda a * alpha a) +
        ∑ c : Fin q, mu c * beta c := by
  have hheadLower :
      eta * (∑ a : Fin r, alpha a) ≤
        ∑ a : Fin r, lambda a * alpha a := by
    calc
      eta * (∑ a : Fin r, alpha a)
          = ∑ a : Fin r, eta * alpha a := by
              rw [Finset.mul_sum]
      _ ≤ ∑ a : Fin r, lambda a * alpha a := by
            exact Finset.sum_le_sum
              (fun a _ => mul_le_mul_of_nonneg_right (hhead a)
                (halpha_nonneg a))
  have htailDefUpper :
      (∑ c : Fin q, mu c * (1 - beta c)) ≤
        eta * (∑ c : Fin q, (1 - beta c)) := by
    calc
      (∑ c : Fin q, mu c * (1 - beta c))
          ≤ ∑ c : Fin q, eta * (1 - beta c) := by
              exact Finset.sum_le_sum
                (fun c _ => mul_le_mul_of_nonneg_right (htail c)
                  (sub_nonneg.mpr (hbeta_le_one c)))
      _ = eta * (∑ c : Fin q, (1 - beta c)) := by
            rw [Finset.mul_sum]
  have hdef_le_head :
      (∑ c : Fin q, mu c * (1 - beta c)) ≤
        ∑ a : Fin r, lambda a * alpha a := by
    calc
      (∑ c : Fin q, mu c * (1 - beta c))
          ≤ eta * (∑ c : Fin q, (1 - beta c)) := htailDefUpper
      _ = eta * (∑ a : Fin r, alpha a) := by rw [← hbalance]
      _ ≤ ∑ a : Fin r, lambda a * alpha a := hheadLower
  have htail_decomp :
      (∑ c : Fin q, mu c) =
        (∑ c : Fin q, mu c * beta c) +
          ∑ c : Fin q, mu c * (1 - beta c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  calc
    (∑ c : Fin q, mu c)
        = (∑ c : Fin q, mu c * beta c) +
            ∑ c : Fin q, mu c * (1 - beta c) := htail_decomp
    _ ≤ (∑ c : Fin q, mu c * beta c) +
          ∑ a : Fin r, lambda a * alpha a := by
          exact add_le_add (le_refl _) hdef_le_head
    _ = (∑ a : Fin r, lambda a * alpha a) +
          ∑ c : Fin q, mu c * beta c := by ring

/-- A coordinate of an exact Euclidean orthonormal frame carries total squared
mass at most one.  This is Bessel's inequality against a standard coordinate
vector. -/
theorem orthonormal_sum_coord_sq_le_one {n q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) (j : Fin n) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) ≤ 1 := by
  classical
  let e : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun k : Fin n => if k = j then (1 : ℝ) else 0)
  have hb :
      (∑ c : Fin q, ‖inner ℝ (x c) e‖ ^ 2) ≤ ‖e‖ ^ 2 := by
    simpa using
      (hx.sum_inner_products_le
        (x := e) (s := (Finset.univ : Finset (Fin q))))
  have hinner :
      ∀ c : Fin q, inner ℝ (x c) e =
        (x c : EuclideanSpace ℝ (Fin n)) j := by
    intro c
    rw [PiLp.inner_apply]
    simp [e, real_inner_eq_re_inner, RCLike.inner_apply, Finset.mem_univ]
  have hright : ‖e‖ ^ 2 = 1 := by
    simp [e, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      Finset.mem_univ]
  calc
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2)
        = ∑ c : Fin q, ‖inner ℝ (x c) e‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hinner c]
            simp [Real.norm_eq_abs, sq_abs]
    _ ≤ ‖e‖ ^ 2 := hb
    _ = 1 := hright

/-- The coordinate masses of a `q`-element exact Euclidean orthonormal frame
sum to `q`. -/
theorem orthonormal_sum_coord_sq_eq_card {n q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    (∑ j : Fin n,
        ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) =
      (q : ℝ) := by
  classical
  rw [orthonormal_iff_ite] at hx
  have hnorm :
      ∀ c : Fin q,
        (∑ j : Fin n,
          ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) = 1 := by
    intro c
    have hcc := hx c c
    have hnorm_sq : ‖x c‖ ^ 2 = 1 := by
      simpa [pow_two] using hcc
    have hcoord :
        (∑ j : Fin n,
          ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) =
          ‖x c‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hcoord, hnorm_sq]
  calc
    (∑ j : Fin n,
        ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2)
        = ∑ c : Fin q,
            ∑ j : Fin n,
              ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ c : Fin q, (1 : ℝ) := by
          exact Finset.sum_congr rfl (fun c _ => hnorm c)
    _ = (q : ℝ) := by simp

/-- Expanding the total action of a diagonal matrix on a Euclidean frame gives
the singular-square weights times the coordinate masses. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq
    {n q : ℕ}
    (sigma : Fin n → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin n)) :
    (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin n => if i = j then sigma i else 0)
            (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j))) =
      ∑ j : Fin n,
        sigma j ^ 2 *
          ∑ c : Fin q, ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2 := by
  classical
  have hdiag :
      ∀ c : Fin q, ∀ i : Fin n,
        (∑ j : Fin n,
          (if i = j then sigma i else 0) *
            ((x c : EuclideanSpace ℝ (Fin n)) j)) =
          sigma i * ((x c : EuclideanSpace ℝ (Fin n)) i) := by
    intro c i
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  unfold vecNorm2Sq rectMatMulVec
  calc
    (∑ c : Fin q,
        ∑ i : Fin n,
          (∑ j : Fin n,
            (if i = j then sigma i else 0) *
              ((x c : EuclideanSpace ℝ (Fin n)) j)) ^ 2)
        =
          ∑ c : Fin q,
            ∑ i : Fin n,
              (sigma i *
                ((x c : EuclideanSpace ℝ (Fin n)) i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro i _
            rw [hdiag c i]
    _ =
          ∑ i : Fin n,
            ∑ c : Fin q,
              sigma i ^ 2 *
                ((x c : EuclideanSpace ℝ (Fin n)) i) ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ =
          ∑ i : Fin n,
            sigma i ^ 2 *
              ∑ c : Fin q,
                ((x c : EuclideanSpace ℝ (Fin n)) i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]

/-- Diagonal source-side tail-energy lower bound under a visible head-tail gap.

For an exact orthonormal `q`-frame in an `r+q` right domain, if every displayed
head diagonal square is at least `eta` and every displayed tail diagonal square
is at most `eta`, then the total squared action of the diagonal source matrix
on the frame is at least the displayed tail-energy sum.

This is exact-object diagonal Ky Fan infrastructure.  It does not instantiate
the gap from ordered singular values, transport through a nontrivial right
singular-vector table, or certify any computed singular-vector/diagonal
routine.  Sampling probabilities and laws remain exact mathematical inputs by
project convention. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) {eta : ℝ}
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  classical
  let alpha : Fin r → ℝ :=
    fun a => ∑ c : Fin q,
      ((x c : EuclideanSpace ℝ (Fin (r + q))) (Fin.castAdd q a)) ^ 2
  let beta : Fin q → ℝ :=
    fun c => ∑ d : Fin q,
      ((x d : EuclideanSpace ℝ (Fin (r + q))) (Fin.natAdd r c)) ^ 2
  have halpha_nonneg : ∀ a : Fin r, 0 ≤ alpha a := by
    intro a
    exact Finset.sum_nonneg (fun c _ => sq_nonneg _)
  have hbeta_le_one : ∀ c : Fin q, beta c ≤ 1 := by
    intro c
    simpa [beta] using
      orthonormal_sum_coord_sq_le_one x hx (Fin.natAdd r c)
  have hmass :=
    orthonormal_sum_coord_sq_eq_card x hx
  have hsplit :
      (∑ a : Fin r, alpha a) + (∑ c : Fin q, beta c) = (q : ℝ) := by
    have h := hmass
    rw [Fin.sum_univ_add] at h
    simpa [alpha, beta] using h
  have hbalance :
      (∑ a : Fin r, alpha a) =
        ∑ c : Fin q, (1 - beta c) := by
    calc
      (∑ a : Fin r, alpha a)
          = (q : ℝ) - ∑ c : Fin q, beta c := by linarith
      _ = ∑ c : Fin q, (1 - beta c) := by
            simp [Finset.sum_sub_distrib]
  have hweighted :=
    headTail_weighted_tail_sum_le_of_gap
      (fun a : Fin r => sigma (Fin.castAdd q a) ^ 2)
      (fun c : Fin q => sigma (Fin.natAdd r c) ^ 2)
      alpha beta halpha_nonneg hbeta_le_one hbalance hhead htail
  have henergy :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j))) =
        (∑ a : Fin r,
          sigma (Fin.castAdd q a) ^ 2 * alpha a) +
          ∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2 * beta c := by
    rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
    rw [Fin.sum_univ_add]
  rw [henergy]
  exact hweighted

/-- Ordered diagonal head-tail gap certificate, positive-head case.

If the displayed diagonal/singular-value squares are antitone in the coordinate
index and the head block is nonempty, then the last head square is a valid gap
parameter for LR.1dk: every head square lies above it and every tail square
lies below it. -/
theorem diagonal_headTail_square_gap_of_antitone_head_pos {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) (hr : 0 < r)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    ∃ eta : ℝ,
      (∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2) ∧
        ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta := by
  classical
  let lastHead : Fin r := rectTopLastIndex hr
  refine ⟨sigma (Fin.castAdd q lastHead) ^ 2, ?_, ?_⟩
  · intro a
    exact
      hmono (Fin.castAdd q a) (Fin.castAdd q lastHead)
        (by
          simpa [lastHead] using le_rectTopLastIndex hr a)
  · intro c
    exact
      hmono (Fin.castAdd q lastHead) (Fin.natAdd r c)
        (by
          have hlast_le_r : (lastHead : ℕ) ≤ r :=
            Nat.le_of_lt lastHead.isLt
          calc
            ((Fin.castAdd q lastHead : Fin (r + q)) : ℕ)
                = (lastHead : ℕ) := rfl
            _ ≤ r := hlast_le_r
            _ ≤ r + (c : ℕ) := Nat.le_add_right r (c : ℕ)
            _ = ((Fin.natAdd r c : Fin (r + q)) : ℕ) := rfl)

/-- Ordered diagonal source-side tail-energy lower bound, positive-head case.

This composes LR.1dk with the finite ordered-gap certificate above.  It removes
the abstract gap parameter when the displayed head count is positive and the
exact diagonal/singular-value-square table is antitone in coordinate order.
It remains exact-object diagonal infrastructure: the zero-head edge case,
right-basis transport, SVD/source-split construction, randomness, and computed
non-probability routine certificates are separate obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone_head_pos
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ) (hr : 0 < r)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  rcases diagonal_headTail_square_gap_of_antitone_head_pos
      sigma hr hmono with
    ⟨eta, hhead, htail⟩
  exact
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
      sigma x hx hhead htail

/-- A Euclidean orthonormal frame whose cardinality equals the ambient
coordinate dimension has coordinate-square mass one in each coordinate.

This is the zero-head companion to the LR.1dk coordinate-mass facts: when the
number of vectors equals the ambient coordinate dimension, the Bessel upper
bound is saturated coordinate by coordinate. -/
theorem orthonormal_sum_coord_sq_eq_one_of_card_eq {n q : ℕ}
    (hnq : n = q)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) (j : Fin n) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin n)) j) ^ 2) = 1 := by
  classical
  subst n
  let alpha : Fin q → ℝ :=
    fun j => ∑ c : Fin q,
      ((x c : EuclideanSpace ℝ (Fin q)) j) ^ 2
  have hle : ∀ j : Fin q, alpha j ≤ 1 := by
    intro j
    simpa [alpha] using orthonormal_sum_coord_sq_le_one x hx j
  have hdef_nonneg : ∀ j : Fin q, 0 ≤ 1 - alpha j := by
    intro j
    linarith [hle j]
  have hsum_alpha : (∑ j : Fin q, alpha j) = (q : ℝ) := by
    simpa [alpha] using orthonormal_sum_coord_sq_eq_card x hx
  have hsum_def : (∑ j : Fin q, (1 - alpha j)) = 0 := by
    calc
      (∑ j : Fin q, (1 - alpha j))
          = (∑ _j : Fin q, (1 : ℝ)) - ∑ j : Fin q, alpha j := by
            rw [Finset.sum_sub_distrib]
      _ = (q : ℝ) - (q : ℝ) := by
            simp [hsum_alpha]
      _ = 0 := by ring
  have hdef_zero : 1 - alpha j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hdef_nonneg j)).mp hsum_def j (Finset.mem_univ j)
  have halpha : alpha j = 1 := by linarith
  simpa [alpha] using halpha

/-- A full Euclidean orthonormal `q`-frame has coordinate-square mass one in
each coordinate. -/
theorem orthonormal_sum_coord_sq_eq_one_of_full {q : ℕ}
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) (j : Fin q) :
    (∑ c : Fin q,
        ((x c : EuclideanSpace ℝ (Fin q)) j) ^ 2) = 1 := by
  simpa using
    orthonormal_sum_coord_sq_eq_one_of_card_eq
      (n := q) (q := q) rfl x hx j

/-- Full-frame diagonal energy identity.

When an exact orthonormal `q`-frame fills the whole `q`-dimensional coordinate
space, the total squared action of a diagonal source matrix on the frame is
exactly the sum of its displayed diagonal squares. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_sum_sq_of_orthonormal_full
    {q : ℕ}
    (sigma : Fin q → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin q => if i = j then sigma i else 0)
            (fun j : Fin q => (x c : EuclideanSpace ℝ (Fin q)) j))) =
      ∑ j : Fin q, sigma j ^ 2 := by
  classical
  rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
  apply Finset.sum_congr rfl
  intro j _
  rw [orthonormal_sum_coord_sq_eq_one_of_full x hx j]
  ring

/-- Zero-head diagonal source-side tail-energy lower bound.

With no displayed head coordinates, an exact orthonormal `q`-frame fills the
whole right coordinate space, so the LR.1dk diagonal source action equals the
tail diagonal-square sum.  This closes the `r = 0` companion to LR.1dl; the
right-basis transport and full Ky Fan/Eckart--Young foundations remain separate
obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_zero_head
    {q : ℕ}
    (sigma : Fin q → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin q))
    (hx : Orthonormal ℝ x) :
    (∑ c : Fin q, sigma c ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin q => if i = j then sigma i else 0)
            (fun j : Fin q =>
              (x c : EuclideanSpace ℝ (Fin q)) j)) := by
  have h :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_sum_sq_of_orthonormal_full
      sigma x hx
  simpa using (le_of_eq h.symm)

/-- Combined ordered diagonal source-side tail-energy lower bound.

The positive-head branch uses the ordered last-head gap certificate LR.1dl; the
zero-head branch uses the full-frame equality LR.1dm.  Thus the ordered
diagonal lower bound no longer exposes a separate `0 < r` side condition.  This
is still exact-object diagonal infrastructure: right-basis transport, the full
Rayleigh/Ky Fan theorem, Eckart--Young, randomness, and computed
non-probability routine certificates remain separate obligations. -/
theorem sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone
    {r q : ℕ}
    (sigma : Fin (r + q) → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hcoord :
        ∀ j : Fin (0 + q),
          (∑ c : Fin q,
            ((x c : EuclideanSpace ℝ (Fin (0 + q))) j) ^ 2) = 1 := by
        intro j
        exact
          orthonormal_sum_coord_sq_eq_one_of_card_eq
            (n := 0 + q) (q := q) (by simp) x hx j
    rw [sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq]
    rw [Fin.sum_univ_add]
    simp [hcoord]
  · exact
      sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone_head_pos
        sigma hr x hx hmono

/-- Kernel-to-residual min-max adapter for the Eckart--Young route.

If the exact source block has a vector-action lower bound
`sigma * ||x||₂ <= ||A x||₂` on every nonzero vector in an `r+1` dimensional
right domain, then every repository rank-at-most-`r` competitor has Frobenius
residual at least `sigma`.  This theorem uses the LR.1cy rank-nullity kernel
vector and the local Frobenius matrix-vector domination theorem; proving the
source lower-action hypothesis from ordered singular values is a later D4
step. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    {m r : ℕ}
    (A B : Fin m → Fin (r + 1) → ℝ) {sigma : ℝ}
    (hB : RectRankAtMost m (r + 1) r B)
    (hA :
      ∀ x : Fin (r + 1) → ℝ, x ≠ 0 →
        sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x)) :
    sigma ≤ lowRankResidualFrob A B := by
  rcases rectRankAtMost_exists_rightKernelVector_succ hB with
    ⟨x, hxne, hBx⟩
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hzero
    apply hxne
    ext j
    exact (vecNorm2_eq_zero_iff x).mp hzero j
  have hxnorm_pos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  have hres_vec :
      rectMatMulVec (fun i j => A i j - B i j) x = rectMatMulVec A x :=
    rectMatMulVec_sub_eq_left_of_rightKernel A B x hBx
  have hlower :
      sigma * vecNorm2 x ≤ vecNorm2 (rectMatMulVec A x) :=
    hA x hxne
  have hupper0 :
      vecNorm2 (rectMatMulVec (fun i j => A i j - B i j) x) ≤
        frobNormRect (fun i j => A i j - B i j) * vecNorm2 x :=
    vecNorm2_rectMatMulVec_le_frobNormRect_mul
      (fun i j => A i j - B i j) x
  have hupper :
      vecNorm2 (rectMatMulVec A x) ≤
        lowRankResidualFrob A B * vecNorm2 x := by
    simpa [lowRankResidualFrob, hres_vec] using hupper0
  have hmul :
      sigma * vecNorm2 x ≤ lowRankResidualFrob A B * vecNorm2 x :=
    le_trans hlower hupper
  have hdiv :
      sigma ≤ (lowRankResidualFrob A B * vecNorm2 x) / vecNorm2 x :=
    (le_div_iff₀ hxnorm_pos).mpr hmul
  have hcancel :
      (lowRankResidualFrob A B * vecNorm2 x) / vecNorm2 x =
        lowRankResidualFrob A B := by
    field_simp [hxnorm_ne]
  simpa [hcancel] using hdiv

/-- A minimal rectangular norm-like interface for equation (9) theorem
surfaces.  This is deliberately weaker than a full unitarily invariant norm
API: it exposes only nonnegativity and the triangle step needed to turn an
exact head/tail residual certificate into a residual bound.  Concrete
unitarily invariant norm instances remain a separate foundation obligation. -/
structure RectNormLike (m n : ℕ) where
  norm : (Fin m → Fin n → ℝ) → ℝ
  norm_nonneg : ∀ A, 0 ≤ norm A
  sub_le_add : ∀ A B,
    norm (fun i j => A i j - B i j) ≤ norm A + norm B

/-- A rectangular norm-like functional with exact left and right orthogonal
invariance.  This is still certificate-shaped: it exposes the unitarily
invariant API needed by equation (9), while singular-value comparison and
Eckart--Young instantiation remain separate foundations. -/
structure UnitaryInvariantRectNormLike (m n : ℕ) extends RectNormLike m n where
  orthogonal_left : ∀ U A, IsOrthogonal m U →
    norm (matMulRectLeft U A) = norm A
  orthogonal_right : ∀ A V, IsOrthogonal n V →
    norm (matMulRectRight A V) = norm A

namespace UnitaryInvariantRectNormLike

/-- Left orthogonal invariance as a namespace theorem. -/
theorem norm_matMulRectLeft {m n : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    ξ.norm (matMulRectLeft U A) = ξ.norm A :=
  ξ.orthogonal_left U A hU

/-- Right orthogonal invariance as a namespace theorem. -/
theorem norm_matMulRectRight {m n : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    ξ.norm (matMulRectRight A V) = ξ.norm A :=
  ξ.orthogonal_right A V hV

end UnitaryInvariantRectNormLike

/-- Residual measured by a supplied rectangular norm-like functional. -/
noncomputable def lowRankResidualNorm {m n : ℕ}
    (ξ : RectNormLike m n)
    (A B : Fin m → Fin n → ℝ) : ℝ :=
  ξ.norm (fun i j => A i j - B i j)

/-- The rectangular Frobenius norm as a concrete `RectNormLike` instance.
This closes only the Frobenius instance of the norm-generic equation (9)
surface; it is not a general unitarily invariant norm API. -/
noncomputable def frobRectNormLike (m n : ℕ) : RectNormLike m n where
  norm := frobNormRect
  norm_nonneg := by
    intro A
    exact frobNormRect_nonneg A
  sub_le_add := by
    intro A B
    exact frobNormRect_sub_le A B

/-- The norm field of `frobRectNormLike` is exactly `frobNormRect`. -/
theorem frobRectNormLike_norm {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    (frobRectNormLike m n).norm A = frobNormRect A :=
  rfl

/-- The rectangular Frobenius norm as a concrete unitarily invariant
`RectNormLike` certificate. -/
noncomputable def frobUnitaryInvariantRectNormLike (m n : ℕ) :
    UnitaryInvariantRectNormLike m n where
  toRectNormLike := frobRectNormLike m n
  orthogonal_left := by
    intro U A hU
    exact frobNormRect_orthogonal_left U A hU
  orthogonal_right := by
    intro A V hV
    exact frobNormRect_orthogonal_right A V hV

/-- Forgetting the Frobenius unitarily invariant certificate recovers the
existing Frobenius `RectNormLike` instance. -/
theorem frobUnitaryInvariantRectNormLike_toRectNormLike {m n : ℕ} :
    (frobUnitaryInvariantRectNormLike m n).toRectNormLike =
      frobRectNormLike m n :=
  rfl

/-- The norm field of the Frobenius unitarily invariant certificate is exactly
the repository rectangular Frobenius norm. -/
theorem frobUnitaryInvariantRectNormLike_norm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    (frobUnitaryInvariantRectNormLike m n).norm A = frobNormRect A :=
  rfl

/-- The norm-generic residual specializes definitionally to the Frobenius
residual under `frobRectNormLike`. -/
theorem lowRankResidualNorm_frobRectNormLike {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    lowRankResidualNorm (frobRectNormLike m n) A B =
      lowRankResidualFrob A B :=
  rfl

/-- `frobRectNormLike` inherits left orthogonal invariance from the repository
rectangular Frobenius norm. -/
theorem frobRectNormLike_orthogonal_left {m n : ℕ}
    (U : Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ)
    (hU : IsOrthogonal m U) :
    (frobRectNormLike m n).norm (matMulRectLeft U A) =
      (frobRectNormLike m n).norm A := by
  exact frobNormRect_orthogonal_left U A hU

/-- `frobRectNormLike` inherits right orthogonal invariance from the repository
rectangular Frobenius norm. -/
theorem frobRectNormLike_orthogonal_right {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (V : Fin n → Fin n → ℝ)
    (hV : IsOrthogonal n V) :
    (frobRectNormLike m n).norm (matMulRectRight A V) =
      (frobRectNormLike m n).norm A := by
  exact frobNormRect_orthogonal_right A V hV

/-- A Frobenius-best rank-`k` approximation certificate.  This is intentionally
certificate-shaped: later SVD infrastructure can instantiate it, while
Algorithm 3 implementation-facing results separately account for computed bases
and projectors. -/
structure IsBestRankApproxFrob (m n k : ℕ)
    (A Ak : Fin m → Fin n → ℝ) : Prop where
  rank_le : RectRankAtMost m n k Ak
  optimal : ∀ B, RectRankAtMost m n k B →
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A B

/-- Best rank-`k` approximation certificate measured by a supplied norm-like
functional.  This is the norm-generic analogue of `IsBestRankApproxFrob`;
instantiating it from singular values/Eckart--Young for unitarily invariant
norms is still tracked separately. -/
structure IsBestRankApproxNorm (m n k : ℕ)
    (ξ : RectNormLike m n)
    (A Ak : Fin m → Fin n → ℝ) : Prop where
  rank_le : RectRankAtMost m n k Ak
  optimal : ∀ B, RectRankAtMost m n k B →
    lowRankResidualNorm ξ A Ak ≤ lowRankResidualNorm ξ A B











































































/-- The optimality field of a best rank-`k` Frobenius approximation, exposed as
a reusable theorem for downstream low-rank structural arguments. -/
theorem IsBestRankApproxFrob.residual_le_of_rankAtMost {m n k : ℕ}
    {A Ak B : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hB : RectRankAtMost m n k B) :
    lowRankResidualFrob A Ak ≤ lowRankResidualFrob A B :=
  hbest.optimal B hB

/-- The optimality field of a norm-generic best rank-`k` certificate. -/
theorem IsBestRankApproxNorm.residual_le_of_rankAtMost {m n k : ℕ}
    {ξ : RectNormLike m n}
    {A Ak B : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hB : RectRankAtMost m n k B) :
    lowRankResidualNorm ξ A Ak ≤ lowRankResidualNorm ξ A B :=
  hbest.optimal B hB

/-- A Frobenius-best rank certificate is the corresponding norm-generic
certificate for `frobRectNormLike`. -/
theorem IsBestRankApproxFrob.to_norm_frobRectNormLike {m n k : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (hbest : IsBestRankApproxFrob m n k A Ak) :
    IsBestRankApproxNorm m n k (frobRectNormLike m n) A Ak where
  rank_le := hbest.rank_le
  optimal := by
    intro B hB
    simpa [lowRankResidualNorm_frobRectNormLike]
      using hbest.optimal B hB










































































































































































































/-- Certificate that a square left multiplier factors through the columns of a
displayed rectangular matrix.  For equation (9), this is the exact-object
surface needed to say that the analysis projector `P_{A Z}` maps through the
sketch column space before introducing pseudoinverse-specific foundations. -/
structure LeftFactorThrough {m r : ℕ}
    (P : Fin m → Fin m → ℝ) (B : Fin m → Fin r → ℝ) where
  coeff : Fin r → Fin m → ℝ
  factorization : ∀ i j, P i j = ∑ a : Fin r, B i a * coeff a j







































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- A positive-definite exact head Gram remains nonsingular after adding an
exact positive-semidefinite tail Gram. -/
theorem matrix_det_ne_zero_of_posDef_add_posSemidef {r : ℕ}
    (Head Tail : Fin r → Fin r → ℝ)
    (hHead : Matrix.PosDef (Head : Matrix (Fin r) (Fin r) ℝ))
    (hTail : Matrix.PosSemidef (Tail : Matrix (Fin r) (Fin r) ℝ)) :
    Matrix.det ((fun a b => Head a b + Tail a b) :
      Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hsum :
      Matrix.PosDef
        ((Head : Matrix (Fin r) (Fin r) ℝ) +
          (Tail : Matrix (Fin r) (Fin r) ℝ)) :=
    hHead.add_posSemidef hTail
  have hdet :
      0 <
        Matrix.det
          ((Head : Matrix (Fin r) (Fin r) ℝ) +
            (Tail : Matrix (Fin r) (Fin r) ℝ)) :=
    Matrix.PosDef.det_pos hsum
  exact ne_of_gt (by simpa using hdet)












































































































































































/-- A rectangular left factor with exact orthonormal columns preserves the
squared Euclidean norm of a coefficient vector.  This is exact source-SVD
algebra; a computed left singular-vector table needs a separate certificate. -/
theorem vecNorm2Sq_leftOrthonormalFactor {m r : ℕ}
    (U : Fin m → Fin r → ℝ) (y : Fin r → ℝ)
    (hU :
      ∀ a b : Fin r, (∑ i : Fin m, U i a * U i b) = idMatrix r a b) :
    vecNorm2Sq (fun i : Fin m => ∑ a : Fin r, U i a * y a) =
      vecNorm2Sq y := by
  unfold vecNorm2Sq
  have expand : ∀ i : Fin m,
      (∑ a : Fin r, U i a * y a) ^ 2 =
        ∑ a : Fin r, ∑ b : Fin r,
          U i a * U i b * (y a * y b) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  have factor : ∀ b : Fin r,
      ∑ i : Fin m, U i a * U i b * (y a * y b) =
        (∑ i : Fin m, U i a * U i b) * (y a * y b) := by
    intro b
    rw [← Finset.sum_mul]
  simp_rw [factor, hU]
  simp [idMatrix, Finset.sum_ite_eq, Finset.mem_univ]
  ring

/-- A diagonal exact source block whose displayed diagonal entries are bounded
below by a nonnegative `sigma` expands every vector by at least `sigma` in
squared Euclidean norm.  Computed diagonal singular values require a separate
implementation-facing certificate. -/
theorem vecNorm2Sq_diagonal_lower_bound {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigmaDiag : Fin r → ℝ) {sigma : ℝ}
    (hSigma : ∀ a b, Sigma a b = if a = b then sigmaDiag a else 0)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a, sigma ≤ sigmaDiag a)
    (y : Fin r → ℝ) :
    sigma ^ 2 * vecNorm2Sq y ≤ vecNorm2Sq (matMulVec r Sigma y) := by
  have hcoord : ∀ a : Fin r,
      matMulVec r Sigma y a = sigmaDiag a * y a := by
    intro a
    unfold matMulVec
    calc
      (∑ b : Fin r, Sigma a b * y b)
          = ∑ b : Fin r, (if a = b then sigmaDiag a else 0) * y b := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hSigma a b]
      _ = sigmaDiag a * y a := by
              simp [Finset.sum_ite_eq, Finset.mem_univ]
  have hnorm :
      vecNorm2Sq (matMulVec r Sigma y) =
        ∑ a : Fin r, sigmaDiag a ^ 2 * y a ^ 2 := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro a _
    rw [hcoord a]
    ring
  calc
    sigma ^ 2 * vecNorm2Sq y
        = ∑ a : Fin r, sigma ^ 2 * y a ^ 2 := by
            unfold vecNorm2Sq
            rw [Finset.mul_sum]
    _ ≤ ∑ a : Fin r, sigmaDiag a ^ 2 * y a ^ 2 := by
            apply Finset.sum_le_sum
            intro a _
            have hsq : sigma ^ 2 ≤ sigmaDiag a ^ 2 := by
              nlinarith [hsigma_nonneg, hdiag a]
            exact mul_le_mul_of_nonneg_right hsq (sq_nonneg (y a))
    _ = vecNorm2Sq (matMulVec r Sigma y) := hnorm.symm

































































/-- Exact right-orthogonal transport preserves Euclidean inner products after
multiplication by `V^T`. -/
theorem inner_matTranspose_mulVec_eq_of_isOrthogonal {n : ℕ}
    (V : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V)
    (x y : Fin n → ℝ) :
    inner ℝ
        (WithLp.toLp 2 (matMulVec n (matTranspose V) x) :
          EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 (matMulVec n (matTranspose V) y) :
          EuclideanSpace ℝ (Fin n)) =
      inner ℝ
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) := by
  have hsum :
      (∑ i : Fin n,
          (∑ j : Fin n, V j i * y j) *
            (∑ k : Fin n, V k i * x k)) =
        ∑ j : Fin n, y j * x j := by
    calc
      (∑ i : Fin n,
          (∑ j : Fin n, V j i * y j) *
            (∑ k : Fin n, V k i * x k))
          =
            ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              (V j i * V k i) * (y j * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ =
            ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
              (V j i * V k i) * (y j * x k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
      _ =
            ∑ j : Fin n, ∑ k : Fin n,
              (∑ i : Fin n, V j i * V k i) * (y j * x k) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [← Finset.sum_mul]
      _ = ∑ j : Fin n, y j * x j := by
            simp [hV.row_orthonormal, Finset.sum_ite_eq, Finset.mem_univ]
  simpa [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
    matMulVec, matTranspose] using hsum

/-- Exact right-orthogonal transport sends an orthonormal Euclidean frame to
another orthonormal frame via multiplication by `V^T`. -/
theorem orthonormal_matTranspose_mulVec_of_isOrthogonal {n q : ℕ}
    (V : Fin n → Fin n → ℝ) (hV : IsOrthogonal n V)
    (x : Fin q → EuclideanSpace ℝ (Fin n))
    (hx : Orthonormal ℝ x) :
    Orthonormal ℝ
      (fun c : Fin q =>
        (WithLp.toLp 2
          (matMulVec n (matTranspose V)
            (fun j : Fin n =>
              (x c : EuclideanSpace ℝ (Fin n)) j)) :
          EuclideanSpace ℝ (Fin n))) := by
  rw [orthonormal_iff_ite] at hx ⊢
  intro c d
  have hinner :=
    inner_matTranspose_mulVec_eq_of_isOrthogonal V hV
      (fun j : Fin n => (x c : EuclideanSpace ℝ (Fin n)) j)
      (fun j : Fin n => (x d : EuclideanSpace ℝ (Fin n)) j)
  simpa using hinner.trans (hx c d)






















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- A displayed diagonal source singular-value block is nonsingular when all
displayed diagonal entries are nonzero.  This is exact source-SVD algebra; a
computed singular-value routine must separately certify its rounded diagonal
entries and any perturbation radius. -/
theorem matrix_det_ne_zero_of_eq_diagonal_nonzero
    {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hdiag : ∀ a, sigma a ≠ 0) :
    Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hmat :
      (Sigma : Matrix (Fin r) (Fin r) ℝ) = Matrix.diagonal sigma := by
    ext a b
    rw [hSigma a b]
    simp [Matrix.diagonal_apply]
  rw [hmat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (by
    intro a _
    exact hdiag a)

/-- Positive displayed diagonal singular values give the determinant
hypothesis consumed by the exact source determinant route. -/
theorem matrix_det_ne_zero_of_eq_diagonal_pos
    {r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hpos : ∀ a, 0 < sigma a) :
    Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  matrix_det_ne_zero_of_eq_diagonal_nonzero Sigma sigma hSigma
    (by
      intro a
      exact ne_of_gt (hpos a))













































































































namespace DiagonalSourceSVDTailCertificate



































end DiagonalSourceSVDTailCertificate


























































































































































































































































































































































































































































































































































































































































/-- Squared Frobenius norm is preserved by left multiplication with a
rectangular matrix whose columns are exactly orthonormal.  This is the
rectangular-tail analogue of square orthogonal invariance used in the source
equation (9) route. -/
theorem frobNormSqRect_leftOrthonormalFactor
    {m q n : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b) :
    frobNormSqRect (fun i j => ∑ a : Fin q, U i a * C a j) =
      frobNormSqRect C := by
  unfold frobNormSqRect
  calc
    (∑ i : Fin m, ∑ j : Fin n, (∑ a : Fin q, U i a * C a j) ^ 2)
        =
          ∑ j : Fin n, ∑ i : Fin m, (∑ a : Fin q, U i a * C a j) ^ 2 := by
            rw [Finset.sum_comm]
    _ =
          ∑ j : Fin n, ∑ a : Fin q, C a j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            calc
              (∑ i : Fin m, (∑ a : Fin q, U i a * C a j) ^ 2)
                  =
                    ∑ i : Fin m, ∑ a : Fin q, ∑ b : Fin q,
                      (U i a * C a j) * (U i b * C b j) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [sq, Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.mul_sum]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q, ∑ i : Fin m,
                      (U i a * C a j) * (U i b * C b j) := by
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.sum_comm]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q,
                      (∑ i : Fin m, U i a * U i b) * (C a j * C b j) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      apply Finset.sum_congr rfl
                      intro b _
                      calc
                        (∑ i : Fin m, (U i a * C a j) * (U i b * C b j))
                            =
                              ∑ i : Fin m,
                                (U i a * U i b) * (C a j * C b j) := by
                                apply Finset.sum_congr rfl
                                intro i _
                                ring
                        _ =
                              (∑ i : Fin m, U i a * U i b) *
                                (C a j * C b j) := by
                                rw [Finset.sum_mul]
              _ =
                    ∑ a : Fin q, ∑ b : Fin q,
                      idMatrix q a b * (C a j * C b j) := by
                      apply Finset.sum_congr rfl
                      intro a _
                      apply Finset.sum_congr rfl
                      intro b _
                      rw [hU a b]
              _ = ∑ a : Fin q, C a j ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro a _
                      simp [idMatrix, Finset.mem_univ]
                      ring
    _ =
          ∑ a : Fin q, ∑ j : Fin n, C a j ^ 2 := by
            rw [Finset.sum_comm]

/-- Frobenius norm is preserved by left multiplication with a rectangular
matrix whose columns are exactly orthonormal. -/
theorem frobNormRect_leftOrthonormalFactor
    {m q n : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b) :
    frobNormRect (fun i j => ∑ a : Fin q, U i a * C a j) =
      frobNormRect C := by
  unfold frobNormRect
  rw [frobNormSqRect_leftOrthonormalFactor U C hU]































































































































































































































































































































































































































































































































































































































































































































/-- Concatenate the exact right-tail and right-head bases as a single
sum-indexed right-basis block.  The left summand is `Vperp`; the right summand
is `V`. -/
noncomputable def rightBasisBlock {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin n → (Fin q ⊕ Fin r) → ℝ :=
  fun j bc =>
    match bc with
    | Sum.inl c => Vperp j c
    | Sum.inr b => V j b

/-- Row orthonormality of the concatenated right-basis block from the explicit
tail/head row-completeness identity. -/
theorem rightBasisBlock_row_orthonormal_of_sum
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    ∀ j k,
      ∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc =
      idMatrix n j k := by
  intro j k
  unfold rightBasisBlock
  rw [Fintype.sum_sum_type]
  simpa using hcomplete j k

/-- Component right-basis orthonormality fields assemble the column
orthonormality certificate for the concatenated block `[Vperp,V]`.  This is an
exact source-SVD bridge: constructing or computing the component bases remains
a separate non-probability obligation. -/
theorem rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0 := by
  intro bc bd
  cases bc with
  | inl a =>
      cases bd with
      | inl c =>
          simpa [rightBasisBlock, idMatrix] using hVperp a c
      | inr c =>
          simpa [rightBasisBlock] using hcrossHead a c
  | inr b =>
      cases bd with
      | inl c =>
          simpa [rightBasisBlock] using hcrossTail b c
      | inr c =>
          simpa [rightBasisBlock, idMatrix] using hV b c

/-- Component right-basis fields plus the row-completeness identity assemble
both orthonormality certificates for the concatenated block `[Vperp,V]`. -/
theorem rightBasisBlock_col_row_orthonormal_of_component_fields
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    (∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0) ∧
      (∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k) := by
  constructor
  · exact
      rightBasisBlock_col_orthonormal_of_component_orthonormal_fields
        Vperp V hVperp hcrossTail hcrossHead hV
  · exact rightBasisBlock_row_orthonormal_of_sum Vperp V hcomplete

/-- Column orthonormality of the concatenated right-basis block
`[Vperp,V]` implies all component right-basis fields used by the source-tail
residual block algebra.  This is an exact source-SVD block certificate; a
computed basis routine must separately certify its rounded basis columns. -/
theorem rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hcols :
      ∀ bc bd : Fin q ⊕ Fin r,
        (∑ j : Fin n,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
          if bc = bd then 1 else 0) :
    (∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c) ∧
      (∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) ∧
      (∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0) ∧
      (∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) := by
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inl c)
    simpa [rightBasisBlock, idMatrix] using h
  constructor
  · intro b c
    have h := hcols (Sum.inr b) (Sum.inl c)
    simpa [rightBasisBlock] using h
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inr c)
    simpa [rightBasisBlock] using h
  · intro b c
    have h := hcols (Sum.inr b) (Sum.inr c)
    simpa [rightBasisBlock, idMatrix] using h

/-- Row orthonormality of the concatenated right-basis block is exactly the
tail-plus-head row-completeness identity consumed by the source-tail Frobenius
block identity. -/
theorem rightBasisBlock_complete_sum_of_row_orthonormal
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (V : Fin n → Fin r → ℝ)
    (hrows :
      ∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k) :
    ∀ j k,
      (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k := by
  intro j k
  have h := hrows j k
  simpa [rightBasisBlock, Fintype.sum_sum_type] using h
































































































































































































/-- The singular-value-weighted right-tail residual block
`[Sigma, -Sigma M]`. -/
noncomputable def sigmaRightResidualBlock {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ) :
    Fin q → (Fin q ⊕ Fin r) → ℝ :=
  fun a bc =>
    match bc with
    | Sum.inl c => Sigma a c
    | Sum.inr c => -matMulRectLeft Sigma M a c

/-- The squared Frobenius norm of `[Sigma, -Sigma M]` splits into the source
tail squared norm and the squared norm of the inverse-cross term. -/
theorem finiteFrobNormSq_sigmaRightResidualBlock
    {q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (M : Fin q → Fin r → ℝ) :
    finiteFrobNormSq (sigmaRightResidualBlock Sigma M) =
      frobNormSq Sigma + frobNormSqRect (matMulRectLeft Sigma M) := by
  unfold finiteFrobNormSq sigmaRightResidualBlock frobNormSq frobNormSqRect
  calc
    (∑ a : Fin q,
        ∑ bc : Fin q ⊕ Fin r,
          (match bc with
          | Sum.inl c => Sigma a c
          | Sum.inr c => -matMulRectLeft Sigma M a c) ^ 2)
        =
          ∑ a : Fin q,
            ((∑ c : Fin q, Sigma a c ^ 2) +
              (∑ c : Fin r, (-matMulRectLeft Sigma M a c) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Fintype.sum_sum_type]
    _ =
          (∑ a : Fin q, ∑ c : Fin q, Sigma a c ^ 2) +
            (∑ a : Fin q, ∑ c : Fin r,
              matMulRectLeft Sigma M a c ^ 2) := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro c _
            ring















































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- A nonsingular square real factor has a positive-definite normal Gram
`RᵀR`.  This is the positive-definiteness version of the determinant bridge
used in the equation (9) source-head route. -/
theorem matrix_transpose_mul_self_posDef_of_det_ne_zero {r : ℕ}
    (R : Matrix (Fin r) (Fin r) ℝ)
    (hdet : Matrix.det R ≠ 0) :
    Matrix.PosDef (R.transpose * R) := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa using Matrix.isHermitian_conjTranspose_mul_self R
  · intro x hx
    have hRx : Matrix.mulVec R x ≠ 0 := by
      intro hzero
      exact hx (Matrix.eq_zero_of_mulVec_eq_zero hdet hzero)
    have hquad :
        star x ⬝ᵥ Matrix.mulVec (R.transpose * R) x =
          Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
      calc
        star x ⬝ᵥ Matrix.mulVec (R.transpose * R) x
            = star x ⬝ᵥ Matrix.mulVec R.transpose (Matrix.mulVec R x) := by
                rw [← Matrix.mulVec_mulVec]
        _ = Matrix.vecMul (star x) R.transpose ⬝ᵥ Matrix.mulVec R x := by
                rw [Matrix.dotProduct_mulVec]
        _ = Matrix.mulVec R (star x) ⬝ᵥ Matrix.mulVec R x := by
                rw [Matrix.vecMul_transpose]
        _ = Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
                simp
    have hnonneg : 0 ≤ Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x := by
      unfold dotProduct
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((Matrix.mulVec R x) i)
    have hne : Matrix.mulVec R x ⬝ᵥ Matrix.mulVec R x ≠ 0 := by
      intro hzero
      exact hRx (dotProduct_self_eq_zero.mp hzero)
    exact hquad.symm ▸ lt_of_le_of_ne hnonneg hne.symm


































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Concatenate the exact left-head and left-tail bases as a single
sum-indexed left-basis block.  The left summand is the source head basis `U`;
the right summand is the tail basis `Utail`. -/
noncomputable def leftBasisBlock {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ) :
    Fin m → (Fin r ⊕ Fin q) → ℝ :=
  fun i bc =>
    match bc with
    | Sum.inl a => U i a
    | Sum.inr c => Utail i c

/-- Column orthonormality of the concatenated left-basis block `[U,Utail]`
implies the component source-head orthonormality, head-tail cross
orthogonality, and tail orthonormality fields consumed by
`DiagonalSourceSVDTailCertificate`.  This is exact SVD-block algebra; computed
left singular-vector tables remain separate non-probability obligations. -/
theorem leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
    {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hcols :
      ∀ bc bd : Fin r ⊕ Fin q,
        (∑ i : Fin m,
          leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
          if bc = bd then 1 else 0) :
    (∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b) ∧
      (∀ a c, ∑ i : Fin m, U i a * Utail i c = 0) ∧
      (∀ a c, ∑ i : Fin m, Utail i a * Utail i c = idMatrix q a c) := by
  constructor
  · intro a b
    have h := hcols (Sum.inl a) (Sum.inl b)
    simpa [leftBasisBlock, idMatrix] using h
  constructor
  · intro a c
    have h := hcols (Sum.inl a) (Sum.inr c)
    simpa [leftBasisBlock] using h
  · intro a c
    have h := hcols (Sum.inr a) (Sum.inr c)
    simpa [leftBasisBlock, idMatrix] using h

/-- Component left-basis fields assemble the column orthonormality certificate
for the concatenated block `[U,Utail]`.  This is exact source-SVD algebra:
constructing the tail-left completion or computing singular-vector tables
remains a separate non-probability obligation. -/
theorem leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
    {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hUtail : ∀ a c, ∑ i : Fin m, Utail i a * Utail i c = idMatrix q a c) :
    ∀ bc bd : Fin r ⊕ Fin q,
      (∑ i : Fin m,
        leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
        if bc = bd then 1 else 0 := by
  intro bc bd
  cases bc with
  | inl a =>
      cases bd with
      | inl b =>
          simpa [leftBasisBlock, idMatrix] using hU a b
      | inr c =>
          simpa [leftBasisBlock] using hcross a c
  | inr c =>
      cases bd with
      | inl a =>
          calc
            (∑ i : Fin m,
              leftBasisBlock U Utail i (Sum.inr c) *
                leftBasisBlock U Utail i (Sum.inl a))
                =
                  ∑ i : Fin m, U i a * Utail i c := by
                    apply Finset.sum_congr rfl
                    intro i _
                    simp [leftBasisBlock]
                    ring
            _ = 0 := hcross a c
      | inr d =>
          simpa [leftBasisBlock, idMatrix] using hUtail c d

/-- A sum-indexed column-orthonormal family in `ℝ^m` has no more columns than
ambient rows.  This bridges the repository's raw finite-sum convention to
mathlib's `Orthonormal`/`LinearIndependent` dimension theorem. -/
theorem colOrthonormal_fintype_card_le_rows {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : Fin m → ι → ℝ)
    (hX : ∀ a b : ι,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0) :
    Fintype.card ι ≤ m := by
  let v : ι → EuclideanSpace ℝ (Fin m) :=
    fun a => WithLp.toLp 2 (fun i : Fin m => X i a)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := hX a b
    unfold v
    rw [PiLp.inner_apply]
    simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h
  have hli : LinearIndependent ℝ v := hv.linearIndependent
  have hcard := hli.fintype_card_le_finrank
  simpa using hcard

/-- A concatenated left block `[U,Utail]` with column orthonormality forces the
visible dimension condition `r+q <= m`.  Thus any full left-block
nullspace-completion route for equation (9) must either expose this tall/thin
condition or use a different rectangular SVD surface. -/
theorem leftBasisBlock_col_orthonormal_card_le_rows {m r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Utail : Fin m → Fin q → ℝ)
    (hcols :
      ∀ bc bd : Fin r ⊕ Fin q,
        (∑ i : Fin m,
          leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
          if bc = bd then 1 else 0) :
    r + q ≤ m := by
  have h :=
    colOrthonormal_fintype_card_le_rows
      (X := fun i bc => leftBasisBlock U Utail i bc) hcols
  simpa using h

/-- A partially specified family of raw column-orthonormal columns in `ℝ^m`
can be extended to a full `m × m` column-orthonormal table while preserving the
specified columns.

This is the finite-dimensional orthonormal-completion bridge needed by the
zero-tail replacement route for equation (9).  It is exact-object
infrastructure: it constructs no floating-point routine and charges no
probability-law error. -/
theorem partialColOrthonormal_exists_fullColOrthonormal {m : ℕ}
    (X : Fin m → Fin m → ℝ) (s : Set (Fin m))
    (hX : ∀ a b : s,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0) :
    ∃ Y : Fin m → Fin m → ℝ,
      (∀ a : Fin m, a ∈ s → ∀ i : Fin m, Y i a = X i a) ∧
        ∀ a b : Fin m,
          (∑ i : Fin m, Y i a * Y i b) = if a = b then 1 else 0 := by
  classical
  let v : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun a => WithLp.toLp 2 (fun i : Fin m => X i a)
  have hv : Orthonormal ℝ (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro a b
    have h := hX a b
    unfold v
    rw [PiLp.inner_apply]
    simpa [Set.restrict, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h
  have hcard :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Fintype.card (Fin m) := by
    simp
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (v := v) (s := s) hcard
  refine ⟨fun i a => b a i, ?_, ?_⟩
  · intro a ha i
    have h := hb a ha
    change b a i = X i a
    simpa [v] using congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) h
  · intro a c
    have h := b.inner_eq_ite a c
    rw [PiLp.inner_apply] at h
    simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm] using h

/-- Embedded block-column version of
`partialColOrthonormal_exists_fullColOrthonormal`.

If the head columns and any chosen tail columns of `[U,Utail₀]` are already a
partial orthonormal family, and the block indices embed into a full `Fin m`
coordinate set, then the unspecified tail columns can be replaced so that the
whole block `[U,Utail]` is column-orthonormal.  The replacement preserves every
tail column included in the partial set.

This is exact-object nullspace-completion infrastructure for equation (9).  It
does not yet instantiate the ordered right-Gram zero-tail set, prove
Eckart--Young, derive randomness certificates, or certify any computed
non-probability routine. -/
theorem partialLeftBasisBlock_exists_replacement_tail
    {m r q : ℕ}
    (e : Fin r ⊕ Fin q ↪ Fin m)
    (U : Fin m → Fin r → ℝ) (Utail₀ : Fin m → Fin q → ℝ)
    (s : Set (Fin r ⊕ Fin q))
    (hhead : ∀ a : Fin r, Sum.inl a ∈ s)
    (hpartial : ∀ a b : s,
      (∑ i : Fin m,
        leftBasisBlock U Utail₀ i a * leftBasisBlock U Utail₀ i b) =
        if a = b then 1 else 0) :
    ∃ Utail : Fin m → Fin q → ℝ,
      (∀ c : Fin q, Sum.inr c ∈ s → ∀ i : Fin m, Utail i c = Utail₀ i c) ∧
        ∀ bc bd : Fin r ⊕ Fin q,
          (∑ i : Fin m,
            leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
            if bc = bd then 1 else 0 := by
  classical
  let blockCol : Fin r ⊕ Fin q → Fin m → ℝ :=
    fun bc i => leftBasisBlock U Utail₀ i bc
  let X : Fin m → Fin m → ℝ :=
    fun i a =>
      if ha : a ∈ Set.range (fun bc : Fin r ⊕ Fin q => e bc) then
        blockCol (Classical.choose ha) i
      else
        0
  let sFull : Set (Fin m) :=
    Set.image (fun bc : Fin r ⊕ Fin q => e bc) s
  have hX : ∀ a b : sFull,
      (∑ i : Fin m, X i a * X i b) = if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨bc, hbc, hbc_eq⟩
    rcases b.2 with ⟨bd, hbd, hbd_eq⟩
    have hmem_a : (a : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bc, hbc_eq⟩
    have hmem_b : (b : Fin m) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨bd, hbd_eq⟩
    have hchoose_a : Classical.choose hmem_a = bc :=
      e.injective (by
        calc
          e (Classical.choose hmem_a) = (a : Fin m) :=
            Classical.choose_spec hmem_a
          _ = e bc := hbc_eq.symm)
    have hchoose_b : Classical.choose hmem_b = bd :=
      e.injective (by
        calc
          e (Classical.choose hmem_b) = (b : Fin m) :=
            Classical.choose_spec hmem_b
          _ = e bd := hbd_eq.symm)
    have h := hpartial ⟨bc, hbc⟩ ⟨bd, hbd⟩
    have hsum :
        (∑ i : Fin m, X i a * X i b) =
          ∑ i : Fin m,
            leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := by
      apply Finset.sum_congr rfl
      intro i _
      have hXa : X i a = leftBasisBlock U Utail₀ i bc := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_a]
        simp [hchoose_a]
      have hXb : X i b = leftBasisBlock U Utail₀ i bd := by
        dsimp [X, blockCol]
        rw [dif_pos hmem_b]
        simp [hchoose_b]
      rw [hXa, hXb]
    have hite_s :
        (if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then (1 : ℝ) else 0) =
          if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        simp
      · have hne : (⟨bc, hbc⟩ : s) ≠ (⟨bd, hbd⟩ : s) := by
          intro hEq
          exact hbdc (Subtype.ext_iff.mp hEq)
        simp [hbdc, hne]
    have hite_full : (if a = b then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbdc : bc = bd
      · subst hbdc
        have hab : a = b := by
          apply Subtype.ext
          calc
            (a : Fin m) = e bc := hbc_eq.symm
            _ = (b : Fin m) := hbd_eq
        simp [hab]
      · have hne :
          a ≠ b := by
          intro hEq
          apply hbdc
          apply e.injective
          calc
            e bc = (a : Fin m) := hbc_eq
            _ = (b : Fin m) := congrArg Subtype.val hEq
            _ = e bd := hbd_eq.symm
        simp [hbdc, hne]
    calc
      (∑ i : Fin m, X i a * X i b)
          = ∑ i : Fin m,
              leftBasisBlock U Utail₀ i bc * leftBasisBlock U Utail₀ i bd := hsum
      _ = if (⟨bc, hbc⟩ : s) = (⟨bd, hbd⟩ : s) then 1 else 0 := h
      _ = if bc = bd then 1 else 0 := hite_s
      _ = if a = b then 1 else 0 := hite_full.symm
  obtain ⟨Y, hYspec, hYcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X sFull hX
  refine ⟨fun i c => Y i (e (Sum.inr c)), ?_, ?_⟩
  · intro c hc i
    have hmem : e (Sum.inr c) ∈ sFull := ⟨Sum.inr c, hc, rfl⟩
    have hrange : e (Sum.inr c) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
      ⟨Sum.inr c, rfl⟩
    have hchoose : Classical.choose hrange = Sum.inr c :=
      e.injective (Classical.choose_spec hrange)
    simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using
      hYspec (e (Sum.inr c)) hmem i
  · intro bc bd
    have hrewrite_left :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc) =
          fun i : Fin m => Y i (e bc) := by
      funext i
      cases bc with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hrewrite_right :
        (fun i : Fin m => leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd) =
          fun i : Fin m => Y i (e bd) := by
      funext i
      cases bd with
      | inl a =>
          have hmem : e (Sum.inl a) ∈ sFull := ⟨Sum.inl a, hhead a, rfl⟩
          have hrange : e (Sum.inl a) ∈ Set.range (fun x : Fin r ⊕ Fin q => e x) :=
            ⟨Sum.inl a, rfl⟩
          have hchoose : Classical.choose hrange = Sum.inl a :=
            e.injective (Classical.choose_spec hrange)
          have h := hYspec (e (Sum.inl a)) hmem i
          simpa [X, blockCol, leftBasisBlock, hrange, hchoose] using h.symm
      | inr _ =>
          rfl
    have hcols := hYcols (e bc) (e bd)
    have hite : (if e bc = e bd then (1 : ℝ) else 0) =
        if bc = bd then 1 else 0 := by
      by_cases hbc : bc = bd
      · subst hbc
        simp
      · have hne : e bc ≠ e bd := fun h => hbc (e.injective h)
        simp [hbc, hne]
    calc
      (∑ i : Fin m,
        leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bc *
          leftBasisBlock U (fun i c => Y i (e (Sum.inr c))) i bd)
          = ∑ i : Fin m, Y i (e bc) * Y i (e bd) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [congr_fun hrewrite_left i, congr_fun hrewrite_right i]
      _ = if e bc = e bd then 1 else 0 := hcols
      _ = if bc = bd then 1 else 0 := hite













































namespace BlockDiagonalSourceSVDTailCertificate


































































































































































































































































































































































































































































end BlockDiagonalSourceSVDTailCertificate






































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Squared Frobenius norm of the displayed tail diagonal equals the sum of
the displayed tail singular-value squares.

This is exact-object diagonal algebra for the multi-tail equation-(9)
Eckart--Young route; computed singular values require a separate
non-probability routine certificate. -/
theorem frobNormSq_diagonal_eq_sum {q : ℕ}
    (sigma : Fin q → ℝ) :
    frobNormSq (fun c d : Fin q => if c = d then sigma c else 0) =
      ∑ c : Fin q, sigma c ^ 2 := by
  unfold frobNormSq
  apply Finset.sum_congr rfl
  intro c _
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- Norm form of `frobNormSq_diagonal_eq_sum`. -/
theorem frobNorm_diagonal_eq_sqrt_sum {q : ℕ}
    (sigma : Fin q → ℝ) :
    frobNorm (fun c d : Fin q => if c = d then sigma c else 0) =
      Real.sqrt (∑ c : Fin q, sigma c ^ 2) := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSq_diagonal_eq_sum]












































































































































































































































































































































































































































































































































































































































































































































/-- Scalar relative-comparison expansion.

If the displayed scalar rate `2 * sqrt (1 + eps^2)` is at most `rho`, then
multiplying by any nonnegative tail norm gives the product-form comparison
used by the equation-(9) relative surfaces. -/
theorem two_sqrt_one_add_sq_mul_tail_le_of_scalar
    {eps rho tail : ℝ}
    (hscalar : 2 * Real.sqrt (1 + eps ^ 2) ≤ rho)
    (htail : 0 ≤ tail) :
    2 * (Real.sqrt (1 + eps ^ 2) * tail) ≤ rho * tail := by
  calc
    2 * (Real.sqrt (1 + eps ^ 2) * tail)
        = (2 * Real.sqrt (1 + eps ^ 2)) * tail := by
          ring
    _ ≤ rho * tail :=
        mul_le_mul_of_nonneg_right hscalar htail































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
