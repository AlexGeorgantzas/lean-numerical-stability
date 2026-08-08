import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.Doolittle
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Equation09.LowRankApproximation.Endpoints

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.LowRankApprox`; the historical path re-exports this module.
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

















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace UnitaryInvariantRectNormLike

















end UnitaryInvariantRectNormLike











































































































































































































































































































































































































































































/-- Certificate-shaped exact residual surface for the source equation (9).
The terms `tail` and `coupling` stand for the exact analysis quantities
`||Σ_{k,⊥}||` and `||Σ_{k,⊥}(V_{k,⊥}ᵀ Z)(V_kᵀ Z)^+||` after choosing a
concrete norm route.  This structure records the inequality without pretending
that the repository has already built the rectangular SVD, pseudoinverse, or
unitarily invariant norm infrastructure needed to instantiate it. -/
structure Equation9ResidualCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling : ℝ) : Prop where
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  residual_bound :
    lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling

/-- Norm-generic exact residual surface for source equation (9).  The supplied
functional `ξ` may later be instantiated by a concrete unitarily invariant norm,
but this theorem surface only assumes the explicit norm-like fields in
`RectNormLike`. -/
structure Equation9ResidualNormCertificate {m n : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling : ℝ) : Prop where
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  residual_bound :
    lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling

/-- Head/tail decomposition certificate for equation (9).

This exposes the exact algebra hidden in the source proof before the remaining
rectangular-SVD and pseudoinverse foundations are available: `A = Head + Tail`,
the head lies in the exact sketch column space, and the tail plus projected-tail
Frobenius norms are bounded by the displayed radii. -/
structure Equation9HeadTailSketchCertificate {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ)
    (tail coupling : ℝ) where
  split : ∀ i j, A i j = Head i j + Tail i j
  head_factor : ColumnSketchHeadFactorization A Z Head
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  tail_bound : frobNormRect Tail ≤ tail
  coupling_bound : frobNormRect (preconditionRows P_AZ Tail) ≤ coupling

/-- Norm-generic head/tail decomposition certificate for equation (9).  It is
the same exact head-in-sketch algebra as `Equation9HeadTailSketchCertificate`,
but the two visible analytic bounds are measured by a supplied norm-like
functional. -/
structure Equation9HeadTailSketchNormCertificate {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ)
    (tail coupling : ℝ) where
  split : ∀ i j, A i j = Head i j + Tail i j
  head_factor : ColumnSketchHeadFactorization A Z Head
  tail_nonneg : 0 ≤ tail
  coupling_nonneg : 0 ≤ coupling
  tail_bound : ξ.norm Tail ≤ tail
  coupling_bound : ξ.norm (preconditionRows P_AZ Tail) ≤ coupling

/-- A Frobenius equation-(9) residual certificate is the norm-generic
certificate for `frobRectNormLike`. -/
theorem Equation9ResidualCertificate.to_norm_frobRectNormLike {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualCertificate A P_AZ tail coupling) :
    Equation9ResidualNormCertificate (frobRectNormLike m n)
      A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    simpa [lowRankResidualNorm_frobRectNormLike]
      using h.residual_bound

/-- A Frobenius head/tail sketch certificate is the norm-generic head/tail
certificate for `frobRectNormLike`. -/
def Equation9HeadTailSketchCertificate.to_norm_frobRectNormLike
    {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    Equation9HeadTailSketchNormCertificate (frobRectNormLike m n)
      A Z P_AZ Head Tail tail coupling where
  split := h.split
  head_factor := h.head_factor
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  tail_bound := by
    simpa [frobRectNormLike] using h.tail_bound
  coupling_bound := by
    simpa [frobRectNormLike] using h.coupling_bound

/-- A head/tail sketch certificate and sketch reproduction instantiate the
equation (9) residual certificate. -/
theorem Equation9HeadTailSketchCertificate.to_residualCertificate {m n r : ℕ}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a) :
    Equation9ResidualCertificate A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    have hHead :
        ∀ i j, preconditionRows P_AZ Head i j = Head i j :=
      preconditionRows_reproduces_head_of_columnSketchHeadFactorization
        A Z P_AZ Head hrepr h.head_factor
    have hPA :
        ∀ i j,
          preconditionRows P_AZ A i j =
            preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
      intro i j
      calc
        preconditionRows P_AZ A i j
            = ∑ k : Fin m, P_AZ i k * (Head k j + Tail k j) := by
                unfold preconditionRows
                apply Finset.sum_congr rfl
                intro k _
                rw [h.split k j]
        _ = ∑ k : Fin m,
              (P_AZ i k * Head k j + P_AZ i k * Tail k j) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = (∑ k : Fin m, P_AZ i k * Head k j) +
              (∑ k : Fin m, P_AZ i k * Tail k j) := by
                rw [Finset.sum_add_distrib]
        _ = preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
                rfl
    have hres :
        (fun i j => A i j - preconditionRows P_AZ A i j) =
          (fun i j => Tail i j - preconditionRows P_AZ Tail i j) := by
      funext i
      funext j
      rw [h.split i j, hPA i j, hHead i j]
      ring
    unfold lowRankResidualFrob
    rw [hres]
    exact le_trans (frobNormRect_sub_le Tail (preconditionRows P_AZ Tail))
      (add_le_add h.tail_bound h.coupling_bound)

/-- A norm-generic head/tail sketch certificate and sketch reproduction
instantiate the norm-generic equation (9) residual certificate.  Only the
triangle field of `RectNormLike` is used here; unitarily invariant norm
invariance and singular-value comparisons are intentionally not hidden in this
adapter. -/
theorem Equation9HeadTailSketchNormCertificate.to_residualNormCertificate
    {m n r : ℕ}
    {ξ : RectNormLike m n}
    {A : Fin m → Fin n → ℝ} {Z : Fin n → Fin r → ℝ}
    {P_AZ : Fin m → Fin m → ℝ} {Head Tail : Fin m → Fin n → ℝ}
    {tail coupling : ℝ}
    (h : Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling)
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a) :
    Equation9ResidualNormCertificate ξ A P_AZ tail coupling where
  tail_nonneg := h.tail_nonneg
  coupling_nonneg := h.coupling_nonneg
  residual_bound := by
    have hHead :
        ∀ i j, preconditionRows P_AZ Head i j = Head i j :=
      preconditionRows_reproduces_head_of_columnSketchHeadFactorization
        A Z P_AZ Head hrepr h.head_factor
    have hPA :
        ∀ i j,
          preconditionRows P_AZ A i j =
            preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
      intro i j
      calc
        preconditionRows P_AZ A i j
            = ∑ k : Fin m, P_AZ i k * (Head k j + Tail k j) := by
                unfold preconditionRows
                apply Finset.sum_congr rfl
                intro k _
                rw [h.split k j]
        _ = ∑ k : Fin m,
              (P_AZ i k * Head k j + P_AZ i k * Tail k j) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = (∑ k : Fin m, P_AZ i k * Head k j) +
              (∑ k : Fin m, P_AZ i k * Tail k j) := by
                rw [Finset.sum_add_distrib]
        _ = preconditionRows P_AZ Head i j + preconditionRows P_AZ Tail i j := by
                rfl
    have hres :
        (fun i j => A i j - preconditionRows P_AZ A i j) =
          (fun i j => Tail i j - preconditionRows P_AZ Tail i j) := by
      funext i
      funext j
      rw [h.split i j, hPA i j, hHead i j]
      ring
    unfold lowRankResidualNorm
    rw [hres]
    exact le_trans (ξ.sub_le_add Tail (preconditionRows P_AZ Tail))
      (add_le_add h.tail_bound h.coupling_bound)

/-- The canonical head/tail pair from a displayed coefficient table `W`
instantiates the head/tail sketch certificate once the two exact norm bounds
are supplied. -/
noncomputable def equation9HeadTailSketchCertificate_of_columnSketchHead
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling : ℝ)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (columnSketchTail A Z W)) ≤ coupling) :
    Equation9HeadTailSketchCertificate A Z P_AZ
      (columnSketchHead A Z W) (columnSketchTail A Z W) tail coupling where
  split := columnSketchHeadTail_split A Z W
  head_factor := columnSketchHead_headFactorization A Z W
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- The right-hand side in an equation (9) residual certificate is nonnegative. -/
theorem Equation9ResidualCertificate.tail_add_coupling_nonneg {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualCertificate A P_AZ tail coupling) :
    0 ≤ tail + coupling :=
  add_nonneg h.tail_nonneg h.coupling_nonneg

/-- The right-hand side in a norm-generic equation (9) residual certificate is
nonnegative. -/
theorem Equation9ResidualNormCertificate.tail_add_coupling_nonneg {m n : ℕ}
    {ξ : RectNormLike m n}
    {A : Fin m → Fin n → ℝ} {P_AZ : Fin m → Fin m → ℝ}
    {tail coupling : ℝ}
    (h : Equation9ResidualNormCertificate ξ A P_AZ tail coupling) :
    0 ≤ tail + coupling :=
  add_nonneg h.tail_nonneg h.coupling_nonneg

/-- Exact equation (9) rank/residual surface: a supplied column-sketch projector
factorization and a supplied residual certificate imply that `P_AZ A` is a
rank-`r` candidate with the displayed equation (9) residual bound. -/
theorem equation9RankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualCertificate A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  ⟨sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP, hEq9.residual_bound⟩

/-- Norm-generic equation (9) rank/residual surface.  This proves the algebraic
rank and residual wrapper for any supplied `RectNormLike`; proving that a
specific unitarily invariant norm supplies the required head/tail bounds is a
separate foundation. -/
theorem equation9RankResidualNormSurface {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualNormCertificate ξ A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling :=
  ⟨sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP, hEq9.residual_bound⟩

/-- Rank/residual surface from the explicit head/tail sketch certificate. -/
theorem equation9HeadTailSketchRankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9RankResidualSurface A Z P_AZ tail coupling hP
    (hHT.to_residualCertificate hrepr)

/-- The arbitrary selected right-Gram head/tail split instantiates the
equation-(9) head/tail sketch certificate for the selected eigenvector sketch,
once the exact tail and projected-tail coupling bounds are supplied. -/
noncomputable def equation9HeadTailSketchCertificate_of_rectRightGramBasisSVDHead
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    Equation9HeadTailSketchCertificate A (rectRightGramBasisSketchMatrix A s)
      P_AZ (rectRightGramBasisSVDHead A s) (rectRightGramBasisSVDTail A s)
      tail coupling where
  split := rectRightGramBasisSVD_head_tail_entry A s
  head_factor := rectRightGramBasisSVDHead_columnSketchHeadFactorization A s
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- Selected right-Gram equation-(9) rank/residual surface: if the exact
selected-sketch multiplier factors through and reproduces the selected sketch
columns, and if the selected tail and projected-tail coupling are bounded by
the displayed radii, then the exact projector candidate has rank at most
`|s|` and residual at most `tail + coupling`. -/
theorem equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A (rectRightGramBasisSketchMatrix A s)))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A (rectRightGramBasisSketchMatrix A s)) i a =
          columnSketch A (rectRightGramBasisSketchMatrix A s) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    RectRankAtMost m n s.card (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface A
    (rectRightGramBasisSketchMatrix A s) P_AZ
    (rectRightGramBasisSVDHead A s) (rectRightGramBasisSVDTail A s)
    tail coupling hP hrepr
    (equation9HeadTailSketchCertificate_of_rectRightGramBasisSVDHead
      A s P_AZ tail coupling htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Selected right-Gram equation-(9) rank/residual surface with an explicit
paper-facing rank parameter `k`, obtained from the cardinality certificate
`s.card = k`. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_card_eq
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hcard : s.card = k)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A (rectRightGramBasisSketchMatrix A s)))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A (rectRightGramBasisSketchMatrix A s)) i a =
          columnSketch A (rectRightGramBasisSketchMatrix A s) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail : frobNormRect (rectRightGramBasisSVDTail A s) ≤ tail)
    (hcoupling :
      frobNormRect (preconditionRows P_AZ (rectRightGramBasisSVDTail A s)) ≤
        coupling) :
    RectRankAtMost m n k (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  have hsurface :=
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead
      A s P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg htail
      hcoupling
  exact ⟨rectRankAtMost_of_eq_rank hcard hsurface.1, hsurface.2⟩

/-- Selected right-Gram equation-(9) rank/residual surface for a selected-index
embedding `Fin k ↪ Fin n`.  The rank parameter is the displayed domain size
`k`; the selected set cardinality is proved by `rectRightGramSelectedIndexSet_card`. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_embedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (e : Fin k ↪ Fin n)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A (rectRightGramSelectedIndexSet e))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet e))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet e)) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e)) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e))) ≤
        coupling) :
    RectRankAtMost m n k (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_card_eq
    A (rectRightGramSelectedIndexSet e) P_AZ tail coupling
    (rectRightGramSelectedIndexSet_card e) hP hrepr htail_nonneg
    hcoupling_nonneg htail hcoupling

/-- Semantic ordered-top embedding handoff for the selected right-Gram
equation-(9) surface.  The certificate exposes exactly what remains to connect
mathlib's arbitrary basis-indexed right-Gram eigenvectors to the ordered
singular-value sequence: selected basis singular values must agree with the
first `k` ordered singular values.  Under that certificate, the selected square
and order facts are available together with the LR.1ch embedding rank/residual
surface. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_orderedTopEmbedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (e : Fin k ↪ Fin n)
    (htop : RectRightGramOrderedTopEmbeddingCertificate A hk e)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A (rectRightGramSelectedIndexSet e))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet e))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet e)) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e)) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A (rectRightGramSelectedIndexSet e))) ≤
        coupling) :
    (∀ a : Fin k,
      (rectRightGramBasisSingularValue A (e a)) ^ 2 =
        rectSingularValueSq A (rectTopIndex hk a)) ∧
      Antitone (fun a : Fin k => rectRightGramBasisSingularValue A (e a)) ∧
        RectRankAtMost m n k (preconditionRows P_AZ A) ∧
          lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  refine ⟨?_, ?_⟩
  · intro a
    exact rectRightGramOrderedTopEmbeddingCertificate_selected_sq_eq
      A hk e htop a
  · refine ⟨?_, ?_⟩
    · exact rectRightGramOrderedTopEmbeddingCertificate_selected_antitone
        A hk e htop
    · exact
        equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_embedding
          A e P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg
          htail hcoupling

/-- Constructed ordered-top embedding version of the selected right-Gram
equation-(9) surface.  The semantic ordered-top certificate is instantiated by
the mathlib reindexing equivalence used for the right-Gram eigenbasis. -/
theorem
    equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_constructedOrderedTopEmbedding
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP :
      LeftFactorThrough P_AZ
        (columnSketch A
          (rectRightGramBasisSketchMatrix A
            (rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk)))))
    (hrepr :
      ∀ i a,
        preconditionRows P_AZ
            (columnSketch A
              (rectRightGramBasisSketchMatrix A
                (rectRightGramSelectedIndexSet
                  (rectRightGramOrderedTopEmbedding hk)))) i a =
          columnSketch A
            (rectRightGramBasisSketchMatrix A
              (rectRightGramSelectedIndexSet
                (rectRightGramOrderedTopEmbedding hk))) i a)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect
          (rectRightGramBasisSVDTail A
            (rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))) ≤
        tail)
    (hcoupling :
      frobNormRect
          (preconditionRows P_AZ
            (rectRightGramBasisSVDTail A
              (rectRightGramSelectedIndexSet
                (rectRightGramOrderedTopEmbedding hk)))) ≤
        coupling) :
    (∀ a : Fin k,
      (rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a)) ^ 2 =
        rectSingularValueSq A (rectTopIndex hk a)) ∧
      Antitone
        (fun a : Fin k =>
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a)) ∧
        RectRankAtMost m n k (preconditionRows P_AZ A) ∧
          lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface_of_rectRightGramBasisSVDHead_orderedTopEmbedding
    A hk (rectRightGramOrderedTopEmbedding hk)
    (rectRightGramOrderedTopEmbedding_certificate A hk)
    P_AZ tail coupling hP hrepr htail_nonneg hcoupling_nonneg
    htail hcoupling

/-- Norm-generic rank/residual surface from the explicit head/tail sketch
certificate. -/
theorem equation9HeadTailSketchNormRankResidualSurface {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9RankResidualNormSurface ξ A Z P_AZ tail coupling hP
    (hHT.to_residualNormCertificate hrepr)

/-- Unitarily invariant norm rank/residual surface.  This is a typed wrapper
around the norm-generic theorem: the orthogonal-invariance fields are available
on `ξ` for later singular-value/source-SVD instantiations, while this theorem
uses only the `RectNormLike` part. -/
theorem equation9RankResidualUnitaryNormSurface {m n r : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 :
      Equation9ResidualNormCertificate ξ.toRectNormLike A P_AZ tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
        tail + coupling :=
  equation9RankResidualNormSurface ξ.toRectNormLike A Z P_AZ
    tail coupling hP hEq9

/-- Unitarily invariant norm rank/residual surface from an explicit head/tail
certificate. -/
theorem equation9HeadTailSketchUnitaryNormRankResidualSurface {m n r : ℕ}
    (ξ : UnitaryInvariantRectNormLike m n)
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ.toRectNormLike A Z P_AZ
        Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
        tail + coupling :=
  equation9HeadTailSketchNormRankResidualSurface ξ.toRectNormLike
    A Z P_AZ Head Tail tail coupling hP hrepr hHT

/-- Relative-error surface for equation (9): if the supplied equation (9)
right-hand side is itself bounded by `rho` times the residual of a certified
best rank-`k` approximation, then the exact projector candidate has that
relative residual bound. -/
theorem equation9RelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualCertificate A P_AZ tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak :=
  ⟨hbest.rank_le,
    sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP,
    le_trans hEq9.residual_bound hrelative⟩

/-- Norm-generic relative-error surface for equation (9), conditional on a
norm-generic best-rank certificate and a scalar comparison of the visible
head/tail radii. -/
theorem equation9RelativeResidualNormSurface {m n k r : ℕ}
    {ξ : RectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 : Equation9ResidualNormCertificate ξ A P_AZ tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualNorm ξ A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ A Ak :=
  ⟨hbest.rank_le,
    sketchColumnProjectorApprox_rankAtMost A Z P_AZ hP,
    le_trans hEq9.residual_bound hrelative⟩

/-- Relative-error surface from the explicit head/tail sketch certificate. -/
theorem equation9HeadTailSketchRelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak :=
  equation9RelativeResidualSurface Z P_AZ tail coupling rho hbest hP
    (hHT.to_residualCertificate hrepr) hrelative

/-- Norm-generic relative-error surface from the explicit head/tail sketch
certificate. -/
theorem equation9HeadTailSketchNormRelativeResidualSurface {m n k r : ℕ}
    {ξ : RectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualNorm ξ A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ A Ak :=
  equation9RelativeResidualNormSurface Z P_AZ tail coupling rho hbest hP
    (hHT.to_residualNormCertificate hrepr) hrelative

/-- Unitarily invariant norm relative-error surface for equation (9).  The
best-rank and residual certificates are still explicit; Eckart--Young and
singular-value construction remain separate foundations. -/
theorem equation9RelativeResidualUnitaryNormSurface {m n k r : ℕ}
    {ξ : UnitaryInvariantRectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ.toRectNormLike A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hEq9 :
      Equation9ResidualNormCertificate ξ.toRectNormLike A P_AZ tail coupling)
    (hrelative :
      tail + coupling ≤ rho * lowRankResidualNorm ξ.toRectNormLike A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ.toRectNormLike A Ak :=
  equation9RelativeResidualNormSurface Z P_AZ tail coupling rho
    hbest hP hEq9 hrelative

/-- Unitarily invariant norm relative-error surface from the explicit
head/tail sketch certificate. -/
theorem equation9HeadTailSketchUnitaryNormRelativeResidualSurface {m n k r : ℕ}
    {ξ : UnitaryInvariantRectNormLike m n}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxNorm m n k ξ.toRectNormLike A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchNormCertificate ξ.toRectNormLike A Z P_AZ
        Head Tail tail coupling)
    (hrelative :
      tail + coupling ≤ rho * lowRankResidualNorm ξ.toRectNormLike A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualNorm ξ.toRectNormLike A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualNorm ξ.toRectNormLike A Ak :=
  equation9HeadTailSketchNormRelativeResidualSurface Z P_AZ Head Tail
    tail coupling rho hbest hP hrepr hHT hrelative

/-- Frobenius specialization of the norm-generic head/tail rank/residual
surface.  This makes the concrete `frobRectNormLike` instantiation explicit
while preserving the older Frobenius statement shape. -/
theorem equation9HeadTailSketchFrobNormRankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling := by
  simpa [lowRankResidualNorm_frobRectNormLike]
    using
      equation9HeadTailSketchNormRankResidualSurface
        (frobRectNormLike m n) A Z P_AZ Head Tail tail coupling hP hrepr
        hHT.to_norm_frobRectNormLike

/-- Frobenius specialization of the norm-generic head/tail relative-residual
surface.  This is a D2 bridge theorem: it closes the concrete Frobenius
`RectNormLike` instantiation, not the still-open all-unitarily-invariant norm
or Eckart--Young foundations. -/
theorem equation9HeadTailSketchFrobNormRelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hP : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a = columnSketch A Z i a)
    (hHT :
      Equation9HeadTailSketchCertificate A Z P_AZ Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
        lowRankResidualFrob A (preconditionRows P_AZ A) ≤
          rho * lowRankResidualFrob A Ak := by
  simpa [lowRankResidualNorm_frobRectNormLike]
    using
      equation9HeadTailSketchNormRelativeResidualSurface
        (Z := Z) (P_AZ := P_AZ) (Head := Head) (Tail := Tail)
        (tail := tail) (coupling := coupling) (rho := rho)
        (hbest := hbest.to_norm_frobRectNormLike)
        (hP := hP) (hrepr := hrepr)
        (hHT := hHT.to_norm_frobRectNormLike)
        (hrelative := by
          simpa [lowRankResidualNorm_frobRectNormLike] using hrelative)



































































































































































































































































/-- Exact source-factor matrix `U Σ Vᵀ`.  This is a theorem-surface object for
the equation (9) SVD route; implementation-facing theorems must separately
certify any computed singular vectors, singular values, or products. -/
noncomputable def sourceSVDFactorMatrix {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => ∑ a : Fin r, U i a * (∑ b : Fin r, Sigma a b * V j b)

/-- A diagonal source factor expands to the usual supplied-SVD sum
`sum_k U_ik sigma_k V_jk`.

This is exact-object algebra.  It is used only to align supplied SVD-style
representations with the source-factor theorem surface; computed singular
vectors, singular values, and products remain non-probability FP/certificate
obligations. -/
theorem sourceSVDFactorMatrix_diagonal_eq_sum {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix U
        (fun a b : Fin r => if a = b then sigma a else 0) V i j =
      ∑ k : Fin r, U i k * (sigma k * V j k) := by
  unfold sourceSVDFactorMatrix
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The exact source head `U Σ Vᵀ` factors through the displayed source rank
dimension.  This is an exact-object source-SVD rank certificate; constructing
or computing the source SVD data remains a separate obligation. -/
noncomputable def sourceSVDFactorMatrixRankFactorization {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) :
    RectRankFactorization m n r (sourceSVDFactorMatrix U Sigma V) where
  left := U
  right := fun a j => ∑ b : Fin r, Sigma a b * V j b
  factorization := by
    intro i j
    rfl

/-- The exact source head `U Σ Vᵀ` has rank at most the displayed source
dimension `r`. -/
theorem sourceSVDFactorMatrix_rankAtMost {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) :
    RectRankAtMost m n r (sourceSVDFactorMatrix U Sigma V) :=
  ⟨sourceSVDFactorMatrixRankFactorization U Sigma V⟩

















































































/-- Matrix-vector action of an exact source factor `U Sigma V^T`, written as
successive right-transpose, diagonal/source, and left-basis actions. -/
theorem rectMatMulVec_sourceSVDFactorMatrix {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (Sigma : Fin n → Fin n → ℝ)
    (V : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x =
      fun i : Fin m =>
        ∑ a : Fin n,
          U i a * matMulVec n Sigma (matMulVec n (matTranspose V) x) a := by
  ext i
  unfold rectMatMulVec sourceSVDFactorMatrix matMulVec matTranspose
  calc
    (∑ j : Fin n,
        (∑ a : Fin n, U i a * (∑ b : Fin n, Sigma a b * V j b)) * x j)
        =
          ∑ j : Fin n, ∑ a : Fin n,
            U i a * ((∑ b : Fin n, Sigma a b * V j b) * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          ∑ a : Fin n, ∑ j : Fin n,
            U i a * ((∑ b : Fin n, Sigma a b * V j b) * x j) := by
            rw [Finset.sum_comm]
    _ =
          ∑ a : Fin n,
            U i a *
              (∑ j : Fin n, (∑ b : Fin n, Sigma a b * V j b) * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ a : Fin n,
            U i a *
              (∑ b : Fin n, Sigma a b *
                ∑ j : Fin n, V j b * x j) := by
            apply Finset.sum_congr rfl
            intro a _
            congr 1
            calc
              (∑ j : Fin n, (∑ b : Fin n, Sigma a b * V j b) * x j)
                  =
                    ∑ j : Fin n, ∑ b : Fin n,
                      (Sigma a b * V j b) * x j := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
                  _ =
                    ∑ b : Fin n, ∑ j : Fin n,
                      (Sigma a b * V j b) * x j := by
                      rw [Finset.sum_comm]
                  _ =
                    ∑ b : Fin n, Sigma a b *
                      ∑ j : Fin n, V j b * x j := by
                      apply Finset.sum_congr rfl
                      intro b _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring












































































/-- For an exact source factor `U diag(sigma) V^T`, exact left
column-orthonormality of `U` identifies the source action energy with the
diagonal action energy after right-basis transport by `V^T`. -/
theorem vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (sigma : Fin n → ℝ)
    (V : Fin n → Fin n → ℝ)
    (hU :
      ∀ a b : Fin n, (∑ i : Fin m, U i a * U i b) = idMatrix n a b)
    (x : Fin n → ℝ) :
    vecNorm2Sq
        (rectMatMulVec
          (sourceSVDFactorMatrix U
            (fun i j : Fin n => if i = j then sigma i else 0) V) x) =
      vecNorm2Sq
        (rectMatMulVec
          (fun i j : Fin n => if i = j then sigma i else 0)
          (matMulVec n (matTranspose V) x)) := by
  let y : Fin n → ℝ := matMulVec n (matTranspose V) x
  let z : Fin n → ℝ :=
    matMulVec n (fun i j : Fin n => if i = j then sigma i else 0) y
  have hleft :
      vecNorm2Sq (fun i : Fin m => ∑ a : Fin n, U i a * z a) =
        vecNorm2Sq z :=
    vecNorm2Sq_leftOrthonormalFactor U z hU
  rw [rectMatMulVec_sourceSVDFactorMatrix U
    (fun i j : Fin n => if i = j then sigma i else 0) V x]
  simpa [y, z, matMulVec, rectMatMulVec] using hleft

/-- Exact source-factor transport for the ordered diagonal source-side
tail-energy theorem.  The right orthogonal table transports the probe frame,
the left column-orthonormal table preserves the squared source action, and
LR.1dn supplies the ordered diagonal lower bound.

This remains exact-object source-factor infrastructure only: it does not
construct an SVD/source split, prove Eckart--Young optimality, derive
randomness, or certify computed SVD/singular-vector/projector/Gram/sketch/
product routines.  Sampling probabilities and laws remain exact mathematical
inputs by convention. -/
theorem sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hx : Orthonormal ℝ x)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
      (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  let y : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q =>
      (WithLp.toLp 2
        (matMulVec (r + q) (matTranspose V)
          (fun j : Fin (r + q) =>
            (x c : EuclideanSpace ℝ (Fin (r + q))) j)) :
        EuclideanSpace ℝ (Fin (r + q)))
  have hy : Orthonormal ℝ y := by
    simpa [y] using
      orthonormal_matTranspose_mulVec_of_isOrthogonal V hV x hx
  have hdiag :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_antitone
      sigma y hy hmono
  have hsum_eq :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (y c : EuclideanSpace ℝ (Fin (r + q))) j))) =
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have h :=
      vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action
        U sigma V hU
        (fun j : Fin (r + q) =>
      (x c : EuclideanSpace ℝ (Fin (r + q))) j)
    simpa [y] using h.symm
  simpa [hsum_eq] using hdiag

/-- Exact q-dimensional Eckart--Young lower-bound bridge for supplied ordered
source-factor data, squared form.

For every exact rank-at-most-`r` competitor, LR.1dj selects an orthonormal
right-kernel probe family.  LR.1do lower-bounds the source action on that same
family by the displayed ordered tail-square sum, while LR.1dj upper-bounds it
by the competitor residual Frobenius square.

This is exact-object infrastructure only: rectangular SVD/source-split
construction, randomness, and computed non-probability SVD/projector/Gram/
sketch/product certificates remain separate obligations. -/
theorem rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      (lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B) ^ 2 := by
  rcases hB with ⟨fac⟩
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
      (A := A) fac with
    ⟨x, hx, _hzero, henergy⟩
  let xAmb : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))
  have hxAmb : Orthonormal ℝ xAmb := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [xAmb, Submodule.coe_inner] using h
  have hsource :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec A
              (fun j : Fin (r + q) =>
                (xAmb c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    simpa [A, xAmb] using
      sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_antitone
        U sigma V xAmb hU hV hxAmb hmono
  have hsq :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        frobNormSqRect (fun i j => A i j - B i j) :=
    le_trans hsource henergy
  rw [lowRankResidualFrob, frobNormRect_sq]
  exact hsq

/-- Exact source-factor transport for the head-tail gap version of the
ordered diagonal tail-energy theorem.

Unlike the antitone source-factor theorem, this statement only requires a
visible gap `eta`: every head square is at least `eta`, and every tail square
is at most `eta`.  This is the right exact-object shape for constructed
ordered top-`k` splits whose complement-tail enumeration is not itself sorted
by singular value.  It does not construct an SVD/source split, derive
randomness, or certify computed non-probability SVD/projector/Gram/sketch/
product routines. Sampling probabilities and laws remain exact mathematical
inputs by convention. -/
theorem sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (x : Fin q → EuclideanSpace ℝ (Fin (r + q)))
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hx : Orthonormal ℝ x)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
  let y : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q =>
      (WithLp.toLp 2
        (matMulVec (r + q) (matTranspose V)
          (fun j : Fin (r + q) =>
            (x c : EuclideanSpace ℝ (Fin (r + q))) j)) :
        EuclideanSpace ℝ (Fin (r + q)))
  have hy : Orthonormal ℝ y := by
    simpa [y] using
      orthonormal_matTranspose_mulVec_of_isOrthogonal V hV x hx
  have hdiag :=
    sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap
      sigma y hy hhead htail
  have hsum_eq :
      (∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (fun i j : Fin (r + q) => if i = j then sigma i else 0)
            (fun j : Fin (r + q) =>
              (y c : EuclideanSpace ℝ (Fin (r + q))) j))) =
      ∑ c : Fin q,
        vecNorm2Sq
          (rectMatMulVec
            (sourceSVDFactorMatrix U
              (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
            (fun j : Fin (r + q) =>
              (x c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    apply Finset.sum_congr rfl
    intro c _
    have h :=
      vecNorm2Sq_sourceSVDFactorMatrix_eq_diagonal_transpose_action
        U sigma V hU
        (fun j : Fin (r + q) =>
          (x c : EuclideanSpace ℝ (Fin (r + q))) j)
    simpa [y] using h.symm
  simpa [hsum_eq] using hdiag

/-- Exact q-dimensional Eckart--Young lower-bound bridge for supplied
source-factor data under a visible head-tail gap, squared form.

This is the gap-based companion to
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone`.
It is exact-object lower-bound infrastructure only; the gap must still be
instantiated by a source theorem, and computed non-probability routines remain
separate obligations. -/
theorem rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      (lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B) ^ 2 := by
  rcases hB with ⟨fac⟩
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  rcases rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le
      (A := A) fac with
    ⟨x, hx, _hzero, henergy⟩
  let xAmb : Fin q → EuclideanSpace ℝ (Fin (r + q)) :=
    fun c : Fin q => (x c : EuclideanSpace ℝ (Fin (r + q)))
  have hxAmb : Orthonormal ℝ xAmb := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro c d
    have h := hx c d
    simpa [xAmb, Submodule.coe_inner] using h
  have hsource :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        ∑ c : Fin q,
          vecNorm2Sq
            (rectMatMulVec A
              (fun j : Fin (r + q) =>
                (xAmb c : EuclideanSpace ℝ (Fin (r + q))) j)) := by
    simpa [A, xAmb] using
      sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap
        U sigma V xAmb hU hV hxAmb hhead htail
  have hsq :
      (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
        frobNormSqRect (fun i j => A i j - B i j) :=
    le_trans hsource henergy
  rw [lowRankResidualFrob, frobNormRect_sq]
  exact hsq

/-- Square-root norm form of
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`. -/
theorem sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    {eta : ℝ}
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hhead : ∀ a : Fin r, eta ≤ sigma (Fin.castAdd q a) ^ 2)
    (htail : ∀ c : Fin q, sigma (Fin.natAdd r c) ^ 2 ≤ eta)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B := by
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  have hsq :=
    rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap
      U sigma V hU hV hhead htail B hB
  calc
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2)
        ≤ Real.sqrt ((lowRankResidualFrob A B) ^ 2) :=
          Real.sqrt_le_sqrt (by simpa [A] using hsq)
    _ = lowRankResidualFrob A B := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (frobNormRect_nonneg _)

/-- Square-root norm form of
`rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone`. -/
theorem sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
    {m r q : ℕ}
    (U : Fin m → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (V : Fin (r + q) → Fin (r + q) → ℝ)
    (hU :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, U i a * U i b) = idMatrix (r + q) a b)
    (hV : IsOrthogonal (r + q) V)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix U
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) V)
        B := by
  let A : Fin m → Fin (r + q) → ℝ :=
    sourceSVDFactorMatrix U
      (fun i j : Fin (r + q) => if i = j then sigma i else 0) V
  have hsq :=
    rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_antitone
      U sigma V hU hV hmono B hB
  calc
    Real.sqrt (∑ c : Fin q, sigma (Fin.natAdd r c) ^ 2)
        ≤ Real.sqrt ((lowRankResidualFrob A B) ^ 2) :=
          Real.sqrt_le_sqrt (by simpa [A] using hsq)
    _ = lowRankResidualFrob A B := by
          rw [Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (frobNormRect_nonneg _)

/-- Diagonal source-block vector-action lower bound.  If `U` has exact
orthonormal columns, `V` is exact square orthogonal, and the diagonal entries of
`Sigma` are all at least a nonnegative `sigma`, then the exact source factor
`U Sigma V^T` supplies the vector-action hypothesis needed by LR.1cz.

This is exact-object spectral infrastructure only; it does not certify computed
SVD/singular-vector/diagonal routines, and sampling probabilities/laws remain
exact mathematical inputs by convention. -/
theorem sourceSVDFactorMatrix_diagonal_vector_action_lower_bound {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (Sigma : Fin n → Fin n → ℝ)
    (sigmaDiag : Fin n → ℝ) (V : Fin n → Fin n → ℝ) {sigma : ℝ}
    (hU :
      ∀ a b : Fin n, (∑ i : Fin m, U i a * U i b) = idMatrix n a b)
    (hV : IsOrthogonal n V)
    (hSigma : ∀ a b, Sigma a b = if a = b then sigmaDiag a else 0)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a, sigma ≤ sigmaDiag a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := by
  let y : Fin n → ℝ := matMulVec n (matTranspose V) x
  let z : Fin n → ℝ := matMulVec n Sigma y
  have hleft :
      vecNorm2Sq (fun i : Fin m => ∑ a : Fin n, U i a * z a) =
        vecNorm2Sq z :=
    vecNorm2Sq_leftOrthonormalFactor U z hU
  have hdiag_lower :
      sigma ^ 2 * vecNorm2Sq y ≤ vecNorm2Sq z := by
    simpa [z] using
      vecNorm2Sq_diagonal_lower_bound Sigma sigmaDiag hSigma
        hsigma_nonneg hdiag y
  have hy_norm : vecNorm2Sq y = vecNorm2Sq x := by
    simpa [y] using
      vecNorm2Sq_orthogonal (matTranspose V) x hV.transpose
  have hsq_source :
      vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) =
        vecNorm2Sq z := by
    rw [rectMatMulVec_sourceSVDFactorMatrix U Sigma V x]
    simpa [z] using hleft
  have hsq :
      sigma ^ 2 * vecNorm2Sq x ≤
        vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := by
    calc
      sigma ^ 2 * vecNorm2Sq x
          = sigma ^ 2 * vecNorm2Sq y := by rw [hy_norm]
      _ ≤ vecNorm2Sq z := hdiag_lower
      _ = vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) :=
          hsq_source.symm
  have hsq_norm :
      (sigma * vecNorm2 x) ^ 2 ≤
        (vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x)) ^ 2 := by
    calc
      (sigma * vecNorm2 x) ^ 2
          = sigma ^ 2 * vecNorm2Sq x := by
              rw [mul_pow, vecNorm2_sq]
      _ ≤ vecNorm2Sq (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) := hsq
      _ =
          (vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x)) ^ 2 := by
          rw [vecNorm2_sq]
  have hleft_nonneg : 0 ≤ sigma * vecNorm2 x :=
    mul_nonneg hsigma_nonneg (vecNorm2_nonneg x)
  have hright_nonneg :
      0 ≤ vecNorm2 (rectMatMulVec (sourceSVDFactorMatrix U Sigma V) x) :=
    vecNorm2_nonneg _
  have habs := (sq_le_sq).mp hsq_norm
  simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs

/-- Supplied exact square SVD-style diagonal data instantiate the generic
diagonal source-block vector-action lower bound.  Every displayed singular
entry is assumed to be at least the nonnegative lower radius `sigma`.

This is exact-object spectral infrastructure only; it does not construct or
certify computed singular vectors, singular values, or source products. -/
theorem squareSVD_diagonal_vector_action_lower_bound {n : ℕ}
    (Ufull Vfull : Fin n → Fin n → ℝ) (sigmaVals : Fin n → ℝ)
    {sigma : ℝ}
    (hU : IsOrthogonal n Ufull)
    (hV : IsOrthogonal n Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin n, sigma ≤ sigmaVals a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2
        (rectMatMulVec
          (sourceSVDFactorMatrix Ufull
            (fun a b => if a = b then sigmaVals a else 0) Vfull) x) :=
  sourceSVDFactorMatrix_diagonal_vector_action_lower_bound
    Ufull (fun a b => if a = b then sigmaVals a else 0) sigmaVals Vfull
    (by
      intro a b
      exact hU.col_orthonormal a b)
    hV
    (by
      intro a b
      rfl)
    hsigma_nonneg hdiag x

/-- Supplied exact thin-rectangular SVD-style diagonal data instantiate the
generic diagonal source-block vector-action lower bound.  The left table is
rectangular and is supplied by an exact column-orthonormality certificate; the
right table remains square orthogonal.

This is exact-object spectral infrastructure only; computed non-probability
SVD/singular-vector/product routines remain separate obligations. -/
theorem rectangularThinSVD_diagonal_vector_action_lower_bound {m n : ℕ}
    (Ufull : Fin m → Fin n → ℝ) (Vfull : Fin n → Fin n → ℝ)
    (sigmaVals : Fin n → ℝ) {sigma : ℝ}
    (hUcols :
      ∀ a b : Fin n,
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal n Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin n, sigma ≤ sigmaVals a)
    (x : Fin n → ℝ) :
    sigma * vecNorm2 x ≤
      vecNorm2
        (rectMatMulVec
          (sourceSVDFactorMatrix Ufull
            (fun a b => if a = b then sigmaVals a else 0) Vfull) x) :=
  sourceSVDFactorMatrix_diagonal_vector_action_lower_bound
    Ufull (fun a b => if a = b then sigmaVals a else 0) sigmaVals Vfull
    (by
      intro a b
      simpa [idMatrix] using hUcols a b)
    hV
    (by
      intro a b
      rfl)
    hsigma_nonneg hdiag x

/-- Square supplied-SVD residual lower bound on an `(r+1)` source block.  The
diagonal lower-action theorem supplies the vector hypothesis in the LR.1cz
rank-nullity/min-max adapter. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_squareSVD_diagonal_succ
    {r : ℕ}
    (Ufull Vfull : Fin (r + 1) → Fin (r + 1) → ℝ)
    (sigmaVals : Fin (r + 1) → ℝ) {sigma : ℝ}
    (hU : IsOrthogonal (r + 1) Ufull)
    (hV : IsOrthogonal (r + 1) Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a)
    (B : Fin (r + 1) → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost (r + 1) (r + 1) r B) :
    sigma ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix Ufull
          (fun a b => if a = b then sigmaVals a else 0) Vfull) B :=
  rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    (sourceSVDFactorMatrix Ufull
      (fun a b => if a = b then sigmaVals a else 0) Vfull)
    B hB
    (by
      intro x _hx
      exact
        squareSVD_diagonal_vector_action_lower_bound Ufull Vfull
          sigmaVals hU hV hsigma_nonneg hdiag x)

/-- Thin-rectangular supplied-SVD residual lower bound on an `(r+1)` source
block.  This exact-object wrapper charges no floating-point probability
construction and does not certify computed singular-vector routines. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_rectangularThinSVD_diagonal_succ
    {m r : ℕ}
    (Ufull : Fin m → Fin (r + 1) → ℝ)
    (Vfull : Fin (r + 1) → Fin (r + 1) → ℝ)
    (sigmaVals : Fin (r + 1) → ℝ) {sigma : ℝ}
    (hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + 1) Vfull)
    (hsigma_nonneg : 0 ≤ sigma)
    (hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a)
    (B : Fin m → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost m (r + 1) r B) :
    sigma ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix Ufull
          (fun a b => if a = b then sigmaVals a else 0) Vfull) B :=
  rectRankAtMost_lowRankResidualFrob_ge_of_vector_lower_bound_succ
    (sourceSVDFactorMatrix Ufull
      (fun a b => if a = b then sigmaVals a else 0) Vfull)
    B hB
    (by
      intro x _hx
      exact
        rectangularThinSVD_diagonal_vector_action_lower_bound Ufull Vfull
          sigmaVals hUcols hV hsigma_nonneg hdiag x)

/-- The constructed ordered top-`r+1` right-Gram head block instantiates the
one-block min-max residual lower bound.  If the last selected ordered singular
value is positive, every displayed selected diagonal entry dominates it, so any
rank-at-most-`r` competitor on those displayed coordinates has Frobenius
residual at least that last selected value.

This is exact-object spectral infrastructure only.  It uses the exact
right-Gram singular data as analysis objects and does not certify a computed
SVD/singular-vector/projector/Gram/sketch/product routine. -/
theorem rectRankAtMost_lowRankResidualFrob_ge_of_rectRightGramOrderedHeadDiagonal_succ
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : r + 1 ≤ n)
    (hlast :
      0 < rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))))
    (B : Fin m → Fin (r + 1) → ℝ)
    (hB : RectRankAtMost m (r + 1) r B) :
    rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))) ≤
      lowRankResidualFrob
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (idMatrix (r + 1))) B := by
  classical
  let sigma :=
    rectSingularValue A
      (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r)))
  let sigmaVals : Fin (r + 1) → ℝ :=
    fun a => rectRightGramBasisSingularValue A
      (rectRightGramOrderedTopEmbedding hk a)
  have hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedHeadLeft A hk i b) =
          if a = b then 1 else 0 := by
    intro a b
    simpa [idMatrix] using
      rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
        A hk (Nat.succ_pos r) hlast a b
  have hsigma_nonneg : 0 ≤ sigma := by
    exact rectSingularValue_nonneg A _
  have hdiag : ∀ a : Fin (r + 1), sigma ≤ sigmaVals a := by
    intro a
    change sigma ≤
      rectRightGramBasisSingularValue A (rectRightGramOrderedTopEmbedding hk a)
    rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq a]
    simpa [sigma] using
      rectSingularValue_antitone A
        (rectTopIndex_le_last hk (Nat.succ_pos r) a)
  have hthin :=
    rectRankAtMost_lowRankResidualFrob_ge_of_rectangularThinSVD_diagonal_succ
      (rectRightGramOrderedHeadLeft A hk)
      (idMatrix (r + 1))
      sigmaVals
      hUcols
      (IsOrthogonal.id (r + 1))
      hsigma_nonneg
      hdiag
      B hB
  simpa [sigma, sigmaVals, rectRightGramOrderedHeadSingularDiagonal] using hthin

/-- Expanding the ordered top-`k` source factor gives the displayed selected
right-Gram SVD terms in the constructed embedding order. -/
theorem sourceSVDFactorMatrix_rectRightGramOrderedHead_entry
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j =
      ∑ a : Fin k,
        rectRightGramLeftSingularZeroSafe A i
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a) *
          rectRightGramEigenbasis A j
            (rectRightGramOrderedTopEmbedding hk a) := by
  unfold sourceSVDFactorMatrix rectRightGramOrderedHeadLeft
    rectRightGramOrderedHeadSingularDiagonal rectRightGramOrderedHeadRight
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]
  ring

/-- The selected right-Gram head induced by the constructed ordered top-`k`
embedding is exactly the ordered source factor `U_ord Sigma_ord V_ord^T`.
This closes the exact ordered source-head factorization step, not the
complementary tail factor or Eckart--Young optimality. -/
theorem rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A
        (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
        i j =
      sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j := by
  classical
  rw [sourceSVDFactorMatrix_rectRightGramOrderedHead_entry]
  unfold rectRightGramBasisSVDHead rectRightGramSelectedIndexSet
  rw [Finset.sum_map]

/-- Expanding the complement-tail source factor gives the displayed
basis-indexed SVD terms in the complement enumeration order. -/
theorem sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramBasisSVDTailLeft A s)
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j =
      ∑ a : Fin ((sᶜ).card),
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramEigenbasis A j
            ((sᶜ).orderEmbOfFin rfl a) := by
  unfold sourceSVDFactorMatrix rectRightGramBasisSVDTailLeft
    rectRightGramBasisSVDTailSingularDiagonal rectRightGramBasisSVDTailRight
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]
  ring

/-- The complementary right-Gram tail for any selected finite index set is
exactly the source factor `U_tail Sigma_tail V_tail^T` obtained by enumerating
the complement.  This is exact analysis-object algebra; it does not assert that
the zero-safe tail-left table is an orthonormal SVD tail basis. -/
theorem rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A s i j =
      sourceSVDFactorMatrix
        (rectRightGramBasisSVDTailLeft A s)
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j := by
  classical
  rw [sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry]
  unfold rectRightGramBasisSVDTail
  let e : Fin ((sᶜ).card) → Fin n := fun a => (sᶜ).orderEmbOfFin rfl a
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hsum :
      (sᶜ).sum term = ∑ a : Fin ((sᶜ).card), term (e a) := by
    have hsub :
        (∑ a : Fin ((sᶜ).card), term (e a)) =
          ∑ x : {x // x ∈ (sᶜ)}, term x := by
      refine Fintype.sum_equiv ((sᶜ).orderIsoOfFin rfl).toEquiv
        (fun a : Fin ((sᶜ).card) => term (e a))
        (fun x : {x // x ∈ (sᶜ)} => term x) ?_
      intro a
      simp [e]
    calc
      (sᶜ).sum term = ∑ x : {x // x ∈ (sᶜ)}, term x := by
            simpa using (Finset.sum_coe_sort (sᶜ) term).symm
      _ = ∑ a : Fin ((sᶜ).card), term (e a) := hsub.symm
  rw [show
      (sᶜ).sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) = (sᶜ).sum term by rfl]
  rw [hsum]

/-- A replacement complement-tail left table gives the same source factor as
the zero-safe table if it agrees with the zero-safe table on every nonzero
complement singular direction.  On zero singular directions, the diagonal tail
singular-value block erases the left column. -/
theorem sourceSVDFactorMatrix_rectRightGramBasisSVDTail_replacement_left_entry
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (Utail : Fin m → Fin ((sᶜ).card) → ℝ)
    (hUtail :
      ∀ i a,
        rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) ≠ 0 →
          Utail i a =
            rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a))
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j =
      ∑ a : Fin ((sᶜ).card),
        rectRightGramLeftSingularZeroSafe A i
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) *
          rectRightGramEigenbasis A j
            ((sᶜ).orderEmbOfFin rfl a) := by
  unfold sourceSVDFactorMatrix rectRightGramBasisSVDTailSingularDiagonal
    rectRightGramBasisSVDTailRight
  apply Finset.sum_congr rfl
  intro a _
  by_cases hτ :
      rectRightGramBasisSingularValue A
        ((sᶜ).orderEmbOfFin rfl a) = 0
  · simp [hτ]
  · rw [hUtail i a hτ]
    simp
    ring

/-- Replacement-left version of the complement-tail source factorization.  This
is the exact adapter needed by a nullspace-completed tail-left construction:
the replacement table may differ from the zero-safe table only on diagonal-zero
tail singular directions. -/
theorem rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix_replacement_left
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (Utail : Fin m → Fin ((sᶜ).card) → ℝ)
    (hUtail :
      ∀ i a,
        rectRightGramBasisSingularValue A
            ((sᶜ).orderEmbOfFin rfl a) ≠ 0 →
          Utail i a =
            rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A s i j =
      sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A s)
        (rectRightGramBasisSVDTailRight A s) i j := by
  calc
    rectRightGramBasisSVDTail A s i j =
        sourceSVDFactorMatrix
          (rectRightGramBasisSVDTailLeft A s)
          (rectRightGramBasisSVDTailSingularDiagonal A s)
          (rectRightGramBasisSVDTailRight A s) i j :=
        rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix A s i j
    _ =
        ∑ a : Fin ((sᶜ).card),
          rectRightGramLeftSingularZeroSafe A i
              ((sᶜ).orderEmbOfFin rfl a) *
            rectRightGramBasisSingularValue A
              ((sᶜ).orderEmbOfFin rfl a) *
            rectRightGramEigenbasis A j
              ((sᶜ).orderEmbOfFin rfl a) :=
        sourceSVDFactorMatrix_rectRightGramBasisSVDTail_entry A s i j
    _ =
        sourceSVDFactorMatrix
          Utail
          (rectRightGramBasisSVDTailSingularDiagonal A s)
          (rectRightGramBasisSVDTailRight A s) i j :=
        (sourceSVDFactorMatrix_rectRightGramBasisSVDTail_replacement_left_entry
          A s Utail hUtail i j).symm

/-- The ordered top-`k` complementary right-Gram tail is exactly the ordered
complement source factor. -/
theorem rectRightGramBasisSVDTail_orderedTopEmbedding_eq_sourceSVDFactorMatrix
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDTail A
        (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
        i j =
      sourceSVDFactorMatrix
        (rectRightGramOrderedTailLeft A hk)
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j := by
  simpa [rectRightGramOrderedTailLeft, rectRightGramOrderedTailRight,
    rectRightGramOrderedTailSingularDiagonal] using
    rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j

/-- The constructed ordered right-Gram source head plus the ordered complement
source tail reconstructs `A` entrywise.  This closes only the exact source-split
algebra; orthonormal tail-left completion and Eckart--Young optimality remain
separate D3 obligations. -/
theorem rectRightGramOrdered_source_head_add_tail
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j +
      sourceSVDFactorMatrix
        (rectRightGramOrderedTailLeft A hk)
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j =
      A i j := by
  rw [← rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j,
    ← rectRightGramBasisSVDTail_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j]
  exact
    rectRightGramBasisSVD_head_add_tail A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j

/-- Ordered source split with a replacement complement-tail left table.  The
replacement table must agree with the constructed zero-safe tail-left table on
nonzero complement singular directions; zero complement directions are erased
by the diagonal tail singular-value block. -/
theorem rectRightGramOrdered_source_head_add_tail_replacement_left
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail :
      Fin m →
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ)
    (hUtail :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c)
    (i : Fin m) (j : Fin n) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (rectRightGramOrderedHeadRight A hk) i j +
      sourceSVDFactorMatrix
        Utail
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) i j =
      A i j := by
  rw [← rectRightGramBasisSVDHead_orderedTopEmbedding_eq_sourceSVDFactorMatrix
      A hk i j]
  change
    rectRightGramBasisSVDHead A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk)) i j +
      sourceSVDFactorMatrix
        Utail
        (rectRightGramBasisSVDTailSingularDiagonal A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk)))
        (rectRightGramBasisSVDTailRight A
          (rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))) i j =
      A i j
  rw [← rectRightGramBasisSVDTail_eq_sourceSVDFactorMatrix_replacement_left
    A (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk))
    Utail ?_ i j]
  exact
    rectRightGramBasisSVD_head_add_tail A
      (rectRightGramSelectedIndexSet (rectRightGramOrderedTopEmbedding hk)) i j
  intro i c hτ
  simpa [rectRightGramOrderedTailLeft] using hUtail i c hτ

/-- For an exact source split `A = U Sigma V^T + Tail`, the Frobenius residual
of the displayed source head is exactly the Frobenius norm of the tail.  This is
an exact analysis-object identity; a computed SVD/head/tail routine must supply
its own perturbation certificate before using it implementation-facing. -/
theorem lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    lowRankResidualFrob A (sourceSVDFactorMatrix U Sigma V) =
      frobNormRect Tail := by
  unfold lowRankResidualFrob
  apply congrArg frobNormRect
  funext i j
  rw [hA i j]
  ring

/-- Norm-generic version of
`lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail`. -/
theorem lowRankResidualNorm_sourceSVDFactorMatrix_eq_tail {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    lowRankResidualNorm ξ A (sourceSVDFactorMatrix U Sigma V) =
      ξ.norm Tail := by
  unfold lowRankResidualNorm
  apply congrArg ξ.norm
  funext i j
  rw [hA i j]
  ring

/-- If a source split has the supplied Eckart--Young/tail-optimality inequality,
then the displayed source head is a Frobenius best rank-`r` approximation.
The rank side is proved by `sourceSVDFactorMatrix_rankAtMost`; the optimality
inequality remains an explicit source-SVD/Eckart--Young obligation. -/
theorem sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U Sigma V) where
  rank_le := sourceSVDFactorMatrix_rankAtMost U Sigma V
  optimal := by
    intro B hB
    rw [lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail A Tail U Sigma V hA]
    exact hopt B hB

/-- Norm-generic best-rank certificate from an exact source split and a supplied
tail-optimality inequality for the chosen norm. -/
theorem sourceSVDFactorMatrix_isBestRankApproxNorm_of_tail_optimal {m n r : ℕ}
    (ξ : RectNormLike m n)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hopt : ∀ B, RectRankAtMost m n r B →
      ξ.norm Tail ≤ lowRankResidualNorm ξ A B) :
    IsBestRankApproxNorm m n r ξ A (sourceSVDFactorMatrix U Sigma V) where
  rank_le := sourceSVDFactorMatrix_rankAtMost U Sigma V
  optimal := by
    intro B hB
    rw [lowRankResidualNorm_sourceSVDFactorMatrix_eq_tail ξ A Tail U Sigma V hA]
    exact hopt B hB









/-- Exact source sketch right factor `Σ (Vᵀ Z)`. -/
noncomputable def sourceSVDSketchRightFactor {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => ∑ c : Fin r, Sigma a c * rightSketchCrossGram V Z c b


































/-- Exact source-tail left orthogonality, `U^T Tail = 0`, stated entrywise.
This is an analysis-side SVD split certificate; if an implementation computes
the source basis or tail, those are non-probability computed quantities. -/
def sourceTailLeftOrthogonal {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Tail : Fin m → Fin n → ℝ) : Prop :=
  ∀ a j, ∑ i : Fin m, U i a * Tail i j = 0

/-- A supplied tail SVD-style factorization gives the left source-tail
orthogonality field once the head and tail left bases are cross-orthogonal.
This is exact analysis-side algebra; computed bases or tail factors remain
implementation-facing non-probability obligations. -/
theorem sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero {m n r q : ℕ}
    (U : Fin m → Fin r → ℝ) (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hTail : ∀ i j,
      Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0) :
    sourceTailLeftOrthogonal U Tail := by
  intro a j
  calc
    ∑ i : Fin m, U i a * Tail i j =
        ∑ i : Fin m, U i a *
          sourceSVDFactorMatrix Utail SigmaTail Vtail i j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hTail i j]
    _ = ∑ c : Fin q, (∑ b : Fin q, SigmaTail c b * Vtail j b) *
          (∑ i : Fin m, U i a * Utail i c) := by
          unfold sourceSVDFactorMatrix
          calc
            ∑ i : Fin m, U i a *
                (∑ c : Fin q, Utail i c *
                  (∑ b : Fin q, SigmaTail c b * Vtail j b)) =
                ∑ i : Fin m, ∑ c : Fin q,
                  U i a * (Utail i c *
                    (∑ b : Fin q, SigmaTail c b * Vtail j b)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
            _ = ∑ c : Fin q, ∑ i : Fin m,
                  U i a * (Utail i c *
                    (∑ b : Fin q, SigmaTail c b * Vtail j b)) := by
                  rw [Finset.sum_comm]
            _ = ∑ c : Fin q, (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                  (∑ i : Fin m, U i a * Utail i c) := by
                  apply Finset.sum_congr rfl
                  intro c _
                  calc
                    ∑ i : Fin m, U i a * (Utail i c *
                        (∑ b : Fin q, SigmaTail c b * Vtail j b)) =
                        ∑ i : Fin m,
                          (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                            (U i a * Utail i c) := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                    _ = (∑ b : Fin q, SigmaTail c b * Vtail j b) *
                        (∑ i : Fin m, U i a * Utail i c) := by
                          rw [Finset.mul_sum]
    _ = 0 := by
          simp [hcross]

/-- First-class exact source-SVD head/tail certificate for the diagonal
equation-(9) route.

This packages the exact analysis-side data that LR.1bm/LR.1bn previously
threaded as separate hypotheses: a source split, a tail factorization, exact
left/right orthogonality and completeness fields, and a diagonal nonsingular
head block. It is deliberately not a rectangular SVD existence theorem and it
does not certify computed singular vectors, singular values, bases, projectors,
Grams, inverses, or products. Those remain implementation-facing
non-probability obligations. Sampling probabilities and laws remain exact
mathematical inputs by project convention. -/
structure DiagonalSourceSVDTailCertificate (m n r q : ℕ)
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ) : Prop where
  split :
    ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j
  tail_factor :
    ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j
  Utail_orthonormal :
    ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b
  left_cross :
    ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0
  U_orthonormal :
    ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b
  head_diagonal :
    ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0
  head_nonzero :
    ∀ a, sigmaHead a ≠ 0
  Vperp_orthonormal :
    ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c
  right_cross_tail :
    ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0
  right_cross_head :
    ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0
  V_orthonormal :
    ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c
  right_complete :
    ∀ j k,
      (∑ c : Fin q, Vperp j c * Vperp k c) +
        (∑ b : Fin r, V j b * V k b) =
      idMatrix n j k

namespace DiagonalSourceSVDTailCertificate

/-- The exact certificate supplies the source-tail left-orthogonality field
consumed by the head-plus-tail sketch-Gram split. -/
theorem sourceTailLeftOrthogonal {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    sourceTailLeftOrthogonal U Tail :=
  sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
    U Tail Utail SigmaTail Vperp cert.tail_factor cert.left_cross

/-- A supplied tail-optimality inequality turns the exact diagonal source
certificate into the Frobenius best-rank certificate used by the relative
equation-(9) surfaces. The actual Eckart--Young/singular-value proof of this
inequality remains a separate foundation obligation. -/
theorem isBestRankApproxFrob_of_tail_optimal {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) :=
  sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal
    A Tail U SigmaHead V cert.split hopt

end DiagonalSourceSVDTailCertificate

/-- Sketching the exact source head `U Sigma V^T` gives
`U (Sigma (V^T Z))`. -/
theorem columnSketch_sourceSVDFactorMatrix
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    ∀ i a,
      columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a =
        ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
  intro i a
  unfold columnSketch preconditionColumns sourceSVDFactorMatrix
    sourceSVDSketchRightFactor rightSketchCrossGram
  calc
    (∑ k : Fin n,
        (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
          Z k a)
        =
          ∑ k : Fin n, ∑ c : Fin r,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ k : Fin n,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n,
                (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, ∑ d : Fin r,
                (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            apply congrArg (fun x => U i c * x)
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, ∑ k : Fin n,
                (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r,
                Sigma c d * ∑ k : Fin n, V k d * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- The source head sketch is left-orthogonal to the sketched tail when
`U^T Tail = 0`.  This is the cross-term cancellation needed before proving the
head-plus-tail sketch-Gram determinant route. -/
theorem columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Tail : Fin m → Fin n → ℝ)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      ∑ i : Fin m,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          columnSketch Tail Z i b = 0 := by
  intro a b
  have hHead := columnSketch_sourceSVDFactorMatrix U Sigma V Z
  calc
    ∑ i : Fin m,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          columnSketch Tail Z i b
        =
          ∑ i : Fin m,
            (∑ c : Fin r,
              U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (∑ j : Fin n, Tail i j * Z j b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hHead i a]
            rfl
    _ =
          ∑ i : Fin m, ∑ c : Fin r, ∑ j : Fin n,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (Tail i j * Z j b) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
    _ =
          ∑ c : Fin r, ∑ j : Fin n, ∑ i : Fin m,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              (Tail i j * Z j b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r, ∑ j : Fin n,
            (sourceSVDSketchRightFactor Sigma V Z c a * Z j b) *
              (∑ i : Fin m, U i c * Tail i j) := by
            apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro c _
            apply Finset.sum_eq_zero
            intro j _
            rw [hUT c j]
            ring

/-- The sketched tail is left-orthogonal to the source head sketch when
`U^T Tail = 0`; this is the transposed cross-term cancellation. -/
theorem columnSketch_tail_sourceSVDFactorMatrix_leftOrthogonal
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (Tail : Fin m → Fin n → ℝ)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      ∑ i : Fin m,
        columnSketch Tail Z i a *
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b = 0 := by
  intro a b
  have hcross :=
    columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
      U Sigma V Z Tail hUT b a
  calc
    ∑ i : Fin m,
        columnSketch Tail Z i a *
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b
        =
          ∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b *
              columnSketch Tail Z i a := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := hcross

/-- Under the exact source split `A = U Sigma V^T + Tail` and the SVD
orthogonality field `U^T Tail = 0`, the sketch Gram of `A Z` decomposes as the
sum of the source-head sketch Gram and the tail sketch Gram.  This is the first
determinant-route dependency for the head-plus-tail equation (9) proof. -/
theorem columnSketchGram_sourceHeadTail_leftOrthogonal
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail) :
    ∀ a b,
      columnSketchGram A Z a b =
        columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z a b +
          columnSketchGram Tail Z a b := by
  intro a b
  have hAZ :
      ∀ i a,
        columnSketch A Z i a =
          columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a +
            columnSketch Tail Z i a := by
    intro i a
    unfold columnSketch preconditionColumns
    calc
      ∑ j : Fin n, A i j * Z j a
          =
            ∑ j : Fin n,
              (sourceSVDFactorMatrix U Sigma V i j + Tail i j) * Z j a := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hA i j]
      _ =
            ∑ j : Fin n, sourceSVDFactorMatrix U Sigma V i j * Z j a +
              ∑ j : Fin n, Tail i j * Z j a := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
  have hcross₁ :=
    columnSketch_sourceSVDFactorMatrix_tail_leftOrthogonal
      U Sigma V Z Tail hUT a b
  have hcross₂ :=
    columnSketch_tail_sourceSVDFactorMatrix_leftOrthogonal
      U Sigma V Z Tail hUT a b
  unfold columnSketchGram
  calc
    ∑ i : Fin m, columnSketch A Z i a * columnSketch A Z i b
        =
          ∑ i : Fin m,
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a +
              columnSketch Tail Z i a) *
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
              columnSketch Tail Z i b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hAZ i a, hAZ i b]
    _ =
          ∑ i : Fin m,
            (columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch Tail Z i b +
            columnSketch Tail Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b +
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch Tail Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            simp_rw [Finset.sum_add_distrib]
    _ =
          (∑ i : Fin m,
            columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
              columnSketch (sourceSVDFactorMatrix U Sigma V) Z i b) +
          (∑ i : Fin m,
            columnSketch Tail Z i a * columnSketch Tail Z i b) := by
            rw [hcross₁, hcross₂]
            ring

/-- If the exact source-head sketch Gram is positive definite, then the
head-plus-tail sketch Gram is nonsingular under the orthogonal source split.
The tail-Gram PSD part is supplied by `columnSketchGram_finitePSD`; the
remaining source-facing work is to derive the positive definiteness of the
source-head sketch Gram from the full-rank source data. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hHead :
      Matrix.PosDef
        (columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z :
          Matrix (Fin r) (Fin r) ℝ)) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  have hsplit :=
    columnSketchGram_sourceHeadTail_leftOrthogonal
      A Tail Z U Sigma V hA hUT
  have hTailPSD :
      finitePSD (columnSketchGram Tail Z) :=
    columnSketchGram_finitePSD Tail Z
  have hTailMatPSD :
      Matrix.PosSemidef
        (columnSketchGram Tail Z : Matrix (Fin r) (Fin r) ℝ) :=
    finitePSD.to_matrix_posSemidef
      (columnSketchGram Tail Z)
      (columnSketchGram_symmetric Tail Z)
      hTailPSD
  have hdet :=
    matrix_det_ne_zero_of_posDef_add_posSemidef
      (columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z)
      (columnSketchGram Tail Z)
      hHead hTailMatPSD
  have hmat :
      (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) =
        ((fun a b =>
          columnSketchGram (sourceSVDFactorMatrix U Sigma V) Z a b +
            columnSketchGram Tail Z a b) :
          Matrix (Fin r) (Fin r) ℝ) := by
    ext a b
    exact hsplit a b
  rw [hmat]
  exact hdet

/-- Exact source coefficient table `(VᵀZ)^{-1}Vᵀ` for the source equation
(9) route.  This is an analysis object: if an implementation computes the
cross product, inverse, or coefficient table, those are non-probability
computed quantities and require separate FP/inexact-arithmetic certificates. -/
noncomputable def sourceSketchCoefficient {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin n → ℝ :=
  fun a j =>
    ∑ b : Fin r, nonsingInv r (rightSketchCrossGram V Z) a b * V j b

/-- The exact coefficient table `(VᵀZ)^{-1}Vᵀ` reproduces `Vᵀ` after
left multiplication by `VᵀZ`, provided the source cross factor is nonsingular. -/
theorem rightSketchCrossGram_sourceSketchCoefficient
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ a j,
      (∑ b : Fin r,
        rightSketchCrossGram V Z a b * sourceSketchCoefficient V Z b j) =
        V j a := by
  intro a j
  have hright :=
    (isInverse_nonsingInv_of_det_ne_zero r (rightSketchCrossGram V Z) hVZ).2
  unfold sourceSketchCoefficient
  calc
    (∑ b : Fin r,
        rightSketchCrossGram V Z a b *
          (∑ c : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b c * V j c))
        =
          ∑ b : Fin r, ∑ c : Fin r,
            rightSketchCrossGram V Z a b *
              (nonsingInv r (rightSketchCrossGram V Z) b c * V j c) := by
            simp_rw [Finset.mul_sum]
    _ =
          ∑ c : Fin r, ∑ b : Fin r,
            rightSketchCrossGram V Z a b *
              (nonsingInv r (rightSketchCrossGram V Z) b c * V j c) := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            (∑ b : Fin r,
              rightSketchCrossGram V Z a b *
                nonsingInv r (rightSketchCrossGram V Z) b c) * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ∑ c : Fin r, idMatrix r a c * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hright a c]
            rfl
    _ = V j a := by
            simp [idMatrix, Finset.mem_univ]

/-- Multiplying the exact source sketch right factor `Σ(VᵀZ)` by the source
coefficient table `(VᵀZ)^{-1}Vᵀ` recovers `ΣVᵀ`. -/
theorem sourceSVDSketchRightFactor_sourceSketchCoefficient
    {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ a j,
      (∑ b : Fin r,
        sourceSVDSketchRightFactor Sigma V Z a b *
          sourceSketchCoefficient V Z b j) =
        ∑ c : Fin r, Sigma a c * V j c := by
  intro a j
  have hMW := rightSketchCrossGram_sourceSketchCoefficient V Z hVZ
  unfold sourceSVDSketchRightFactor
  calc
    (∑ b : Fin r,
        (∑ c : Fin r, Sigma a c * rightSketchCrossGram V Z c b) *
          sourceSketchCoefficient V Z b j)
        =
          ∑ b : Fin r, ∑ c : Fin r,
            (Sigma a c * rightSketchCrossGram V Z c b) *
              sourceSketchCoefficient V Z b j := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ b : Fin r,
            (Sigma a c * rightSketchCrossGram V Z c b) *
              sourceSketchCoefficient V Z b j := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            Sigma a c *
              (∑ b : Fin r,
                rightSketchCrossGram V Z c b *
                  sourceSketchCoefficient V Z b j) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
    _ = ∑ c : Fin r, Sigma a c * V j c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hMW c j]

/-- The exact source coefficient table reproduces the source SVD head from its
own column sketch. -/
theorem columnSketchHead_sourceSVDFactorMatrix_sourceSketchCoefficient
    {m n r : ℕ}
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ∀ i j,
      columnSketchHead (sourceSVDFactorMatrix U Sigma V) Z
          (sourceSketchCoefficient V Z) i j =
        sourceSVDFactorMatrix U Sigma V i j := by
  intro i j
  have hSketch :
      ∀ i a,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a =
          ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
    intro i a
    unfold columnSketch preconditionColumns sourceSVDFactorMatrix
      sourceSVDSketchRightFactor rightSketchCrossGram
    calc
      (∑ k : Fin n,
          (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
            Z k a)
          =
            ∑ k : Fin n, ∑ c : Fin r,
              (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ c : Fin r, ∑ k : Fin n,
              (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
              rw [Finset.sum_comm]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ k : Fin n, (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ k : Fin n, ∑ d : Fin r, (Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ d : Fin r, ∑ k : Fin n, (Sigma c d * V k d) * Z k a) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              rw [Finset.sum_comm]
      _ =
            ∑ c : Fin r,
              U i c *
                (∑ d : Fin r, Sigma c d *
                  (∑ k : Fin n, V k d * Z k a)) := by
              apply Finset.sum_congr rfl
              intro c _
              congr 1
              apply Finset.sum_congr rfl
              intro d _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  have hCoeff :=
    sourceSVDSketchRightFactor_sourceSketchCoefficient Sigma V Z hVZ
  unfold columnSketchHead sourceSVDFactorMatrix
  calc
    (∑ a : Fin r,
        columnSketch (sourceSVDFactorMatrix U Sigma V) Z i a *
          sourceSketchCoefficient V Z a j)
        =
          ∑ a : Fin r,
            (∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hSketch i a]
    _ =
          ∑ a : Fin r, ∑ c : Fin r,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ a : Fin r,
            (U i c * sourceSVDSketchRightFactor Sigma V Z c a) *
              sourceSketchCoefficient V Z a j := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ a : Fin r,
                sourceSVDSketchRightFactor Sigma V Z c a *
                  sourceSketchCoefficient V Z a j) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ =
          ∑ c : Fin r, U i c *
            (∑ d : Fin r, Sigma c d * V j d) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hCoeff c j]


























































/-- For a source head/tail split `A = UΣVᵀ + T`, the source coefficient table
rewrites the displayed sketch head as the exact source head plus the sketched
tail contribution. -/
theorem columnSketchHead_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    ∀ i j,
      columnSketchHead A Z (sourceSketchCoefficient V Z) i j =
        sourceSVDFactorMatrix U Sigma V i j +
          columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
  intro i j
  have hAZ :=
    columnSketch_eq_add_of_eq_add A (sourceSVDFactorMatrix U Sigma V) Tail Z hA
  have hAdd :=
    columnSketchHead_eq_add_of_columnSketch_eq_add
      A (sourceSVDFactorMatrix U Sigma V) Tail Z
      (sourceSketchCoefficient V Z) hAZ
  have hHead :=
    columnSketchHead_sourceSVDFactorMatrix_sourceSketchCoefficient
      U Sigma V Z hVZ
  calc
    columnSketchHead A Z (sourceSketchCoefficient V Z) i j
        =
          columnSketchHead (sourceSVDFactorMatrix U Sigma V) Z
              (sourceSketchCoefficient V Z) i j +
            columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
            rw [hAdd i j]
    _ =
          sourceSVDFactorMatrix U Sigma V i j +
            columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j := by
            rw [hHead i j]

/-- Explicit source residual tail induced by the paper's coefficient table:
`T - (T Z)(VᵀZ)^{-1}Vᵀ`. -/
noncomputable def sourceSketchResidualTail {m n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    Tail i j - columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j






















































































/-- Exact source-SVD-style factors with orthonormal left and right column
tables preserve the squared Frobenius norm of the displayed middle block.
This is a local SVD-norm identity on the Eckart--Young route; it assumes the
exact singular-vector tables and does not construct or compute them. -/
theorem frobNormSqRect_sourceSVDFactorMatrix_orthonormal
    {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (Sigma : Fin q → Fin q → ℝ)
    (V : Fin n → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b)
    (hV : ∀ a b, ∑ j : Fin n, V j a * V j b = idMatrix q a b) :
    frobNormSqRect (sourceSVDFactorMatrix U Sigma V) =
      frobNormSq Sigma := by
  have hleft :
      frobNormSqRect (sourceSVDFactorMatrix U Sigma V) =
        frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) := by
    simpa [sourceSVDFactorMatrix] using
      (frobNormSqRect_leftOrthonormalFactor U
        (fun a j => ∑ b : Fin q, Sigma a b * V j b) hU)
  have hright :
      frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) =
        frobNormSqRect Sigma := by
    have h :=
      finiteFrobNormSq_rectRightOrthonormal
        (m := q) (n := q) (κ := Fin n)
        Sigma (fun b j => V j b) hV
    simpa [finiteFrobNormSq_fin] using h
  calc
    frobNormSqRect (sourceSVDFactorMatrix U Sigma V)
        = frobNormSqRect (fun a j => ∑ b : Fin q, Sigma a b * V j b) :=
          hleft
    _ = frobNormSqRect Sigma := hright
    _ = frobNormSq Sigma := frobNormSqRect_eq_frobNormSq Sigma

/-- Norm form of `frobNormSqRect_sourceSVDFactorMatrix_orthonormal`. -/
theorem frobNormRect_sourceSVDFactorMatrix_orthonormal
    {m n q : ℕ}
    (U : Fin m → Fin q → ℝ) (Sigma : Fin q → Fin q → ℝ)
    (V : Fin n → Fin q → ℝ)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix q a b)
    (hV : ∀ a b, ∑ j : Fin n, V j a * V j b = idMatrix q a b) :
    frobNormRect (sourceSVDFactorMatrix U Sigma V) =
      frobNorm Sigma := by
  unfold frobNormRect
  rw [frobNormSqRect_sourceSVDFactorMatrix_orthonormal U Sigma V hU hV]
  rw [frobNorm_eq_sqrt_frobNormSq]

/-- If the source tail factors as `Tail = Utail * TailCoord`, then the exact
source residual tail factors through the same left basis. -/
theorem sourceSketchResidualTail_leftFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j) :
    ∀ i j,
      sourceSketchResidualTail Tail Z V i j =
        ∑ a : Fin q, Utail i a *
          sourceSketchResidualTail TailCoord Z V a j := by
  intro i j
  have hSketch :
      ∀ i b,
        columnSketch Tail Z i b =
          ∑ a : Fin q, Utail i a * columnSketch TailCoord Z a b := by
    intro i b
    unfold columnSketch preconditionColumns
    calc
      (∑ k : Fin n, Tail i k * Z k b)
          =
            ∑ k : Fin n,
              (∑ a : Fin q, Utail i a * TailCoord a k) * Z k b := by
              apply Finset.sum_congr rfl
              intro k _
              rw [hTail i k]
      _ =
            ∑ k : Fin n, ∑ a : Fin q,
              (Utail i a * TailCoord a k) * Z k b := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ =
            ∑ a : Fin q, ∑ k : Fin n,
              (Utail i a * TailCoord a k) * Z k b := by
              rw [Finset.sum_comm]
      _ =
            ∑ a : Fin q, Utail i a *
              (∑ k : Fin n, TailCoord a k * Z k b) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
  have hHead :
      columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j =
        ∑ a : Fin q, Utail i a *
          columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j := by
    unfold columnSketchHead
    calc
      (∑ b : Fin r, columnSketch Tail Z i b *
          sourceSketchCoefficient V Z b j)
          =
            ∑ b : Fin r,
              (∑ a : Fin q, Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hSketch i b]
      _ =
            ∑ b : Fin r, ∑ a : Fin q,
              (Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ a : Fin q, ∑ b : Fin r,
              (Utail i a * columnSketch TailCoord Z a b) *
                sourceSketchCoefficient V Z b j := by
              rw [Finset.sum_comm]
      _ =
            ∑ a : Fin q, Utail i a *
              (∑ b : Fin r,
                columnSketch TailCoord Z a b *
                  sourceSketchCoefficient V Z b j) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b _
              ring
  unfold sourceSketchResidualTail
  calc
    Tail i j - columnSketchHead Tail Z (sourceSketchCoefficient V Z) i j
        =
          (∑ a : Fin q, Utail i a * TailCoord a j) -
            ∑ a : Fin q, Utail i a *
              columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j := by
            rw [hTail i j, hHead]
    _ =
          ∑ a : Fin q, Utail i a *
            (TailCoord a j -
              columnSketchHead TailCoord Z (sourceSketchCoefficient V Z) a j) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a _
            ring

/-- The source residual-tail Frobenius norm reduces exactly to the coordinate
tail residual whenever the tail left factor has orthonormal columns. -/
theorem frobNormSqRect_sourceSketchResidualTail_leftOrthonormalFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b) :
    frobNormSqRect (sourceSketchResidualTail Tail Z V) =
      frobNormSqRect (sourceSketchResidualTail TailCoord Z V) := by
  have hres :=
    sourceSketchResidualTail_leftFactor Tail Utail TailCoord Z V hTail
  calc
    frobNormSqRect (sourceSketchResidualTail Tail Z V)
        =
          frobNormSqRect
            (fun i j => ∑ a : Fin q, Utail i a *
              sourceSketchResidualTail TailCoord Z V a j) := by
            congr 1
            funext i j
            exact hres i j
    _ =
          frobNormSqRect (sourceSketchResidualTail TailCoord Z V) :=
            frobNormSqRect_leftOrthonormalFactor Utail
              (sourceSketchResidualTail TailCoord Z V) hUtail

/-- Norm form of the source residual-tail reduction through an orthonormal
left tail basis. -/
theorem frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor
    {m q n r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ) (TailCoord : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hTail :
      ∀ i j, Tail i j = ∑ a : Fin q, Utail i a * TailCoord a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b) :
    frobNormRect (sourceSketchResidualTail Tail Z V) =
      frobNormRect (sourceSketchResidualTail TailCoord Z V) := by
  unfold frobNormRect
  rw [frobNormSqRect_sourceSketchResidualTail_leftOrthonormalFactor
    Tail Utail TailCoord Z V hTail hUtail]

/-- Transposed row representation of an exact right tail basis `Vperp`.
This is an exact analysis object; computed right bases in an implementation
need separate non-probability FP certificates. -/
def sourceRightBasisTranspose {n q : ℕ}
    (Vperp : Fin n → Fin q → ℝ) : Fin q → Fin n → ℝ :=
  fun a j => Vperp j a







/-- Floating-point rectangular cross factor computed as the matrix product
`fl((Vperpᵀ) Z)`.  This is a concrete non-probability computation; the
sampling law defining `Z` remains an exact mathematical input. -/
noncomputable def flRightSketchCrossGramRect (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin q → Fin r → ℝ :=
  fl_matMul fp q n r (sourceRightBasisTranspose Vperp) Z








/-- Entrywise floating-point dot-product error for the computed rectangular
cross factor `fl((Vperpᵀ)Z)`. -/
theorem rightSketchCrossGramRect_flMatMul_entry_abs_error_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a b,
      |rightSketchCrossGramRect Vperp Z a b -
          flRightSketchCrossGramRect fp Vperp Z a b| ≤
        rightSketchCrossGramRectDotBudget fp Vperp Z a b := by
  intro a b
  have hdot :=
    matMul_error_bound fp q n r (sourceRightBasisTranspose Vperp) Z hγ a b
  simpa [rightSketchCrossGramRect, flRightSketchCrossGramRect,
    rightSketchCrossGramRectDotBudget, sourceRightBasisTranspose,
    abs_sub_comm] using hdot

/-- Summed left-component certificate induced by the concrete floating-point
cross-gram computation. -/
theorem rightSketchCrossGramRect_flMatMul_component_left_error_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ)
    (Y : Fin r → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a c,
      ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |Y b c| ≤
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b * |Y b c| := by
  intro a c
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_right
    (rightSketchCrossGramRect_flMatMul_entry_abs_error_le fp Vperp Z hγ a b)
    (abs_nonneg _)

/-- Floating-point square cross Gram computed as `fl((Vᵀ)Z)`.  This is the
computed non-probability input that an inverse routine would consume when
forming an approximation to `(Vᵀ Z)^{-1}`. -/
noncomputable def flRightSketchCrossGram (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ) :
    Fin r → Fin r → ℝ :=
  flRightSketchCrossGramRect fp V Z







/-- Entrywise floating-point dot-product error for the computed square cross
Gram `fl((Vᵀ)Z)`. -/
theorem rightSketchCrossGram_flMatMul_entry_abs_error_le
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hγ : gammaValid fp n) :
    ∀ a b,
      |rightSketchCrossGram V Z a b -
          flRightSketchCrossGram fp V Z a b| ≤
        rightSketchCrossGramDotBudget fp V Z a b := by
  intro a b
  simpa [rightSketchCrossGram, rightSketchCrossGramRect,
    flRightSketchCrossGram, rightSketchCrossGramDotBudget] using
    rightSketchCrossGramRect_flMatMul_entry_abs_error_le fp V Z hγ a b

/-- Uniform-budget Frobenius certificate for the computed square cross Gram
`fl((Vᵀ)Z)`.  This is an inverse-routine input certificate, not yet an inverse
routine perturbation theorem. -/
theorem frobNorm_rightSketchCrossGram_sub_flMatMul_le_of_dotBudget_le
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    {omega : ℝ}
    (hγ : gammaValid fp n)
    (homega : 0 ≤ omega)
    (hBudget :
      ∀ a b, rightSketchCrossGramDotBudget fp V Z a b ≤ omega) :
    frobNorm
        (fun a b => rightSketchCrossGram V Z a b -
          flRightSketchCrossGram fp V Z a b) ≤
      Real.sqrt ((r : ℝ) * (r : ℝ)) * omega := by
  rw [← frobNormRect_eq_frobNorm]
  exact
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGram V Z a b -
        flRightSketchCrossGram fp V Z a b)
      homega
      (fun a b =>
        le_trans
          (rightSketchCrossGram_flMatMul_entry_abs_error_le fp V Z hγ a b)
          (hBudget a b))

/-- Sketching the transposed right tail basis gives the rectangular cross
factor `Vperpᵀ Z`. -/
theorem columnSketch_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ) (Z : Fin n → Fin r → ℝ) :
    ∀ a b,
      columnSketch (sourceRightBasisTranspose Vperp) Z a b =
        rightSketchCrossGramRect Vperp Z a b := by
  intro a b
  rfl

/-- The exact sketch head of `Vperpᵀ` with the source coefficient table is
`(Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ`. -/
theorem columnSketchHead_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      columnSketchHead (sourceRightBasisTranspose Vperp) Z
          (sourceSketchCoefficient V Z) a j =
        ∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j := by
  intro a j
  unfold columnSketchHead
  apply Finset.sum_congr rfl
  intro b _
  rw [columnSketch_sourceRightBasisTranspose Vperp Z a b]

/-- Coordinate residual identity for the right tail basis:
`Vperpᵀ - (Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ`. -/
theorem sourceSketchResidualTail_sourceRightBasisTranspose
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j =
        Vperp j a -
          ∑ b : Fin r,
            rightSketchCrossGramRect Vperp Z a b *
              sourceSketchCoefficient V Z b j := by
  intro a j
  unfold sourceSketchResidualTail
  rw [columnSketchHead_sourceRightBasisTranspose Vperp Z V a j]
  rfl

/-- If the coordinate tail is `Sigma * R`, then the source residual tail is
`Sigma` times the residual of `R`. -/
theorem sourceSketchResidualTail_leftSquareFactor
    {q n r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (R : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail (matMulRectLeft Sigma R) Z V a j =
        matMulRectLeft Sigma (sourceSketchResidualTail R Z V) a j := by
  intro a j
  simpa [matMulRectLeft] using
    (sourceSketchResidualTail_leftFactor
      (matMulRectLeft Sigma R) Sigma R Z V (by intro i k; rfl) a j)

/-- Frobenius submultiplicative bound for the preceding coordinate-tail
factorization.  This is a non-sharp but explicit foundation step toward the
equation (9) source-tail bound; the sharp spectral/unitarily invariant version
remains a separate obligation. -/
theorem frobNormRect_sourceSketchResidualTail_leftSquareFactor_le
    {q n r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (R : Fin q → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    frobNormRect (sourceSketchResidualTail (matMulRectLeft Sigma R) Z V) ≤
      frobNorm Sigma * frobNormRect (sourceSketchResidualTail R Z V) := by
  have hfact :
      sourceSketchResidualTail (matMulRectLeft Sigma R) Z V =
        matMulRectLeft Sigma (sourceSketchResidualTail R Z V) := by
    funext a j
    exact sourceSketchResidualTail_leftSquareFactor Sigma R Z V a j
  rw [hfact]
  exact frobNormRect_matMulRectLeft_le Sigma (sourceSketchResidualTail R Z V)

/-- Explicit `Sigma_perp Vperpᵀ` coordinate residual factorization:
`Sigma_perp (Vperpᵀ - (Vperpᵀ Z)(Vᵀ Z)^{-1}Vᵀ)`. -/
theorem sourceSketchResidualTail_sigmaRightBasisTranspose_explicit
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    ∀ a j,
      sourceSketchResidualTail
          (matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)) Z V a j =
        ∑ c : Fin q, Sigma a c *
          (Vperp j c -
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z c b *
                sourceSketchCoefficient V Z b j) := by
  intro a j
  rw [sourceSketchResidualTail_leftSquareFactor Sigma
    (sourceRightBasisTranspose Vperp) Z V a j]
  unfold matMulRectLeft
  apply Finset.sum_congr rfl
  intro c _
  rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V c j]

/-- Frobenius bound for the explicit `Sigma_perp Vperpᵀ` coordinate residual
factorization. -/
theorem frobNormRect_sourceSketchResidualTail_sigmaRightBasisTranspose_le
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ) :
    frobNormRect
        (sourceSketchResidualTail
          (matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)) Z V) ≤
      frobNorm Sigma *
        frobNormRect (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) :=
  frobNormRect_sourceSketchResidualTail_leftSquareFactor_le
    Sigma (sourceRightBasisTranspose Vperp) Z V












/-- The exact source coefficient table annihilates the right-tail basis when
the head and tail right bases are exactly orthogonal. -/
theorem sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero
    {n q r : ℕ}
    (V : Fin n → Fin r → ℝ) (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (hcross : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) :
    ∀ b c,
      (∑ j : Fin n, sourceSketchCoefficient V Z b j * Vperp j c) = 0 := by
  intro b c
  unfold sourceSketchCoefficient
  calc
    (∑ j : Fin n,
        (∑ d : Fin r,
          nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
          Vperp j c)
        =
          ∑ j : Fin n, ∑ d : Fin r,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              Vperp j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ d : Fin r, ∑ j : Fin n,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              Vperp j c := by
            rw [Finset.sum_comm]
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d *
              (∑ j : Fin n, V j d * Vperp j c) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d * 0 := by
            apply Finset.sum_congr rfl
            intro d _
            rw [hcross d c]
    _ = 0 := by simp

/-- Multiplying the exact source coefficient table by the head right basis
recovers the displayed inverse factor, provided the head right basis has
orthonormal columns. -/
theorem sourceSketchCoefficient_mul_headRightBasis_of_orthonormal
    {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ b c,
      (∑ j : Fin n, sourceSketchCoefficient V Z b j * V j c) =
        nonsingInv r (rightSketchCrossGram V Z) b c := by
  intro b c
  unfold sourceSketchCoefficient
  calc
    (∑ j : Fin n,
        (∑ d : Fin r,
          nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
          V j c)
        =
          ∑ j : Fin n, ∑ d : Fin r,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              V j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ =
          ∑ d : Fin r, ∑ j : Fin n,
            (nonsingInv r (rightSketchCrossGram V Z) b d * V j d) *
              V j c := by
            rw [Finset.sum_comm]
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d *
              (∑ j : Fin n, V j d * V j c) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ =
          ∑ d : Fin r,
            nonsingInv r (rightSketchCrossGram V Z) b d * idMatrix r d c := by
            apply Finset.sum_congr rfl
            intro d _
            rw [hV d c]
    _ = nonsingInv r (rightSketchCrossGram V Z) b c := by
            simp [idMatrix, Finset.mem_univ]

/-- Right-multiplying the exact right-tail residual by `Vperp` gives the
identity block under exact right-tail orthonormality and head/tail
orthogonality. -/
theorem sourceRightResidual_mul_rightTailBasis_eq_id
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcross : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0) :
    ∀ a c,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          Vperp j c) =
        idMatrix q a c := by
  intro a c
  have hWperp :=
    sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero V Vperp Z hcross
  have htail :
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          Vperp j c) = 0 := by
    calc
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          Vperp j c)
          =
            ∑ b : Fin r, ∑ j : Fin n,
              (rightSketchCrossGramRect Vperp Z a b *
                sourceSketchCoefficient V Z b j) *
                Vperp j c := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                (∑ j : Fin n, sourceSketchCoefficient V Z b j * Vperp j c) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b * 0 := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hWperp b c]
      _ = 0 := by simp
  calc
    (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          Vperp j c)
        =
          ∑ j : Fin n,
            (Vperp j a -
              ∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
              Vperp j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V a j]
    _ =
          (∑ j : Fin n, Vperp j a * Vperp j c) -
            ∑ j : Fin n,
              (∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
                Vperp j c := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = idMatrix q a c := by
            rw [hVperp a c, htail, sub_zero]

/-- Right-multiplying the exact right-tail residual by the head right basis
gives the negative `(Vperpᵀ Z)(Vᵀ Z)^{-1}` block. -/
theorem sourceRightResidual_mul_headRightBasis_eq_neg_invFactor
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hcross : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a c,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          V j c) =
        - rightSketchCrossGramRectInvFactor Vperp Z V a c := by
  intro a c
  have hWV :=
    sourceSketchCoefficient_mul_headRightBasis_of_orthonormal V Z hV
  have htail :
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          V j c) =
        rightSketchCrossGramRectInvFactor Vperp Z V a c := by
    unfold rightSketchCrossGramRectInvFactor
    calc
      (∑ j : Fin n,
        (∑ b : Fin r,
          rightSketchCrossGramRect Vperp Z a b *
            sourceSketchCoefficient V Z b j) *
          V j c)
          =
            ∑ b : Fin r, ∑ j : Fin n,
              (rightSketchCrossGramRect Vperp Z a b *
                sourceSketchCoefficient V Z b j) *
                V j c := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_mul]
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                (∑ j : Fin n, sourceSketchCoefficient V Z b j * V j c) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ =
            ∑ b : Fin r,
              rightSketchCrossGramRect Vperp Z a b *
                nonsingInv r (rightSketchCrossGram V Z) b c := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hWV b c]
  calc
    (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          V j c)
        =
          ∑ j : Fin n,
            (Vperp j a -
              ∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
              V j c := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sourceSketchResidualTail_sourceRightBasisTranspose Vperp Z V a j]
    _ =
          (∑ j : Fin n, Vperp j a * V j c) -
            ∑ j : Fin n,
              (∑ b : Fin r,
                rightSketchCrossGramRect Vperp Z a b *
                  sourceSketchCoefficient V Z b j) *
                V j c := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = - rightSketchCrossGramRectInvFactor Vperp Z V a c := by
            rw [hcross a c, htail]
            ring


































































































































































































































































































































/-- The right-tail residual block `[I, -M]` that appears after multiplying
`R_perp = Vperpᵀ - (Vperpᵀ Z)(VᵀZ)^{-1}Vᵀ` by the full right-basis block. -/
noncomputable def sourceRightResidualBlock {q r : ℕ}
    (M : Fin q → Fin r → ℝ) : Fin q → (Fin q ⊕ Fin r) → ℝ :=
  fun a bc =>
    match bc with
    | Sum.inl c => idMatrix q a c
    | Sum.inr c => -M a c












































/-- Multiplying the exact right-tail residual by the concatenated right-basis
block gives `[I, -M]`, where `M=(Vperpᵀ Z)(VᵀZ)^{-1}`. -/
theorem sourceRightResidual_rightBasisBlock_eq_block
    {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a bc,
      (∑ j : Fin n,
        sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V a j *
          rightBasisBlock Vperp V j bc) =
        sourceRightResidualBlock
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
  intro a bc
  cases bc with
  | inl c =>
      simpa [rightBasisBlock, sourceRightResidualBlock] using
        sourceRightResidual_mul_rightTailBasis_eq_id
          Vperp Z V hVperp hcrossTail a c
  | inr c =>
      simpa [rightBasisBlock, sourceRightResidualBlock] using
        sourceRightResidual_mul_headRightBasis_eq_neg_invFactor
          Vperp Z V hcrossHead hV a c

/-- The singular-value-weighted right-tail residual, multiplied by the
concatenated right-basis block, is `[Sigma, -Sigma M]`. -/
theorem sourceRightResidual_sigma_rightBasisBlock_eq_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c) :
    ∀ a bc,
      (∑ j : Fin n,
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
          rightBasisBlock Vperp V j bc) =
        sigmaRightResidualBlock Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
  intro a bc
  have hblock :=
    sourceRightResidual_rightBasisBlock_eq_block
      Vperp Z V hVperp hcrossTail hcrossHead hV
  calc
    (∑ j : Fin n,
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
          rightBasisBlock Vperp V j bc)
        =
          ∑ c : Fin q, Sigma a c *
            (∑ j : Fin n,
              sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V c j *
                rightBasisBlock Vperp V j bc) := by
            unfold matMulRectLeft
            calc
              (∑ j : Fin n,
                  (∑ c : Fin q,
                    Sigma a c *
                      sourceSketchResidualTail
                        (sourceRightBasisTranspose Vperp) Z V c j) *
                    rightBasisBlock Vperp V j bc)
                  =
                    ∑ j : Fin n, ∑ c : Fin q,
                      (Sigma a c *
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j) *
                        rightBasisBlock Vperp V j bc := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_mul]
              _ =
                    ∑ c : Fin q, ∑ j : Fin n,
                      (Sigma a c *
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j) *
                        rightBasisBlock Vperp V j bc := by
                      rw [Finset.sum_comm]
              _ =
                    ∑ c : Fin q, Sigma a c *
                      (∑ j : Fin n,
                        sourceSketchResidualTail
                          (sourceRightBasisTranspose Vperp) Z V c j *
                          rightBasisBlock Vperp V j bc) := by
                      apply Finset.sum_congr rfl
                      intro c _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
    _ =
          ∑ c : Fin q, Sigma a c *
            sourceRightResidualBlock
              (rightSketchCrossGramRectInvFactor Vperp Z V) c bc := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hblock c bc]
    _ =
        sigmaRightResidualBlock Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V) a bc := by
            cases bc with
            | inl d =>
                simp [sourceRightResidualBlock, sigmaRightResidualBlock,
                  idMatrix, Finset.mem_univ]
            | inr d =>
                unfold sourceRightResidualBlock sigmaRightResidualBlock
                unfold matMulRectLeft
                change
                  (∑ c : Fin q,
                    Sigma a c *
                      (-(rightSketchCrossGramRectInvFactor Vperp Z V c d))) =
                    -(∑ c : Fin q,
                      Sigma a c *
                        rightSketchCrossGramRectInvFactor Vperp Z V c d)
                rw [← Finset.sum_neg_distrib]
                apply Finset.sum_congr rfl
                intro c _
                ring

/-- Squared Frobenius identity for the singular-value-weighted coordinate
right-tail residual after the exact right-basis block is supplied as complete.

This is the exact-object Frobenius/right-orthogonal invariance step following
LR.1w.  It still leaves the sharp spectral/unitarily invariant bound on
`Sigma * (Vperpᵀ Z)(VᵀZ)^{-1}` as the next analytic obligation. -/
theorem frobNormSqRect_sigma_sourceRightResidual_eq_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    frobNormSqRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) =
      frobNormSq Sigma +
        frobNormSqRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) := by
  let R := sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V
  let Q := rightBasisBlock Vperp V
  let M := rightSketchCrossGramRectInvFactor Vperp Z V
  have hQ :
      ∀ j k,
        ∑ bc : Fin q ⊕ Fin r, Q j bc * Q k bc = idMatrix n j k := by
    intro j k
    exact rightBasisBlock_row_orthonormal_of_sum Vperp V hcomplete j k
  have hinv :
      finiteFrobNormSq
          (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) =
        frobNormSqRect (matMulRectLeft Sigma R) :=
    finiteFrobNormSq_rectRightOrthonormal (matMulRectLeft Sigma R) Q hQ
  have hprod :
      finiteFrobNormSq
          (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) =
        finiteFrobNormSq (sigmaRightResidualBlock Sigma M) := by
    unfold finiteFrobNormSq
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro bc _
    have hentry :
        (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) a bc =
          sigmaRightResidualBlock Sigma M a bc := by
      change
        (∑ j : Fin n,
          matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) a j *
            rightBasisBlock Vperp V j bc) =
          sigmaRightResidualBlock Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V) a bc
      exact sourceRightResidual_sigma_rightBasisBlock_eq_block
        Sigma Vperp Z V hVperp hcrossTail hcrossHead hV a bc
    rw [hentry]
  calc
    frobNormSqRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V))
        =
          finiteFrobNormSq
            (fun a bc => ∑ j : Fin n, matMulRectLeft Sigma R a j * Q j bc) := by
            rw [hinv]
    _ = finiteFrobNormSq (sigmaRightResidualBlock Sigma M) := hprod
    _ = frobNormSq Sigma +
          frobNormSqRect
            (matMulRectLeft Sigma
              (rightSketchCrossGramRectInvFactor Vperp Z V)) := by
            exact finiteFrobNormSq_sigmaRightResidualBlock Sigma M

/-- Norm form of the singular-value-weighted right-tail residual block
identity. -/
theorem frobNormRect_sigma_sourceRightResidual_eq_sqrt_block
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) =
      Real.sqrt
        (frobNormSq Sigma +
          frobNormSqRect
            (matMulRectLeft Sigma
              (rightSketchCrossGramRectInvFactor Vperp Z V))) := by
  unfold frobNormRect
  rw [frobNormSqRect_sigma_sourceRightResidual_eq_block
    Sigma Vperp Z V hVperp hcrossTail hcrossHead hV hcomplete]

/-- Source-facing Frobenius tail bound from the CACM equation-(9) cross-term
certificate.  The bound on
`Sigma * (Vperpᵀ Z)(VᵀZ)^{-1}` is a structural exact-object hypothesis of the
paper statement; it is not derived from probability construction or from the
full-rank condition alone. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  let M := rightSketchCrossGramRectInvFactor Vperp Z V
  let Cross := matMulRectLeft Sigma M
  have hSigma_nonneg : 0 ≤ frobNorm Sigma := frobNorm_nonneg Sigma
  have hCross_nonneg : 0 ≤ frobNormRect Cross := frobNormRect_nonneg Cross
  have hepsSigma_nonneg : 0 ≤ eps * frobNorm Sigma :=
    mul_nonneg heps hSigma_nonneg
  have hCross_sq :
      frobNormRect Cross ^ 2 ≤ (eps * frobNorm Sigma) ^ 2 := by
    have habs :
        |frobNormRect Cross| ≤ |eps * frobNorm Sigma| := by
      simpa [Cross, M, abs_of_nonneg hCross_nonneg,
        abs_of_nonneg hepsSigma_nonneg] using hcrossTerm
    exact (sq_le_sq).mpr habs
  have hCross_sq' :
      frobNormRect Cross ^ 2 ≤ eps ^ 2 * frobNorm Sigma ^ 2 := by
    calc
      frobNormRect Cross ^ 2 ≤ (eps * frobNorm Sigma) ^ 2 := hCross_sq
      _ = eps ^ 2 * frobNorm Sigma ^ 2 := by ring
  have hradicand :
      frobNormSq Sigma + frobNormSqRect Cross ≤
        (1 + eps ^ 2) * frobNorm Sigma ^ 2 := by
    rw [← frobNorm_sq Sigma, ← frobNormRect_sq Cross]
    nlinarith [hCross_sq']
  calc
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V))
        =
          Real.sqrt (frobNormSq Sigma + frobNormSqRect Cross) := by
            simpa [M, Cross] using
              frobNormRect_sigma_sourceRightResidual_eq_sqrt_block
                Sigma Vperp Z V hVperp hcrossTail hcrossHead hV hcomplete
    _ ≤ Real.sqrt ((1 + eps ^ 2) * frobNorm Sigma ^ 2) :=
          Real.sqrt_le_sqrt hradicand
    _ = Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
          have hfactor : 0 ≤ 1 + eps ^ 2 := by
            nlinarith [sq_nonneg eps]
          rw [Real.sqrt_mul hfactor (frobNorm Sigma ^ 2),
            Real.sqrt_sq_eq_abs, abs_of_nonneg hSigma_nonneg]

/-- Source-facing Frobenius tail bound from a single exact orthonormality
certificate for the concatenated right-basis block `[Vperp,V]`.  The theorem
derives the component right-basis hypotheses and row-completeness internally,
then applies the source cross-term certificate. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hcols :
      ∀ bc bd : Fin q ⊕ Fin r,
        (∑ j : Fin n,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
          if bc = bd then 1 else 0)
    (hrows :
      ∀ j k,
        (∑ bc : Fin q ⊕ Fin r,
          rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
          idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hfields :=
    rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
      Vperp V hcols
  have hcomplete :=
    rightBasisBlock_complete_sum_of_row_orthonormal Vperp V hrows
  exact
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
      Sigma Vperp Z V heps hfields.1 hfields.2.1 hfields.2.2.1
      hfields.2.2.2 hcomplete hcrossTerm

/-- Source-facing Frobenius tail bound through the assembled block certificate:
separate SVD-style component right-basis fields and row-completeness first
assemble exact column/row orthonormality of `[Vperp,V]`, then feed the
block-certificate theorem. -/
theorem frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_component_block_assembly
    {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hblock :=
    rightBasisBlock_col_row_orthonormal_of_component_fields
      Vperp V hVperp hcrossTail hcrossHead hV hcomplete
  exact
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal
      Sigma Vperp Z V heps hblock.1 hblock.2 hcrossTerm

/-- Ambient source-tail Frobenius certificate obtained by composing the
left-orthonormal tail reduction with the exact coordinate
`Sigma_perp Vperpᵀ` residual factorization and the source cross-term
certificate.

This theorem is still an exact-object result.  It assumes the source tail has
already been represented as `Utail * Sigma * Vperpᵀ`, with `Utail` exactly
left-orthonormal, and it assumes the CACM equation-(9) Frobenius cross-term
bound as a visible certificate.  Computed SVD/basis/projector/Gram/inverse and
product routines require separate non-probability FP certificates. -/
theorem frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect (sourceSketchResidualTail Tail Z V) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  let TailCoord := matMulRectLeft Sigma (sourceRightBasisTranspose Vperp)
  have hleft :
      frobNormRect (sourceSketchResidualTail Tail Z V) =
        frobNormRect (sourceSketchResidualTail TailCoord Z V) :=
    frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor
      Tail Utail TailCoord Z V hTail hUtail
  have hcoord :
      sourceSketchResidualTail TailCoord Z V =
        matMulRectLeft Sigma
          (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V) := by
    funext a j
    exact sourceSketchResidualTail_leftSquareFactor
      Sigma (sourceRightBasisTranspose Vperp) Z V a j
  have hsource :
      frobNormRect
          (matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) ≤
        Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
    frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq
      Sigma Vperp Z V heps hVperp hcrossTail hcrossHead hV hcomplete hcrossTerm
  calc
    frobNormRect (sourceSketchResidualTail Tail Z V)
        = frobNormRect (sourceSketchResidualTail TailCoord Z V) := hleft
    _ =
        frobNormRect
          (matMulRectLeft Sigma
            (sourceSketchResidualTail (sourceRightBasisTranspose Vperp) Z V)) := by
          rw [hcoord]
    _ ≤ Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := hsource

/-- The canonical `columnSketchTail A Z W` becomes the source residual tail
`T - (T Z)(VᵀZ)^{-1}Vᵀ` when `W=(VᵀZ)^{-1}Vᵀ` and
`A = UΣVᵀ + T`. -/
theorem columnSketchTail_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j) :
    ∀ i j,
      columnSketchTail A Z (sourceSketchCoefficient V Z) i j =
        sourceSketchResidualTail Tail Z V i j := by
  intro i j
  have hHead :=
    columnSketchHead_sourceHeadTail_sourceSketchCoefficient
      A Tail U Sigma V Z hVZ hA
  unfold columnSketchTail sourceSketchResidualTail
  rw [hA i j, hHead i j]
  ring

/-- Source-head/tail instantiation of the equation (9) head/tail certificate
using the explicit coefficient table `(VᵀZ)^{-1}Vᵀ`.  The theorem leaves the
two analytic Frobenius bounds as visible obligations. -/
noncomputable def equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    Equation9HeadTailSketchCertificate A Z P_AZ
      (columnSketchHead A Z (sourceSketchCoefficient V Z))
      (sourceSketchResidualTail Tail Z V) tail coupling where
  split := by
    intro i j
    have hHead :=
      columnSketchHead_sourceHeadTail_sourceSketchCoefficient
        A Tail U Sigma V Z hVZ hA
    unfold sourceSketchResidualTail
    rw [hA i j, hHead i j]
    ring
  head_factor :=
    columnSketchHead_headFactorization A Z (sourceSketchCoefficient V Z)
  tail_nonneg := htail_nonneg
  coupling_nonneg := hcoupling_nonneg
  tail_bound := htail
  coupling_bound := hcoupling

/-- Generic rank/residual surface for the source-head/tail coefficient route.
The projector is supplied by exact certificates; this result does not assume a
concrete Gram inverse for the full head-plus-tail sketch. -/
theorem equation9RankResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hleft : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a =
        columnSketch A Z i a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤ tail + coupling :=
  equation9HeadTailSketchRankResidualSurface
    A Z P_AZ
    (columnSketchHead A Z (sourceSketchCoefficient V Z))
    (sourceSketchResidualTail Tail Z V) tail coupling
    hleft hrepr
    (equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z P_AZ U Sigma V tail coupling hVZ hA
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual surface for the source-head/tail coefficient route,
conditional on a certified best-rank approximation and a scalar comparison of
the two visible source-tail radii. -/
theorem equation9RelativeResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (P_AZ : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hleft : LeftFactorThrough P_AZ (columnSketch A Z))
    (hrepr :
      ∀ i a, preconditionRows P_AZ (columnSketch A Z) i a =
        columnSketch A Z i a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows P_AZ (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r (preconditionRows P_AZ A) ∧
      lowRankResidualFrob A (preconditionRows P_AZ A) ≤
        rho * lowRankResidualFrob A Ak :=
  equation9HeadTailSketchRelativeResidualSurface
    Z P_AZ
    (columnSketchHead A Z (sourceSketchCoefficient V Z))
    (sourceSketchResidualTail Tail Z V) tail coupling rho
    hbest hleft hrepr
    (equation9HeadTailSketchCertificate_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z P_AZ U Sigma V tail coupling hVZ hA
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- If `A = U Σ Vᵀ`, then the exact column sketch factors as
`A Z = U (Σ Vᵀ Z)`. -/
theorem columnSketch_eq_sourceSVDFactorization {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j) :
    ∀ i a,
      columnSketch A Z i a =
        ∑ c : Fin r, U i c * sourceSVDSketchRightFactor Sigma V Z c a := by
  intro i a
  unfold columnSketch preconditionColumns sourceSVDSketchRightFactor rightSketchCrossGram
  calc
    (∑ k : Fin n, A i k * Z k a)
        =
          ∑ k : Fin n,
            (∑ c : Fin r, U i c * (∑ d : Fin r, Sigma c d * V k d)) *
              Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hA i k]
            rfl
    _ =
          ∑ k : Fin n, ∑ c : Fin r,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r, ∑ k : Fin n,
            (U i c * (∑ d : Fin r, Sigma c d * V k d)) * Z k a := by
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, (∑ d : Fin r, Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ k : Fin n, ∑ d : Fin r, (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, ∑ k : Fin n, (Sigma c d * V k d) * Z k a) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            rw [Finset.sum_comm]
    _ =
          ∑ c : Fin r,
            U i c *
              (∑ d : Fin r, Sigma c d * (∑ k : Fin n, V k d * Z k a)) := by
            apply Finset.sum_congr rfl
            intro c _
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- The determinant of the exact right factor `Σ(VᵀZ)` is nonzero whenever
both exact source determinants are nonzero. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
  let SM : Matrix (Fin r) (Fin r) ℝ := Sigma
  let VM : Matrix (Fin r) (Fin r) ℝ := rightSketchCrossGram V Z
  have hmat :
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) =
        SM * VM := by
    ext a b
    simp [sourceSVDSketchRightFactor, rightSketchCrossGram, SM, VM,
      Matrix.mul_apply]
  have hdet :
      Matrix.det
          (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) =
        Matrix.det SM * Matrix.det VM := by
    calc
      Matrix.det
          (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ)
          = Matrix.det (SM * VM) := by rw [hmat]
      _ = Matrix.det SM * Matrix.det VM := by rw [Matrix.det_mul]
  intro hzero
  have hprod : Matrix.det SM * Matrix.det VM = 0 := by
    simpa [hdet] using hzero
  rcases mul_eq_zero.mp hprod with hleft | hright
  · exact hSigma hleft
  · exact hVZ hright

/-- Diagonal-singular-block version of
`sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero`.  The exact displayed
diagonal entries supply the `det(Σ) ≠ 0` hypothesis consumed by the source
right-factor determinant route. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_nonzero {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ

/-- Positive displayed diagonal singular values are a sufficient source for
the source right-factor determinant route. -/
theorem sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_pos {n r : ℕ}
    (Sigma : Fin r → Fin r → ℝ) (sigma : Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaPos : ∀ a, 0 < sigma a)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det
      (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z
    (matrix_det_ne_zero_of_eq_diagonal_pos
      Sigma sigma hSigmaDiag hSigmaPos)
    hVZ

/-- Source-SVD-shaped exact thin-factor certificate for `A Z`: if
`A = U Σ Vᵀ`, `U` has orthonormal columns, and `det(Σ(VᵀZ))` is nonzero, then
`A Z = U (Σ VᵀZ)` is a valid thin factorization for LR.1k. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hdet :
      Matrix.det
        (sourceSVDSketchRightFactor Sigma V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) where
  factorization :=
    columnSketch_eq_sourceSVDFactorization A Z U Sigma V hA
  orthonormal_columns := hU
  det_factor_ne_zero := hdet

/-- Source-SVD-shaped exact thin-factor certificate using the separate source
determinant hypotheses `det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0`. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) :=
  columnSketchThinFactorCertificate_of_sourceSVD A Z U Sigma V hA hU
    (sourceSVDSketchRightFactor_det_ne_zero_of_det_ne_zero Sigma V Z hSigma hVZ)

/-- Source-SVD-shaped exact thin-factor certificate using a displayed exact
diagonal singular-value block instead of a raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchThinFactorCertificate A Z U
      (sourceSVDSketchRightFactor Sigma V Z) :=
  columnSketchThinFactorCertificate_of_sourceSVD A Z U Sigma V hA hU
    (sourceSVDSketchRightFactor_det_ne_zero_of_diagonal_nonzero
      Sigma sigma V Z hSigmaDiag hSigmaNonzero hVZ)













































































































































































































































































































/-- Equation (9) rank/residual surface specialized to an explicit coefficient
multiplier `(A Z) C`. -/
theorem columnSketchLeftMultiplier_equation9RankResidualSurface {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ) (tail coupling : ℝ)
    (hEq9 :
      Equation9ResidualCertificate A (columnSketchLeftMultiplier A Z C) tail coupling) :
    RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
          (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
        tail + coupling :=
  equation9RankResidualSurface A Z (columnSketchLeftMultiplier A Z C) tail coupling
    (columnSketchLeftMultiplier_leftFactorThrough A Z C) hEq9

/-- Relative equation (9) surface specialized to an explicit coefficient
multiplier `(A Z) C`. -/
theorem columnSketchLeftMultiplier_equation9RelativeResidualSurface {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hEq9 :
      Equation9ResidualCertificate A (columnSketchLeftMultiplier A Z C) tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
        lowRankResidualFrob A
            (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          rho * lowRankResidualFrob A Ak :=
  equation9RelativeResidualSurface Z (columnSketchLeftMultiplier A Z C)
    tail coupling rho hbest
    (columnSketchLeftMultiplier_leftFactorThrough A Z C) hEq9 hrelative







































































































































































































































































/-- Coupling-tail certificate obtained by applying an exact orthogonal
column-sketch projector to the ambient source-tail residual bound.  The sampling
law remains exact by project convention; the theorem is exact-object and still
requires separate certificates for any computed projector, basis, SVD, inverse,
or product routine used to instantiate its hypotheses. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_orthogonalProjector_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchOrthogonalProjectorCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma := by
  have hprojector :
      frobNormRect
          (preconditionRows (columnSketchLeftMultiplier A Z C)
            (sourceSketchResidualTail Tail Z V)) ≤
        frobNormRect (sourceSketchResidualTail Tail Z V) :=
    frobNormRect_preconditionRows_columnSketchLeftMultiplier_le_of_orthogonalProjectorCertificate
      A Z C (sourceSketchResidualTail Tail Z V) hC
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤
        Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail Sigma Vperp Z V heps hTail hUtail hVperp hcrossTail
      hcrossHead hV hcomplete hcrossTerm
  exact le_trans hprojector htail











































/-- Moore-Penrose-certificate version of the coupling-tail source-SVD
certificate.  This is the form consumed by the later source-coefficient
equation-(9) rank/residual surfaces. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft Sigma
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm Sigma) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_orthogonalProjector_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC.to_orthogonalProjectorCertificate
    hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hcrossTerm



























/-- Moore-Penrose projected source-tail certificate driven by a right-acting
operator-2 bound on the exact rectangular cross factor instead of a supplied
Frobenius cross-term certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_transpose_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hOp :
      rectOpNorm2Le
        (finiteTranspose (rightSketchCrossGramRectInvFactor Vperp Z V))
        eps) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete
    (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le
      Sigma Vperp Z V heps hOp)
























/-- Moore-Penrose projected source-tail certificate driven by an ordinary
operator-2 bound on the exact rectangular cross factor. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hOp :
      rectOpNorm2Le
        (rightSketchCrossGramRectInvFactor Vperp Z V)
        eps) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + eps ^ 2) * frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
    A Tail Utail Sigma Vperp Z V C heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete
    (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le
      Sigma Vperp Z V heps hOp)



















































































/-- Moore-Penrose projected source-tail certificate driven by a computed
non-probability cross factor.

The sampling law for `Z` remains exact.  The extra radius `tau` is reserved for
the computed cross-product/inverse/product data summarized by `Mhat`; concrete
floating-point routines must instantiate the displayed Frobenius perturbation
certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_tau_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps tau : ℝ}
    (heps : 0 ≤ eps)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hErr :
      frobNormRect
          (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b -
            Mhat a b) ≤ tau) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + (eps + tau) ^ 2) * frobNorm Sigma := by
  have htau : 0 ≤ tau :=
    le_trans
      (frobNormRect_nonneg
        (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b))
      hErr
  have hrad : 0 ≤ eps + tau := add_nonneg heps htau
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
      A Tail Utail Sigma Vperp Z V C hrad hC hTail hUtail hVperp hcrossTail
      hcrossHead hV hcomplete
      (frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_frobNormRect_error
        Sigma Vperp Z V Mhat heps hMhat hErr)




























/-- Projected Moore-Penrose source-tail certificate from an entrywise computed
cross-factor error budget. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_entry_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps eta : ℝ}
    (heps : 0 ≤ eps) (heta : 0 ≤ eta)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hEntry :
      ∀ a b,
        |rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b| ≤ eta) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt (1 + (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * eta) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_tau_sq_of_computed_rectOpNorm2Le
    A Tail Utail Sigma Vperp Z V C Mhat heps hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hMhat
    (frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun a b => rightSketchCrossGramRectInvFactor Vperp Z V a b - Mhat a b)
      heta hEntry)













































































/-- Projected Moore-Penrose source-tail certificate when the computed cross
factor is assembled from componentwise-certified computed cross-gram, inverse,
and product data. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_component_sq_of_computed_rectOpNorm2Le
    {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Xhat : Fin q → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b - Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |Xhat a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c, |(∑ b : Fin r, Xhat a b * Yhat b c) - Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + beta + rho)) ^ 2) *
        frobNorm Sigma := by
  have heta : 0 ≤ alpha + beta + rho := by linarith
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_entry_sq_of_computed_rectOpNorm2Le
      A Tail Utail Sigma Vperp Z V C Mhat heps heta hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat
      (rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
        Vperp Z V Xhat Yhat Mhat hLeft hRight hRound)

/-- Entrywise cross-factor error when the rectangular cross Gram is computed by
the concrete floating-point matrix product `fl((Vperpᵀ)Z)`, while the inverse
factor and final product remain certificate-facing computed quantities. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_component_sums
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha beta rho : ℝ}
    (hγ : gammaValid fp n)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + beta + rho := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_component_sums
      Vperp Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      hLeft hRight hRound







































/-- Concrete-left-factor version of
`rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error`
for `Xhat = fl((Vperpᵀ)Z)`. The inverse routine is still represented only by
the entrywise certificate for `Yhat`; the theorem does not charge probability
construction. -/
theorem rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eta chi : ℝ}
    (heta : 0 ≤ eta)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi) :
    ∀ a c,
      ∑ b : Fin r,
        |flRightSketchCrossGramRect fp Vperp Z a b| *
          |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤
        chi * eta :=
  rightSketchCrossGramRectInvFactor_inverse_component_sum_le_of_entry_abs_error
    Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat
    heta hInvEntry hXRowAbs

/-- Entrywise cross-factor error when the rectangular cross Gram is computed by
`fl((Vperpᵀ)Z)`, the inverse factor has a supplied entrywise perturbation
certificate, and the final product has a supplied rounding certificate. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {alpha chi eta rho : ℝ}
    (hγ : gammaValid fp n)
    (heta : 0 ≤ eta)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c - Mhat a c| ≤
        alpha + chi * eta + rho :=
  rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_component_sums
    fp Vperp Z V Yhat Mhat hγ hLeftBudget
    (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
      fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
    hRound

/-- Cross-term certificate with a concrete floating-point computation of the
rectangular cross Gram `Vperpᵀ Z`.  The inverse factor `Yhat`, product `Mhat`,
and operator certificate for `Mhat` remain explicit non-probability
implementation certificates. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_component_error
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + beta + rho)) *
        frobNorm Sigma := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_component_error
      Sigma Vperp Z V (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      heps halpha hbeta hrho hMhat hLeft hRight hRound

/-- Cross-term certificate with a concrete `fl_matMul` rectangular cross Gram
and an entrywise computed-inverse perturbation certificate.

The displayed `chi * eta` term is the computed-inverse contribution: `eta`
bounds every entry of the exact inverse minus `Yhat`, while `chi` bounds the
row absolute sums of the computed rectangular factor. No floating-point error
is charged to sampling probabilities or sampling laws. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_error
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  have hbeta : 0 ≤ chi * eta := mul_nonneg hchi heta
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_component_error
      fp Sigma Vperp Z V Yhat Mhat heps halpha hbeta hrho hγ hMhat
      hLeftBudget
      (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
        fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
      hRound

/-- Projected Moore-Penrose source-tail certificate with a concrete
floating-point computation of the rectangular cross Gram `Vperpᵀ Z`; inverse,
product, projector, and operator certificates remain explicit. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_component_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha beta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hRight :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ beta)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + beta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hLeft :
      ∀ a c,
        ∑ b : Fin r,
          |rightSketchCrossGramRect Vperp Z a b -
              flRightSketchCrossGramRect fp Vperp Z a b| *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRect_flMatMul_component_left_error_le
        fp Vperp Z (nonsingInv r (rightSketchCrossGram V Z)) hγ a c)
      (hLeftBudget a c)
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_component_sq_of_computed_rectOpNorm2Le
      A Tail Utail Sigma Vperp Z V C
      (flRightSketchCrossGramRect fp Vperp Z) Yhat Mhat
      heps halpha hbeta hrho hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat hLeft hRight hRound

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and an entrywise computed-inverse perturbation
certificate. The inverse routine itself remains a ledger obligation until a
concrete algorithm proves `hInvEntry`. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    (Mhat : Fin q → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγ : gammaValid fp n)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat : rectOpNorm2Le Mhat eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            Mhat a c| ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hbeta : 0 ≤ chi * eta := mul_nonneg hchi heta
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_component_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat Mhat heps halpha hbeta hrho hγ hC
      hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hMhat
      hLeftBudget
      (rightSketchCrossGramRectInvFactor_flMatMul_inverse_component_sum_le_of_entry_abs_error
        fp Vperp Z V Yhat heta hInvEntry hXRowAbs)
      hRound





































/-- Entrywise computed cross-factor error with concrete `fl_matMul` routines
for both `Vperpᵀ Z` and the final product `Xhat * Yhat`.

The only remaining inverse-side obligation is the entrywise certificate for
`Yhat`; the final product radius `rho` is now supplied by the displayed
matrix-product dot-budget. -/
theorem rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {alpha chi eta rho : ℝ}
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (heta : 0 ≤ eta)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    ∀ a c,
      |rightSketchCrossGramRectInvFactor Vperp Z V a c -
          flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤
        alpha + chi * eta + rho := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    rightSketchCrossGramRectInvFactor_entry_abs_error_le_of_flMatMul_crossGram_inverse_entry_abs_error
      fp Vperp Z V Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      hγn heta hLeftBudget hInvEntry hXRowAbs hRound

/-- Cross-term certificate with concrete `fl_matMul` routines for the
rectangular cross Gram and the final product, plus an entrywise inverse-factor
certificate. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hMhat :
      rectOpNorm2Le
        (flRightSketchCrossGramRectInvFactorProduct fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat)
        eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_error
      fp Sigma Vperp Z V Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      heps halpha hchi heta hrho hγn hMhat hLeftBudget hInvEntry hXRowAbs
      hRound

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and final product, plus an entrywise computed-inverse
certificate. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_flMatMul_product_sq_of_computed_rectOpNorm2Le
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (heps : 0 ≤ eps)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhat :
      rectOpNorm2Le
        (flRightSketchCrossGramRectInvFactorProduct fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat)
        eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  have hRound :
      ∀ a c,
        |(∑ b : Fin r, flRightSketchCrossGramRect fp Vperp Z a b * Yhat b c) -
            flRightSketchCrossGramRectInvFactorProduct fp
              (flRightSketchCrossGramRect fp Vperp Z) Yhat a c| ≤ rho := by
    intro a c
    exact le_trans
      (rightSketchCrossGramRectInvFactorProduct_flMatMul_entry_abs_error_le
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hγr a c)
      (hProductBudget a c)
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      heps halpha hchi heta hrho hγn hC hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hMhat hLeftBudget hInvEntry hXRowAbs
      hRound

/-- A visible Frobenius bound for the concrete computed product supplies the
ordinary rectangular operator certificate required by the computed cross-factor
theorems.  This is a deterministic certificate handoff for the non-probability
quantity `Mhat = fl(fl((Vperpᵀ)Z) * Yhat)`. -/
theorem rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps : ℝ}
    (hFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps) :
    rectOpNorm2Le
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      eps :=
  rectOpNorm2Le_of_frobNormRect_le
    (flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat)
    hFrob

/-- Cross-term certificate with concrete `fl_matMul` routines and a visible
Frobenius certificate for the computed product instead of an abstract operator
certificate. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hMhatFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma := by
  let Mhat :=
    flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat
  have heps : 0 ≤ eps :=
    le_trans (frobNormRect_nonneg Mhat) hMhatFrob
  have hMhat : rectOpNorm2Le Mhat eps := by
    simpa [Mhat] using
      rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
        fp Vperp Z Yhat hMhatFrob
  exact
    frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_computed_rectOpNorm2Le_of_flMatMul_crossGram_inverse_entry_flMatMul_product
      fp Sigma Vperp Z V Yhat heps halpha hchi heta hrho hγn hγr hMhat
      hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate with concrete `fl_matMul`
rectangular cross Gram and final product, an entrywise computed-inverse
certificate, and a visible Frobenius certificate for the computed product. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps alpha chi eta rho : ℝ}
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hMhatFrob :
      frobNormRect
          (flRightSketchCrossGramRectInvFactorProduct fp
            (flRightSketchCrossGramRect fp Vperp Z) Yhat) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma := by
  let Mhat :=
    flRightSketchCrossGramRectInvFactorProduct fp
      (flRightSketchCrossGramRect fp Vperp Z) Yhat
  have heps : 0 ≤ eps :=
    le_trans (frobNormRect_nonneg Mhat) hMhatFrob
  have hMhat : rectOpNorm2Le Mhat eps := by
    simpa [Mhat] using
      rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
        fp Vperp Z Yhat hMhatFrob
  exact
    frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_plus_flMatMul_crossGram_inverse_entry_flMatMul_product_sq_of_computed_rectOpNorm2Le
      fp A Tail Utail Sigma Vperp Z V C Yhat heps halpha hchi heta hrho hγn hγr
      hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hMhat
      hLeftBudget hInvEntry hXRowAbs hProductBudget












































































/-- Product absolute-sum budgets can supply the computed-product operator
certificate by first producing a Frobenius certificate and then using the
deterministic Frobenius-to-operator handoff. -/
theorem rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa rho : ℝ}
    (hkappa : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hγr : gammaValid fp r)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho)
    (hRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps) :
    rectOpNorm2Le
      (flRightSketchCrossGramRectInvFactorProduct fp
        (flRightSketchCrossGramRect fp Vperp Z) Yhat)
      eps :=
  rectOpNorm2Le_flRightSketchCrossGramRectInvFactorProduct_of_frobNormRect_le
    fp Vperp Z Yhat
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hRadius)

/-- Cross-term certificate where the computed product's operator hypothesis is
instantiated from a visible absolute-product-sum budget for `fl(Xhat Yhat)`. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V Yhat halpha hchi heta hrho hγn hγr
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hProductFrobRadius)
    hLeftBudget hInvEntry hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the computed product's
Frobenius/operator certificate is supplied by an absolute-product-sum budget. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat : Fin r → Fin r → ℝ)
    {eps kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ eps)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hInvEntry :
      ∀ b c,
        |nonsingInv r (rightSketchCrossGram V Z) b c - Yhat b c| ≤ eta)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (eps + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_frobNormRect_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C Yhat halpha hchi heta hrho hγn hγr
    hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
    (le_trans
      (frobNormRect_flRightSketchCrossGramRectInvFactorProduct_le_sqrt_mul_product_sum_budget
        fp (flRightSketchCrossGramRect fp Vperp Z) Yhat hkappa hrho hγr
        hProductAbs hProductBudget)
      hProductFrobRadius)
    hLeftBudget hInvEntry hXRowAbs hProductBudget































































/-- Cross-term certificate where the inverse entrywise radius is supplied by a
perturbed-inverse certificate and the computed-product operator certificate is
supplied by product absolute sums. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_perturbed_inverse_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsM epsInv kappa alpha chi eta rho : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hInvBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V Yhat hkappa halpha hchi heta hrho hγn hγr
    hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
      V Z Yhat DeltaA hepsInv hdet hDelta hYhat hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the inverse entrywise
radius is supplied by a perturbed-inverse certificate and the product operator
certificate is supplied by product absolute sums. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_perturbed_inverse_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (Yhat DeltaA : Fin r → Fin r → ℝ)
    {epsM epsInv kappa alpha chi eta rho : ℝ}
    (hepsInv : 0 ≤ epsInv)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hDelta :
      ∀ b c,
        |DeltaA b c| ≤ epsInv * |rightSketchCrossGram V Z b c|)
    (hYhat :
      ∀ b c,
        ∑ k : Fin r,
          (rightSketchCrossGram V Z b k + DeltaA b k) * Yhat k c =
          if b = c then 1 else 0)
    (hInvBudget :
      ∀ b c,
        epsInv *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  |rightSketchCrossGram V Z k₁ k₂| * |Yhat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| * |Yhat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z) Yhat a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C Yhat hkappa halpha hchi heta hrho hγn hγr
    hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete hProductAbs
    hProductFrobRadius hLeftBudget
  (rightSketchCrossGram_inverse_entry_abs_error_le_of_perturbed_inverse_component_budget
      V Z Yhat DeltaA hepsInv hdet hDelta hYhat hInvBudget)
    hXRowAbs hProductBudget
















































/-- Concrete input-transfer certificate when the LU factors are generated from
the rounded square cross Gram `flRightSketchCrossGram fp V Z`. -/
theorem rightSketchCrossGram_LUBackwardError_of_flRightSketchCrossGram_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu : ℝ}
    (hγn : gammaValid fp n)
    (hLU :
      LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat epsLU)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|) :
    LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (epsLU + mu) :=
  rightSketchCrossGram_LUBackwardError_of_input_abs_error_le_absLUProduct
    V Z (flRightSketchCrossGram fp V Z) L_hat U_hat hLU
    (fun b c =>
      le_trans
        (by
          rw [abs_sub_comm]
          exact rightSketchCrossGram_flMatMul_entry_abs_error_le fp V Z hγn b c)
        (hInputBudget b c))































/-- Method-A inverse-entry certificate when the LU factors are certified for
the rounded square cross Gram `flRightSketchCrossGram fp V Z`; the exact
`VᵀZ` theorem receives the added input coefficient `mu`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_fl_lu_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsLU mu eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat epsLU)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((epsLU + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
    fp V Z L_hat U_hat (add_nonneg hepsLU hmu) hdet hL_diag hU_diag
    (rightSketchCrossGram_LUBackwardError_of_flRightSketchCrossGram_input_budget
      fp V Z L_hat U_hat hγn hLU hInputBudget)
    hγr hBudget

/-- Doolittle-generated LU factors for the rounded square cross Gram satisfy
the standard LU backward-error certificate used by the Method-A inverse layer. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleLU_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    (hγr : gammaValid fp r)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  DoolittleLU.to_LUBackwardError r fp
    (flRightSketchCrossGram fp V Z) L_hat U_hat hγr hD

/-- Method-A inverse-entry certificate when the LU factors are generated by the
Doolittle recurrence from the rounded square cross Gram.  The sampling law stays
exact; the theorem charges the rounded square-cross-Gram input through `mu` and
the Doolittle factorization through `gamma fp r`. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_fl_lu_input_budget
    fp V Z L_hat U_hat (gamma_nonneg fp hγr) hmu hγn hγr hdet
    hL_diag hU_diag
    (rightSketchCrossGram_LUBackwardError_of_DoolittleLU_flRightSketchCrossGram
      fp V Z L_hat U_hat hγr hD)
    hInputBudget hBudget

/-- Cross-term certificate where Method-A uses Doolittle-generated LU factors
for the rounded square cross Gram. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittle_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
      fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag hD
      hInputBudget hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses
Doolittle-generated LU factors for the rounded square cross Gram. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittle_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleLU r (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
      fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag hD
      hInputBudget hInvBudget)
    hXRowAbs hProductBudget

/-- Dense-loop Doolittle factors for the rounded square cross Gram satisfy the
standard LU backward-error certificate once the visible compression budgets in
`DoolittleDenseLoopCertificate` are supplied. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopCertificate_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    (hγr : gammaValid fp r)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  hD.to_LUBackwardError hγr

/-- Method-A inverse-entry certificate when the LU factors are generated by a
dense-Doolittle loop certificate for the rounded square cross Gram. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoop_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittle_fl_input_budget
    fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hBudget

/-- Cross-term certificate where Method-A uses a dense-Doolittle loop
certificate for the rounded square cross Gram. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoop_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittle_fl_input_product_sum_budget
    fp Sigma Vperp Z V L_hat U_hat hmu hkappa halpha hchi heta hrho
    hγn hγr hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hInvBudget
    hProductAbs hProductFrobRadius hLeftBudget hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses a
dense-Doolittle loop certificate for the rounded square cross Gram. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoop_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittle_fl_input_product_sum_budget_sq
    fp A Tail Utail Sigma Vperp Z V C L_hat U_hat hmu hkappa halpha hchi heta
    hrho hγn hγr hC hTail hUtail hVperp hcrossTail hcrossHead hV
    hcomplete hdet hL_diag hU_diag
    (hD.to_DoolittleLU (gamma_nonneg fp hγr)) hInputBudget hInvBudget
    hProductAbs hProductFrobRadius hLeftBudget hXRowAbs hProductBudget

/-- Absolute dense-Doolittle residual budgets plus dominance inequalities
produce the rounded square-cross-Gram LU backward-error certificate. -/
theorem rightSketchCrossGram_LUBackwardError_of_DoolittleDenseLoopAbsBudgetCertificate_flRightSketchCrossGram
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    (hγr : gammaValid fp r)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL) :
    LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat (gamma fp r) :=
  hD.to_LUBackwardError hγr

/-- Method-A inverse-entry certificate when a dense-Doolittle implementation
first proves absolute residual budgets and then proves their dominance by the
relative compression budgets required by the dense-loop certificate. -/
theorem rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoopAbsBudget_fl_input_budget
    (fp : FPModel) {n r : ℕ}
    (V : Fin n → Fin r → ℝ) (Z : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {mu eta : ℝ}
    (hmu : 0 ≤ mu)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta) :
    ∀ b c,
      |nonsingInv r (rightSketchCrossGram V Z) b c -
          methodAComputedInverse fp r L_hat U_hat b c| ≤ eta :=
  rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_doolittleDenseLoop_fl_input_budget
    fp V Z L_hat U_hat hmu hγn hγr hdet hL_diag hU_diag
    hD.to_denseLoopCertificate hInputBudget hBudget

/-- Cross-term certificate where Method-A uses dense-Doolittle factors supplied
through absolute residual budgets plus dominance inequalities. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoopAbsBudget_fl_input_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_doolittleDenseLoop_fl_input_product_sum_budget
    fp Sigma Vperp Z V L_hat U_hat hmu hkappa halpha hchi heta hrho
    hγn hγr hdet hL_diag hU_diag hD.to_denseLoopCertificate
    hInputBudget hInvBudget hProductAbs hProductFrobRadius hLeftBudget
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A uses
dense-Doolittle factors supplied through absolute residual budgets plus
dominance inequalities. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoopAbsBudget_fl_input_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {BU BL : Fin r → Fin r → ℝ}
    {epsM mu kappa alpha chi eta rho : ℝ}
    (hmu : 0 ≤ mu)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hD :
      DoolittleDenseLoopAbsBudgetCertificate r
        (flRightSketchCrossGram fp V Z) L_hat U_hat fp BU BL)
    (hInputBudget :
      ∀ b c : Fin r,
        rightSketchCrossGramDotBudget fp V Z b c ≤
          mu * ∑ l : Fin r, |L_hat b l| * |U_hat l c|)
    (hInvBudget :
      ∀ b c,
        ((gamma fp r + mu) + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_doolittleDenseLoop_fl_input_product_sum_budget_sq
    fp A Tail Utail Sigma Vperp Z V C L_hat U_hat hmu hkappa halpha hchi heta
    hrho hγn hγr hC hTail hUtail hVperp hcrossTail hcrossHead hV
    hcomplete hdet hL_diag hU_diag hD.to_denseLoopCertificate
    hInputBudget hInvBudget hProductAbs hProductFrobRadius hLeftBudget
    hXRowAbs hProductBudget

/-- Cross-term certificate where the inverse entrywise radius is supplied by
Method-A LU inversion, and the computed-product operator certificate is supplied
by product absolute sums. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_inverse_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hInvBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
      fp V Z L_hat U_hat hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where the inverse entrywise
radius is supplied by Method-A LU inversion and the product operator certificate
is supplied by product absolute sums. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_inverse_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM kappa alpha chi eta rho : ℝ}
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU :
      LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat (gamma fp r))
    (hInvBudget :
      ∀ b c,
        (3 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_budget
      fp V Z L_hat U_hat hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Cross-term certificate where the inverse entrywise radius is supplied by
Method-A LU inversion with an exposed LU factorization coefficient. -/
theorem frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_methodA_lu_factor_product_sum_budget
    (fp : FPModel) {n q r : ℕ}
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM epsLU kappa alpha chi eta rho : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hInvBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (matMulRectLeft Sigma
          (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
      (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) * (alpha + chi * eta + rho)) *
        frobNorm Sigma :=
  frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product
    fp Sigma Vperp Z V (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hProductAbs hProductFrobRadius
    hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
      fp V Z L_hat U_hat hepsLU hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget

/-- Projected Moore-Penrose source-tail certificate where Method-A LU inversion
uses an exposed LU factorization coefficient. -/
theorem frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_methodA_lu_factor_product_sum_budget_sq
    (fp : FPModel) {m n q r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Utail : Fin m → Fin q → ℝ)
    (Sigma : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    (Z : Fin n → Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (C : Fin r → Fin m → ℝ)
    (L_hat U_hat : Fin r → Fin r → ℝ)
    {epsM epsLU kappa alpha chi eta rho : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hkappa : 0 ≤ kappa)
    (halpha : 0 ≤ alpha) (hchi : 0 ≤ chi) (heta : 0 ≤ eta) (hrho : 0 ≤ rho)
    (hγn : gammaValid fp n)
    (hγr : gammaValid fp r)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft Sigma (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hdet :
      Matrix.det
          ((rightSketchCrossGram V Z) : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin r, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin r, U_hat i i ≠ 0)
    (hLU : LUBackwardError r (rightSketchCrossGram V Z) L_hat U_hat epsLU)
    (hInvBudget :
      ∀ b c,
        (epsLU + 2 * gamma fp r + gamma fp r ^ 2) *
            ∑ k₁ : Fin r,
              |nonsingInv r (rightSketchCrossGram V Z) b k₁| *
                (∑ k₂ : Fin r,
                  (∑ l : Fin r, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp r L_hat U_hat k₂ c|) ≤ eta)
    (hProductAbs :
      ∀ a c,
        ∑ b : Fin r,
          |flRightSketchCrossGramRect fp Vperp Z a b| *
            |methodAComputedInverse fp r L_hat U_hat b c| ≤ kappa)
    (hProductFrobRadius :
      Real.sqrt ((q : ℝ) * (r : ℝ)) * (kappa + rho) ≤ epsM)
    (hLeftBudget :
      ∀ a c,
        ∑ b : Fin r,
          rightSketchCrossGramRectDotBudget fp Vperp Z a b *
            |nonsingInv r (rightSketchCrossGram V Z) b c| ≤ alpha)
    (hXRowAbs :
      ∀ a, ∑ b : Fin r, |flRightSketchCrossGramRect fp Vperp Z a b| ≤ chi)
    (hProductBudget :
      ∀ a c,
        rightSketchCrossGramRectInvFactorProductDotBudget fp
          (flRightSketchCrossGramRect fp Vperp Z)
          (methodAComputedInverse fp r L_hat U_hat) a c ≤ rho) :
    frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤
      Real.sqrt
          (1 +
            (epsM + Real.sqrt ((q : ℝ) * (r : ℝ)) *
              (alpha + chi * eta + rho)) ^ 2) *
        frobNorm Sigma :=
  frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_product_sum_budget_flMatMul_crossGram_inverse_entry_flMatMul_product_sq
    fp A Tail Utail Sigma Vperp Z V C
    (methodAComputedInverse fp r L_hat U_hat)
    hkappa halpha hchi heta hrho hγn hγr hC hTail hUtail hVperp hcrossTail
    hcrossHead hV hcomplete hProductAbs hProductFrobRadius hLeftBudget
    (rightSketchCrossGram_inverse_entry_abs_error_le_of_methodA_lu_factor_budget
      fp V Z L_hat U_hat hepsLU hdet hL_diag hU_diag hLU hγr hInvBudget)
    hXRowAbs hProductBudget



























































































































































































































/-- Source-SVD-facing nonzero Gram determinant route.  The exact hypotheses
`det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0` instantiate the thin-factor bridge with
`R = Σ(VᵀZ)`. -/
theorem columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing nonzero Gram determinant route with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_det_ne_zero_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing positive-definite Gram route.  The exact hypotheses
`det(Σ) ≠ 0` and `det(VᵀZ) ≠ 0` instantiate the thin-factor bridge and prove
the source-head sketch Gram is positive definite. -/
theorem columnSketchGram_posDef_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) :=
  columnSketchGram_posDef_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing positive-definite Gram route with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_posDef_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.PosDef (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) :=
  columnSketchGram_posDef_of_thinFactorCertificate A Z U
    (sourceSVDSketchRightFactor Sigma V Z)
    (columnSketchThinFactorCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Equation (9) determinant route for an orthogonal source head-plus-tail
split.  The source-head positive-definite certificate required by
`columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef` is generated from
the exact thin source factors `U`, `Σ`, and `VᵀZ`. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    A Tail Z U Sigma V hA hUT
    (columnSketchGram_posDef_of_sourceSVD_det_factors
      (sourceSVDFactorMatrix U Sigma V) Z U Sigma V
      (by intro i j; rfl) hU hSigma hVZ)

/-- Equation (9) determinant route for an orthogonal source head-plus-tail
split, with an exact diagonal singular-value block replacing the raw
`det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef
    A Tail Z U Sigma V hA hUT
    (columnSketchGram_posDef_of_sourceSVD_diagonal_det_factors
      (sourceSVDFactorMatrix U Sigma V) Z U Sigma sigma V
      (by intro i j; rfl) hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-tail-factor version of the equation (9) determinant route.  Instead
of assuming the field `U^T Tail = 0` directly, it derives it from a supplied
exact tail factorization and exact left-basis cross-orthogonality.  Computed
SVD/tail factors remain implementation-facing non-probability obligations. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hTail :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors
    A Tail Z U Sigma V hA
    (sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vtail hTail hcross)
    hU hSigma hVZ

/-- Diagonal-singular-block version of the tail-factor determinant route.  The
visible diagonal entries of the exact source singular block replace the raw
`det(Sigma) != 0` hypothesis. -/
theorem columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_tail_factor_left_cross_zero
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vtail : Fin n → Fin q → ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hTail :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vtail i j)
    (hcross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
  columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero
    A Tail Z U Sigma V Utail SigmaTail Vtail hA hTail hcross hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ

/-- Source-SVD-facing concrete `nonsingInv` Gram-inverse certificate. -/
theorem columnSketchGramInverseCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing exact Gram-inverse certificate with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchGramInverseCertificate A Z
      (nonsingInv r (columnSketchGram A Z)) :=
  columnSketchGramInverseCertificate_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing Moore-Penrose certificate for
`C = nonsingInv((A Z)ᵀ(A Z))(A Z)ᵀ`. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing Moore-Penrose certificate with an exact diagonal
source singular block replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseCoefficient_moorePenroseCertificate_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    ColumnSketchMoorePenroseCertificate A Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z))) :=
  columnSketchGramInverseCoefficient_moorePenroseCertificate A Z
    (nonsingInv r (columnSketchGram A Z))
    (columnSketchGramInverseCertificate_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Source-SVD-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table.  This still does not prove the equation (9)
residual inequality; it only closes the source determinant-to-projector
algebra. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ)

/-- Source-SVD-facing equation (9) projector surface for the concrete exact
Gram-inverse coefficient table, with an exact diagonal singular-value block
replacing the raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix
        (columnSketchLeftMultiplier A Z
          (columnSketchGramInverseCoefficient A Z
            (nonsingInv r (columnSketchGram A Z)))) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))))
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z))))
            (columnSketchLeftMultiplier A Z
              (columnSketchGramInverseCoefficient A Z
                (nonsingInv r (columnSketchGram A Z)))) i j =
          columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z))) i j) ∧
      RectRankAtMost m n r
        (preconditionRows
          (columnSketchLeftMultiplier A Z
            (columnSketchGramInverseCoefficient A Z
              (nonsingInv r (columnSketchGram A Z)))) A) :=
  columnSketchLeftMultiplier_orthogonalProjectorSurface_of_det_ne_zero A Z
    (columnSketchGram_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ)

/-- Named-projector version of the source-SVD-facing exact Gram-inverse
projector surface. -/
theorem columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ

/-- Named-projector version of the source-SVD-facing exact Gram-inverse
projector surface, with an exact diagonal singular-value block replacing the
raw `det(Σ) ≠ 0` hypothesis. -/
theorem columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_orthogonalProjectorSurface_of_sourceSVD_diagonal_det_factors
      A Z U Sigma sigma V hA hU hSigmaDiag hSigmaNonzero hVZ

/-- Source-SVD-facing head/tail residual surface for the concrete exact
Gram-inverse projector.  The source determinant hypotheses provide the
projector reproduction algebra; the supplied head/tail certificate supplies the
still-open equation (9) SVD residual bound. -/
theorem columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling := by
  have hproj :=
    columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ
  have hEq9 :
      Equation9ResidualCertificate A (columnSketchGramInverseProjector A Z)
        tail coupling :=
    hHT.to_residualCertificate hproj.2.2.1
  exact
    ⟨hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1,
      hproj.2.2.2.2, hEq9.residual_bound⟩

/-- Source-SVD-facing relative residual surface for the concrete exact
Gram-inverse projector, still conditional on the explicit head/tail equation
(9) certificate and a scalar comparison to a certified best rank-`k`
approximation. -/
theorem columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  have hproj :=
    columnSketchGramInverseProjector_orthogonalProjectorSurface_of_sourceSVD_det_factors
      A Z U Sigma V hA hU hSigma hVZ
  have hEq9 :
      Equation9ResidualCertificate A (columnSketchGramInverseProjector A Z)
        tail coupling :=
    hHT.to_residualCertificate hproj.2.2.1
  exact
    ⟨hbest.rank_le, hproj.1, hproj.2.1, hproj.2.2.1,
      hproj.2.2.2.1, hproj.2.2.2.2,
      le_trans hEq9.residual_bound hrelative⟩

/-- Source-SVD-facing residual surface where the head/tail certificate is
instantiated by an explicit sketch coefficient table `W`, so the only remaining
residual obligations are the two exact Frobenius norm bounds for
`A - (A Z) W` and its projected image. -/
theorem columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    A Z U Sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling hA hU hSigma hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual version of the explicit-coefficient source-SVD
head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_columnSketchHeadRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ) (W : Fin r → Fin n → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigma :
      Matrix.det (Sigma : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    Z U Sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling rho hbest hA hU hSigma hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- Source-SVD-facing residual surface with an exact diagonal singular-value
block replacing the raw `det(Σ) ≠ 0` hypothesis.  The residual radii still come
from the supplied head/tail equation-(9) certificate; computed SVD, projector,
Gram, inverse, and product routines remain separate non-probability
implementation obligations. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_headTailRankResidualSurface
    A Z U Sigma V Head Tail tail coupling hA hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ hHT

/-- Relative residual version of the diagonal source-SVD head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Head Tail : Fin m → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hHT :
      Equation9HeadTailSketchCertificate A Z
        (columnSketchGramInverseProjector A Z) Head Tail tail coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_headTailRelativeResidualSurface
    Z U Sigma V Head Tail tail coupling rho hbest hA hU
    (matrix_det_ne_zero_of_eq_diagonal_nonzero
      Sigma sigma hSigmaDiag hSigmaNonzero)
    hVZ hHT hrelative

/-- Explicit-coefficient source-SVD residual surface with a displayed diagonal
singular-value block in place of the raw determinant hypothesis. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_columnSketchHeadRankResidualSurface
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) (tail coupling : ℝ)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRankResidualSurface
    A Z U Sigma sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling hA hU hSigmaDiag hSigmaNonzero hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)

/-- Relative residual version of the explicit-coefficient diagonal source-SVD
head/tail bridge. -/
theorem columnSketchGramInverseProjector_sourceSVD_diagonal_columnSketchHeadRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (W : Fin r → Fin n → ℝ) (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA : ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (columnSketchTail A Z W) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (columnSketchTail A Z W)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceSVD_diagonal_headTailRelativeResidualSurface
    Z U Sigma sigma V (columnSketchHead A Z W) (columnSketchTail A Z W)
    tail coupling rho hbest hA hU hSigmaDiag hSigmaNonzero hVZ
    (equation9HeadTailSketchCertificate_of_columnSketchHead
      A Z (columnSketchGramInverseProjector A Z) W tail coupling
      htail_nonneg hcoupling_nonneg htail hcoupling)
    hrelative

/-- Source-coefficient residual surface for any exact Moore-Penrose certificate
for the full sketch `A Z`.  This combines the LR.1o source residual tail with a
supplied four-equation exact pseudoinverse/projector certificate. -/
theorem columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRankResidualSurface
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z C)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          tail + coupling := by
  have hproj :=
    columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
      hC.to_orthogonalProjectorCertificate
  have hres :=
    equation9RankResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
      A Tail Z (columnSketchLeftMultiplier A Z C) U Sigma V tail coupling
      (columnSketchLeftMultiplier_leftFactorThrough A Z C)
      hproj.2.2.1 hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling
  exact
    ⟨hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1, hres.1, hres.2⟩

/-- Relative residual version of the source-coefficient route for any supplied
exact Moore-Penrose certificate for the full sketch `A Z`. -/
theorem columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ) (C : Fin r → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hC : ColumnSketchMoorePenroseCertificate A Z C)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchLeftMultiplier A Z C)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchLeftMultiplier A Z C) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchLeftMultiplier A Z C)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchLeftMultiplier A Z C)
            (columnSketchLeftMultiplier A Z C) i j =
          columnSketchLeftMultiplier A Z C i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchLeftMultiplier A Z C) A) ≤
          rho * lowRankResidualFrob A Ak := by
  have hproj :=
    columnSketchLeftMultiplier_orthogonalProjectorSurface A Z C
      hC.to_orthogonalProjectorCertificate
  have hres :=
    equation9RelativeResidualSurface_of_sourceHeadTail_sourceSketchCoefficient
      Z (columnSketchLeftMultiplier A Z C) U Sigma V tail coupling rho
      hbest (columnSketchLeftMultiplier_leftFactorThrough A Z C)
      hproj.2.2.1 hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling
      hrelative
  exact
    ⟨hres.1, hproj.1, hproj.2.1, hproj.2.2.1, hproj.2.2.2.1,
      hres.2.1, hres.2.2⟩

/-- Source-coefficient residual surface for the concrete exact Gram-inverse
projector `P = (A Z)((A Z)^T(A Z))^{-1}(A Z)^T`, assuming the exact sketch Gram
determinant is nonzero.  This removes the supplied Moore-Penrose certificate
from the previous source-tail bridge while still leaving concrete
Gram/inverse/product computations as separate FP obligations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_det_ne_zero
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRankResidualSurface
      A Tail Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z)))
      U Sigma V tail coupling
      (columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
        A Z hdet)
      hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling

/-- Relative residual version of the concrete exact Gram-inverse source-tail
bridge.  The source residual and projected residual radii are still explicit
analysis obligations; the projector side is now instantiated from
`det((A Z)^T(A Z)) != 0`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  simpa [columnSketchGramInverseProjector] using
    columnSketchLeftMultiplier_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface
      Z
      (columnSketchGramInverseCoefficient A Z
        (nonsingInv r (columnSketchGram A Z)))
      U Sigma V tail coupling rho hbest
      (columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero
        A Z hdet)
      hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling hrelative

/-- Source-head/tail residual surface for the concrete exact Gram-inverse
projector, with the full sketch-Gram determinant generated from an exact
diagonal source singular block and exact source-tail left orthogonality.

This is still an exact-object theorem.  It removes the raw
`det((A Z)^T(A Z)) != 0` hypothesis from the displayed source-head/tail route,
but it does not construct the rectangular SVD, prove the tail-radius
inequalities, or certify computed SVD/projector/Gram/inverse/product routines. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_sourceSVD_diagonal_det_factors
    {m n r : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (tail coupling : ℝ)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          tail + coupling :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_det_ne_zero
    A Tail Z U Sigma V tail coupling
    (columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U Sigma sigma V hA hUT hU hSigmaDiag hSigmaNonzero hVZ)
    hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling

/-- Relative residual version of the diagonal source-head/tail concrete
Gram-inverse projector surface. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_sourceSVD_diagonal_det_factors
    {m n k r : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (Sigma : Fin r → Fin r → ℝ)
    (sigma : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (tail coupling rho : ℝ)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U Sigma V i j + Tail i j)
    (hUT : sourceTailLeftOrthogonal U Tail)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, Sigma a b = if a = b then sigma a else 0)
    (hSigmaNonzero : ∀ a, sigma a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (htail_nonneg : 0 ≤ tail) (hcoupling_nonneg : 0 ≤ coupling)
    (htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ tail)
    (hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ coupling)
    (hrelative : tail + coupling ≤ rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero
    Z U Sigma V tail coupling rho hbest
    (columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U Sigma sigma V hA hUT hU hSigmaDiag hSigmaNonzero hVZ)
    hVZ hA htail_nonneg hcoupling_nonneg htail hcoupling hrelative

/-- Source-head/tail diagonal-source residual surface with the two visible
source-tail radii instantiated from the CACM cross-term certificate.

The source-head determinant and projector route uses the displayed diagonal
source singular block.  The ambient tail and projected-tail radii are both
generated from the exact tail factorization
`Tail = Utail * SigmaTail * Vperpᵀ`, exact source/tail orthogonality, and the
exact cross-term bound for
`SigmaTail * (Vperpᵀ Z)(Vᵀ Z)^{-1}`.  This remains exact-object mathematics:
rectangular SVD construction, singular-value ordering, Eckart--Young
optimality, randomness-derived cross-term certificates, and computed
non-probability SVD/projector/Gram/inverse/product routines remain separate
obligations.  Sampling probabilities and laws remain exact mathematical
inputs. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hTailSource :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j := by
    intro i j
    rw [hTail i j]
    rfl
  have hUT : sourceTailLeftOrthogonal U Tail :=
    sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vperp hTailSource hLeftCross
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V hA hUT hU hSigmaDiag hSigmaNonzero hVZ
  have hC :
      ColumnSketchMoorePenroseCertificate A Z
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z))) :=
    columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero A Z hdet
  have hrad_nonneg : 0 ≤ rad := by
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg SigmaTail)
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ rad :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail SigmaTail Vperp Z V heps hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hcrossTerm
  have hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ rad := by
    simpa [columnSketchGramInverseProjector, rad] using
      frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
        A Tail Utail SigmaTail Vperp Z V
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z)))
        heps hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
        hcrossTerm
  have hres :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRankResidualSurface_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V rad rad hA hUT hU hSigmaDiag
      hSigmaNonzero hVZ hrad_nonneg hrad_nonneg htail hcoupling
  refine ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.1,
    hres.2.2.2.2.1, ?_⟩
  simpa [rad, two_mul] using hres.2.2.2.2.2

/-- Relative-residual version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm`.

The only extra assumption is the visible scalar comparison that the displayed
cross-term-generated radius is small relative to the supplied best-rank
certificate.  This is still not an Eckart--Young theorem: construction of the
best-rank certificate from singular values remains a separate foundation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm
    {m n k r q : ℕ}
    {A Ak Tail : Fin m → Fin n → ℝ}
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hbest : IsBestRankApproxFrob m n k A Ak)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * lowRankResidualFrob A Ak) :
    RectRankAtMost m n k Ak ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A Ak := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hTailSource :
      ∀ i j, Tail i j = sourceSVDFactorMatrix Utail SigmaTail Vperp i j := by
    intro i j
    rw [hTail i j]
    rfl
  have hUT : sourceTailLeftOrthogonal U Tail :=
    sourceTailLeftOrthogonal_of_tail_factor_left_cross_zero
      U Tail Utail SigmaTail Vperp hTailSource hLeftCross
  have hdet :
      Matrix.det (columnSketchGram A Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_det_factors
      A Tail Z U SigmaHead sigmaHead V hA hUT hU hSigmaDiag hSigmaNonzero hVZ
  have hC :
      ColumnSketchMoorePenroseCertificate A Z
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z))) :=
    columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero A Z hdet
  have hrad_nonneg : 0 ≤ rad := by
    exact mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg SigmaTail)
  have htail :
      frobNormRect (sourceSketchResidualTail Tail Z V) ≤ rad :=
    frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq
      Tail Utail SigmaTail Vperp Z V heps hTail hUtail hVperp
      hcrossTail hcrossHead hV hcomplete hcrossTerm
  have hcoupling :
      frobNormRect
        (preconditionRows (columnSketchGramInverseProjector A Z)
          (sourceSketchResidualTail Tail Z V)) ≤ rad := by
    simpa [columnSketchGramInverseProjector, rad] using
      frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq
        A Tail Utail SigmaTail Vperp Z V
        (columnSketchGramInverseCoefficient A Z
          (nonsingInv r (columnSketchGram A Z)))
        heps hC hTail hUtail hVperp hcrossTail hcrossHead hV hcomplete
        hcrossTerm
  have hrelative' : rad + rad ≤ rho * lowRankResidualFrob A Ak := by
    simpa [rad, two_mul] using hrelative
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_sourceSVD_diagonal_det_factors
      Z U SigmaHead sigmaHead V rad rad rho hbest hA hUT hU hSigmaDiag
      hSigmaNonzero hVZ hrad_nonneg hrad_nonneg htail hcoupling hrelative'

/-- Source-head/tail scalar-rate relative surface with the source head itself
as the best-rank comparison.

This composes the LR.1bm scalar residual theorem with the existing
tail-optimality handoff for `IsBestRankApproxFrob`.  The true
Eckart--Young/singular-value proof is not hidden: it is exactly the supplied
`hopt` inequality.  Sampling probabilities and laws remain exact mathematical
inputs, and computed non-probability SVD/projector/Gram/inverse/product
routines still need separate certificates before this exact-object theorem can
be used implementation-facing. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm_tailOptimal
    {m n r q : ℕ}
    (A Tail : Fin m → Fin n → ℝ)
    (Z : Fin n → Fin r → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hA :
      ∀ i j, A i j = sourceSVDFactorMatrix U SigmaHead V i j + Tail i j)
    (hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j)
    (hUtail :
      ∀ a b, ∑ i : Fin m, Utail i a * Utail i b = idMatrix q a b)
    (hLeftCross : ∀ a c, ∑ i : Fin m, U i a * Utail i c = 0)
    (hU : ∀ a b, ∑ i : Fin m, U i a * U i b = idMatrix r a b)
    (hSigmaDiag : ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0)
    (hSigmaNonzero : ∀ a, sigmaHead a ≠ 0)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hVperp : ∀ a c, ∑ j : Fin n, Vperp j a * Vperp j c = idMatrix q a c)
    (hcrossTail : ∀ b c, ∑ j : Fin n, V j b * Vperp j c = 0)
    (hcrossHead : ∀ a c, ∑ j : Fin n, Vperp j a * V j c = 0)
    (hV : ∀ b c, ∑ j : Fin n, V j b * V j c = idMatrix r b c)
    (hcomplete :
      ∀ j k,
        (∑ c : Fin q, Vperp j c * Vperp k c) +
          (∑ b : Fin r, V j b * V k b) =
        idMatrix n j k)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect Tail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  let rad := Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail
  have hbest :
      IsBestRankApproxFrob m n r A
        (sourceSVDFactorMatrix U SigmaHead V) :=
    sourceSVDFactorMatrix_isBestRankApproxFrob_of_tail_optimal
      A Tail U SigmaHead V hA hopt
  have htail_eq :
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail :=
    lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail
      A Tail U SigmaHead V hA
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps hA hTail
      hUtail hLeftCross hU hSigmaDiag hSigmaNonzero hVZ hVperp hcrossTail
      hcrossHead hV hcomplete hcrossTerm
  have hrelative' :
      2 * rad ≤
        rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
    simpa [rad, htail_eq] using hrelative
  refine ⟨hbest, htail_eq, hsurface.1, hsurface.2.1, hsurface.2.2.1,
    hsurface.2.2.2.1, hsurface.2.2.2.2.1, ?_⟩
  exact le_trans hsurface.2.2.2.2.2 hrelative'

/-- Certificate-shaped version of the diagonal source-SVD scalar tail-rate
rank surface.

The exact source-SVD head/tail data are supplied by
`DiagonalSourceSVDTailCertificate`; the only extra exact assumptions are the
sketch nonsingularity condition and the CACM cross-term radius. This closes a
source-split-certificate handoff, not rectangular SVD existence, Eckart--Young,
randomness-derived cross-term bounds, or computed non-probability routine
instantiations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_diagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) := by
  have hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j := by
    intro i j
    rw [cert.tail_factor i j]
    rfl
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_sourceSVD_diagonal_crossTerm
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps cert.split
      hTail cert.Utail_orthonormal cert.left_cross cert.U_orthonormal
      cert.head_diagonal cert.head_nonzero hVZ cert.Vperp_orthonormal
      cert.right_cross_tail cert.right_cross_head cert.V_orthonormal
      cert.right_complete hcrossTerm

/-- Certificate-shaped version of the tail-optimal diagonal source-SVD relative
scalar tail-rate surface.

The exact source-SVD split and orthogonality data are packaged in
`DiagonalSourceSVDTailCertificate`. The visible `hopt` inequality is still the
entire Eckart--Young/tail-optimality obligation; the theorem does not derive it
from singular values. The probability law is exact by convention, while
computed SVD/singular-vector/projector/Gram/inverse/product routines still
require separate FP/inexact-arithmetic certificates before this result is
implementation-facing. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_diagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A Tail : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      DiagonalSourceSVDTailCertificate m n r q A Tail U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect Tail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect Tail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect Tail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  have hTail :
      ∀ i j,
        Tail i j =
          ∑ a : Fin q,
            Utail i a *
              matMulRectLeft SigmaTail (sourceRightBasisTranspose Vperp) a j := by
    intro i j
    rw [cert.tail_factor i j]
    rfl
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_sourceSVD_diagonal_crossTerm_tailOptimal
      A Tail Z U SigmaHead sigmaHead V Utail SigmaTail Vperp heps cert.split
      hTail cert.Utail_orthonormal cert.left_cross cert.U_orthonormal
      cert.head_diagonal cert.head_nonzero hVZ cert.Vperp_orthonormal
      cert.right_cross_tail cert.right_cross_head cert.V_orthonormal
      cert.right_complete hcrossTerm hopt hrelative















































































































































































































































































































































/-- Block-form exact source-SVD certificate for the diagonal equation-(9)
route.

This is one layer closer to a genuine rectangular SVD than
`DiagonalSourceSVDTailCertificate`: it assumes the primitive block
decomposition
`A = U SigmaHead V^T + Utail SigmaTail Vperp^T`, column orthonormality of the
left block `[U,Utail]`, column and row orthonormality of the right block
`[Vperp,V]`, and a displayed diagonal nonsingular source-head singular block.
It still does not prove existence of those singular-vector blocks, singular
value ordering, Eckart--Young tail optimality, randomness-derived cross-term
bounds, or any computed SVD/projector/Gram/inverse/product routine. Sampling
probabilities and laws remain exact mathematical inputs by project convention. -/
structure BlockDiagonalSourceSVDTailCertificate (m n r q : ℕ)
    (A : Fin m → Fin n → ℝ)
    (U : Fin m → Fin r → ℝ) (SigmaHead : Fin r → Fin r → ℝ)
    (sigmaHead : Fin r → ℝ) (V : Fin n → Fin r → ℝ)
    (Utail : Fin m → Fin q → ℝ) (SigmaTail : Fin q → Fin q → ℝ)
    (Vperp : Fin n → Fin q → ℝ) : Prop where
  split :
    ∀ i j,
      A i j =
        sourceSVDFactorMatrix U SigmaHead V i j +
          sourceSVDFactorMatrix Utail SigmaTail Vperp i j
  left_columns :
    ∀ bc bd : Fin r ⊕ Fin q,
      (∑ i : Fin m,
        leftBasisBlock U Utail i bc * leftBasisBlock U Utail i bd) =
        if bc = bd then 1 else 0
  head_diagonal :
    ∀ a b, SigmaHead a b = if a = b then sigmaHead a else 0
  head_nonzero :
    ∀ a, sigmaHead a ≠ 0
  right_columns :
    ∀ bc bd : Fin q ⊕ Fin r,
      (∑ j : Fin n,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V j bd) =
        if bc = bd then 1 else 0
  right_rows :
    ∀ j k,
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock Vperp V j bc * rightBasisBlock Vperp V k bc) =
        idMatrix n j k

namespace BlockDiagonalSourceSVDTailCertificate

/-- Any block source-SVD certificate with a full left block `[U,Utail]` exposes
the necessary dimension side condition `r+q <= m`.  This is a formal guard
against silently constructing `n` orthonormal left columns in too small an
ambient row space. -/
theorem left_column_count_le_row_dim {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    r + q ≤ m :=
  leftBasisBlock_col_orthonormal_card_le_rows U Utail cert.left_columns

/-- The block source-SVD certificate supplies the diagonal source-tail
certificate used by the scalar equation-(9) surface, with the tail set to
`Utail SigmaTail Vperp^T`. -/
theorem to_diagonalSourceSVDTailCertificate {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    DiagonalSourceSVDTailCertificate m n r q A
      (sourceSVDFactorMatrix Utail SigmaTail Vperp) U SigmaHead
        sigmaHead V Utail SigmaTail Vperp := by
  have hleft :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      U Utail cert.left_columns
  have hright :=
    rightBasisBlock_component_orthonormal_fields_of_col_orthonormal
      Vperp V cert.right_columns
  have hcomplete :=
    rightBasisBlock_complete_sum_of_row_orthonormal Vperp V cert.right_rows
  exact
    { split := by
        intro i j
        exact cert.split i j
      tail_factor := by
        intro i j
        rfl
      Utail_orthonormal := hleft.2.2
      left_cross := hleft.2.1
      U_orthonormal := hleft.1
      head_diagonal := cert.head_diagonal
      head_nonzero := cert.head_nonzero
      Vperp_orthonormal := hright.1
      right_cross_tail := hright.2.1
      right_cross_head := hright.2.2.1
      V_orthonormal := hright.2.2.2
      right_complete := hcomplete }

/-- The block source-SVD certificate supplies the source-tail left
orthogonality field, again without constructing the SVD itself. -/
theorem sourceTailLeftOrthogonal {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    sourceTailLeftOrthogonal U
      (sourceSVDFactorMatrix Utail SigmaTail Vperp) :=
  cert.to_diagonalSourceSVDTailCertificate.sourceTailLeftOrthogonal

/-- A supplied Frobenius tail-optimality inequality turns the block source-SVD
certificate into the exact best-rank source-head certificate.  The inequality
is exactly the remaining Eckart--Young obligation. -/
theorem isBestRankApproxFrob_of_tail_optimal {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) :=
  cert.to_diagonalSourceSVDTailCertificate.isBestRankApproxFrob_of_tail_optimal
    hopt

/-- The exact source-tail factor in a block source-SVD certificate has
Frobenius norm equal to the displayed tail singular-value block.  This is
exact-object algebra; computed singular-vector or product routines remain
separate non-probability FP obligations. -/
theorem tail_frobNorm_eq_sigma {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) =
      frobNorm SigmaTail := by
  exact
    frobNormRect_sourceSVDFactorMatrix_orthonormal
      Utail SigmaTail Vperp
      cert.to_diagonalSourceSVDTailCertificate.Utail_orthonormal
      cert.to_diagonalSourceSVDTailCertificate.Vperp_orthonormal

/-- The source-head residual in a block source-SVD certificate is exactly the
Frobenius norm of the displayed tail singular-value block. -/
theorem tail_lowRankResidual_eq_sigma {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp) :
    lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
      frobNorm SigmaTail := by
  calc
    lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V)
        =
          frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) :=
          lowRankResidualFrob_sourceSVDFactorMatrix_eq_tail
            A (sourceSVDFactorMatrix Utail SigmaTail Vperp)
            U SigmaHead V cert.split
    _ = frobNorm SigmaTail := cert.tail_frobNorm_eq_sigma

/-- The constructed ordered right-Gram source split feeds the block diagonal
source-SVD certificate once the remaining left-block columns and nonzero head
singular values are supplied.

This is the LR.1cq exact-object bridge from the constructed ordered
right-Gram split to the existing equation-(9) certificate surface.  It uses the
closed ordered source split and ordered right-basis block completeness.  It
does not construct the nullspace-completed tail-left basis, prove
Eckart--Young tail optimality, derive randomness certificates, or certify
computed SVD/projector/Gram/sketch routines. -/
theorem of_rectRightGramOrderedSourceSplit
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hleft_columns :
      ∀ bc bd :
          Fin k ⊕
            Fin (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        (∑ i : Fin m,
          leftBasisBlock
              (rectRightGramOrderedHeadLeft A hk)
              (rectRightGramOrderedTailLeft A hk) i bc *
            leftBasisBlock
              (rectRightGramOrderedHeadLeft A hk)
              (rectRightGramOrderedTailLeft A hk) i bd) =
          if bc = bd then 1 else 0)
    (hhead_nonzero :
      ∀ a : Fin k,
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  classical
  have hright := rectRightGramOrderedRightBasisBlock_col_row_orthonormal A hk
  exact
    { split := by
        intro i j
        exact (rectRightGramOrdered_source_head_add_tail A hk i j).symm
      left_columns := hleft_columns
      head_diagonal := by
        intro a b
        simp [rectRightGramOrderedHeadSingularDiagonal]
      head_nonzero := hhead_nonzero
      right_columns := hright.1
      right_rows := hright.2 }

/-- Component-left version of the constructed ordered source-split certificate
constructor.  The head/tail left orthonormality and cross fields are kept
visible so a later nullspace-completion theorem can instantiate exactly those
remaining fields. -/
theorem of_rectRightGramOrderedSourceSplit_component_left
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (hU :
      ∀ a b : Fin k,
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedHeadLeft A hk i b =
          idMatrix k a b)
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedTailLeft A hk i c =
          0)
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d)
    (hhead_nonzero :
      ∀ a : Fin k,
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit A hk
      (leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedTailLeft A hk)
        hU hcross hUtail)
      hhead_nonzero

/-- Positivity of the kth ordered singular value supplies the head
nonzero/orthonormal fields in the constructed ordered source-split certificate.
The only remaining left-side fields are the tail-left orthonormality and the
head/tail left cross-orthogonality, exactly isolating the nullspace-completion
obligation. -/
theorem of_rectRightGramOrderedSourceSplit_component_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            rectRightGramOrderedTailLeft A hk i c =
          0)
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_component_left A hk
      (fun a b =>
        rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
          A hk hk0 hlast a b)
      hcross hUtail
      (rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
        A hk hk0 hlast)

/-- After the constructed ordered head-tail left cross field is proved, the
last-position positivity constructor only needs the tail-left orthonormality
certificate.  This isolates the remaining nullspace-completed tail-left
obligation for the constructed ordered block source-SVD route. -/
theorem of_rectRightGramOrderedSourceSplit_tail_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (hUtail :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedTailLeft A hk i c *
            rectRightGramOrderedTailLeft A hk i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_component_left_of_last_pos A hk hk0 hlast
      (fun a c =>
        rectRightGramOrderedHeadTailLeft_cross_zero_of_last_pos
          A hk hk0 hlast a c)
      hUtail

/-- Positive-complement branch for the constructed ordered block source-SVD
certificate.  Kth head positivity supplies the head fields and left cross
field; strict positivity of every complement singular value supplies tail-left
orthonormality for the zero-safe tail table.  Zero complement singular values
still require a separate nullspace-completed tail-left construction. -/
theorem of_rectRightGramOrderedSourceSplit_all_tail_pos_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (htail_pos :
      ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        0 < rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  exact
    of_rectRightGramOrderedSourceSplit_tail_left_of_last_pos A hk hk0 hlast
      (fun c d =>
        rectRightGramOrderedTailLeft_col_orthonormal_of_complement_pos
          A hk htail_pos c d)

/-- Replacement-tail-left constructor for the ordered block source-SVD
certificate.  A future nullspace-completed table can instantiate `Utail` here:
it must agree with the constructed zero-safe table on nonzero complement
singular directions, be orthonormal, and remain orthogonal to the constructed
head-left block. -/
theorem of_rectRightGramOrderedSourceSplit_replacement_tail_left_of_last_pos
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (Utail :
      Fin m →
        Fin (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ)
    (hUtail_agree :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c)
    (hcross :
      ∀ a :
          Fin k,
        ∀ c :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          rectRightGramOrderedHeadLeft A hk i a *
            Utail i c =
          0)
    (hUtail_orthonormal :
      ∀ c d :
          Fin (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        ∑ i : Fin m,
          Utail i c * Utail i d =
          idMatrix
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) c d) :
    BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      Utail
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  classical
  have hright := rectRightGramOrderedRightBasisBlock_col_row_orthonormal A hk
  exact
    { split := by
        intro i j
        exact
          (rectRightGramOrdered_source_head_add_tail_replacement_left
            A hk Utail hUtail_agree i j).symm
      left_columns :=
        leftBasisBlock_col_orthonormal_of_component_orthonormal_fields
          (rectRightGramOrderedHeadLeft A hk)
          Utail
          (fun a b =>
            rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
              A hk hk0 hlast a b)
          hcross
          hUtail_orthonormal
      head_diagonal := by
        intro a b
        simp [rectRightGramOrderedHeadSingularDiagonal]
      head_nonzero :=
        rectRightGramOrderedTopEmbedding_selected_nonzero_of_last_pos
          A hk hk0 hlast
      right_columns := hright.1
      right_rows := hright.2 }

end BlockDiagonalSourceSVDTailCertificate

/-- Obstruction to using the raw constructed zero-safe tail-left table in a
block source-SVD certificate when a complement singular value is zero.  Any
valid block certificate would imply tail-left orthonormality, contradicting the
zero self-dot theorem above. -/
theorem
    not_BlockDiagonalSourceSVDTailCertificate_rectRightGramOrdered_zero_safe_tail_of_zero_complement_singularValue
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    {c :
      Fin (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)}
    (hzero :
      rectRightGramBasisSingularValue A
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c) = 0) :
    ¬ BlockDiagonalSourceSVDTailCertificate m n k
      (((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
      A
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedHeadSingularDiagonal A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk)
      (rectRightGramOrderedTailLeft A hk)
      (rectRightGramOrderedTailSingularDiagonal A hk)
      (rectRightGramOrderedTailRight A hk) := by
  intro cert
  exact
    (not_rectRightGramOrderedTailLeft_col_orthonormal_of_zero_complement_singularValue
      A hk hzero)
      cert.to_diagonalSourceSVDTailCertificate.Utail_orthonormal
























































































































































































































































































































































































































































































































/-- Concrete ordered nullspace-completion existence theorem for equation~(9).
Given an embedding of the constructed head plus complement-tail left columns into
the ambient `Fin m` column coordinates, completing the partial set consisting of
all head columns and the nonzero tail directions produces a replacement tail-left
table.  The replacement agrees with the zero-safe table on every nonzero
complement singular direction, has an orthonormal concatenated left block, and
therefore instantiates the ordered block source-SVD certificate through the
replacement-tail adapter. -/
theorem exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      BlockDiagonalSourceSVDTailCertificate m n k
        (((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card)
        A
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (fun a : Fin k =>
          rectRightGramBasisSingularValue A
            (rectRightGramOrderedTopEmbedding hk a))
        (rectRightGramOrderedHeadRight A hk)
        Utail
        (rectRightGramOrderedTailSingularDiagonal A hk)
        (rectRightGramOrderedTailRight A hk) := by
  classical
  let S := rectRightGramOrderedNonzeroTailPartialSet A hk
  have hhead : ∀ a : Fin k, Sum.inl a ∈ S := by
    intro a
    simp [S]
  have hpartial : ∀ a b : S,
      (∑ i : Fin m,
        leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i a *
          leftBasisBlock
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedTailLeft A hk) i b) =
        if a = b then 1 else 0 :=
    rectRightGramOrderedNonzeroTailPartialSet_leftBasisBlock_col_orthonormal_of_last_pos
      A hk hk0 hlast
  obtain ⟨Utail, hpreserve, hcols⟩ :=
    partialLeftBasisBlock_exists_replacement_tail
      e
      (rectRightGramOrderedHeadLeft A hk)
      (rectRightGramOrderedTailLeft A hk)
      S hhead hpartial
  have hfields :=
    leftBasisBlock_component_orthonormal_fields_of_col_orthonormal
      (rectRightGramOrderedHeadLeft A hk) Utail hcols
  have hagree :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c := by
    intro i c hτ
    have hc : Sum.inr c ∈ S := by
      simpa [S] using
        (rectRightGramOrderedNonzeroTailPartialSet_tail_iff A hk c).mpr hτ
    exact hpreserve c hc i
  refine ⟨Utail, hagree, hcols, ?_⟩
  exact
    BlockDiagonalSourceSVDTailCertificate.of_rectRightGramOrderedSourceSplit_replacement_tail_left_of_last_pos
      A hk hk0 hlast Utail hagree hfields.2.1 hfields.2.2

/-- Block-source-SVD version of the diagonal scalar equation-(9) rank/residual
surface.  The block certificate constructs the diagonal source-tail certificate
internally; the remaining assumptions are exactly the source full-rank
condition on `V^T Z` and the displayed cross-term radius. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_diagonalSourceSVDTailCertificate
    cert.to_diagonalSourceSVDTailCertificate Z heps hVZ hcrossTerm

/-- Ordered right-Gram source-split rank/residual surface.

This composes the constructed ordered replacement-tail source-SVD certificate
with the exact block-certificate equation-(9) rank surface.  The theorem keeps
the source full-rank condition on `V_ord^T Z` and the displayed
`Sigma_tail (V_tail^T Z)(V_ord^T Z)^{-1}` cross-term radius explicit.  It is
an exact-object/exact-law theorem: it does not compute the singular vectors,
projector, sketch Gram, inverse, or downstream products. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      cert Z heps hVZ hcrossTerm
  exact ⟨Utail, hagree, hcols, hsurface⟩

/-- Block-source-SVD version of the tail-optimal diagonal source-SVD relative
scalar-rate surface.  The source-head best-rank certificate is derived from
the supplied tail-optimality inequality after the block certificate has
constructed the diagonal source-tail certificate. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp)) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_diagonalSourceSVDTailCertificate
    cert.to_diagonalSourceSVDTailCertificate Z heps hVZ hcrossTerm hopt
    hrelative

/-- Block-source-SVD relative scalar-rate surface with the denominator written
as the displayed tail singular-value block norm.  The equality
`||Utail SigmaTail Vperpᵀ||_F = ||SigmaTail||_F` is supplied by the exact
orthonormal-factor identity, not by an implementation-facing computed SVD
routine. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    {m n r q : ℕ}
    {A : Fin m → Fin n → ℝ}
    {U : Fin m → Fin r → ℝ} {SigmaHead : Fin r → Fin r → ℝ}
    {sigmaHead : Fin r → ℝ} {V : Fin n → Fin r → ℝ}
    {Utail : Fin m → Fin q → ℝ} {SigmaTail : Fin q → Fin q → ℝ}
    {Vperp : Fin n → Fin q → ℝ}
    (cert :
      BlockDiagonalSourceSVDTailCertificate m n r q A U SigmaHead
        sigmaHead V Utail SigmaTail Vperp)
    (Z : Fin n → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det (rightSketchCrossGram V Z : Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft SigmaTail
            (rightSketchCrossGramRectInvFactor Vperp Z V)) ≤
        eps * frobNorm SigmaTail)
    (hopt : ∀ B, RectRankAtMost m n r B →
      frobNorm SigmaTail ≤ lowRankResidualFrob A B)
    (hrelative :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNorm SigmaTail) :
    IsBestRankApproxFrob m n r A (sourceSVDFactorMatrix U SigmaHead V) ∧
      lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) =
        frobNorm SigmaTail ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho * lowRankResidualFrob A (sourceSVDFactorMatrix U SigmaHead V) := by
  have htail :
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) =
        frobNorm SigmaTail :=
    cert.tail_frobNorm_eq_sigma
  have hopt' : ∀ B, RectRankAtMost m n r B →
      frobNormRect (sourceSVDFactorMatrix Utail SigmaTail Vperp) ≤
        lowRankResidualFrob A B := by
    intro B hB
    simpa [htail] using hopt B hB
  have hrelative' :
      2 * (Real.sqrt (1 + eps ^ 2) * frobNorm SigmaTail) ≤
        rho * frobNormRect
          (sourceSVDFactorMatrix Utail SigmaTail Vperp) := by
    simpa [htail] using hrelative
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      cert Z heps hVZ hcrossTerm hopt' hrelative'
  refine ⟨hsurface.1, ?_, hsurface.2.2.1, hsurface.2.2.2.1,
    hsurface.2.2.2.2.1, hsurface.2.2.2.2.2.1,
    hsurface.2.2.2.2.2.2.1, hsurface.2.2.2.2.2.2.2⟩
  simpa [htail] using hsurface.2.1

/-- Ordered right-Gram source-split relative surface with the tail-optimality
and scalar-comparison obligations still visible.

This composes the constructed ordered replacement-tail source-SVD certificate
with the block-certificate sigma-tail relative theorem.  It closes the exact
ordered source-split handoff for the relative equation-(9) surface, but it does
not prove the displayed tail-optimality inequality, derive the cross-term
radius from randomness, or certify computed non-probability SVD/projector/Gram
routine arithmetic. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hopt : ∀ B, RectRankAtMost m n k B →
      frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) ≤
        rho * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  have hsurface :=
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
      cert Z heps hVZ hcrossTerm hopt hrelative
  exact ⟨Utail, hagree, hcols, hsurface⟩




































































































































































































































































































































































































































































































/-- The head-first `Fin (k+q)` source factor is exactly the original matrix
pulled back along the constructed ordered head-tail column equivalence. -/
theorem sourceSVDFactorMatrix_rectRightGramOrderedHeadTailFinBlock_eq_reindexCols
    {m n k : ℕ} (A : Fin m → Fin n → ℝ) (hk : k ≤ n)
    (Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ)
    (hUtail :
      ∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) :
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
        (fun a b =>
          if a = b then rectRightGramOrderedHeadTailSigmaFin A hk a else 0)
        (rectRightGramOrderedHeadTailRightFinBlock A hk) =
      rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A := by
  classical
  funext i j
  let π := rectRightGramOrderedHeadTailColumnEquiv hk
  let term :
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    fun t =>
      rectRightGramOrderedHeadTailLeftFinBlock A hk Utail i t *
        (rectRightGramOrderedHeadTailSigmaFin A hk t *
          rectRightGramOrderedHeadTailRightFinBlock A hk j t)
  have hsum :
      (∑ t : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t) =
        ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := by
    exact
      (Fintype.sum_equiv finSumFinEquiv
        (fun bc : Fin k ⊕ rectRightGramOrderedTailIndex hk =>
          term (finSumFinEquiv bc))
        term
        (fun _ => rfl)).symm
  have hhead :=
    sourceSVDFactorMatrix_diagonal_eq_sum
      (rectRightGramOrderedHeadLeft A hk)
      (fun a : Fin k =>
        rectRightGramBasisSingularValue A
          (rectRightGramOrderedTopEmbedding hk a))
      (rectRightGramOrderedHeadRight A hk) i (π j)
  have htail :=
    sourceSVDFactorMatrix_diagonal_eq_sum
      Utail
      (fun c : rectRightGramOrderedTailIndex hk =>
        rectRightGramBasisSingularValue A
          (((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c))
      (rectRightGramOrderedTailRight A hk) i (π j)
  calc
    sourceSVDFactorMatrix
        (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
        (fun a b =>
          if a = b then rectRightGramOrderedHeadTailSigmaFin A hk a else 0)
        (rectRightGramOrderedHeadTailRightFinBlock A hk) i j
        = ∑ t : Fin (k + ((rectRightGramSelectedIndexSet
            (rectRightGramOrderedTopEmbedding hk))ᶜ).card), term t := by
            simpa [term] using
              sourceSVDFactorMatrix_diagonal_eq_sum
                (rectRightGramOrderedHeadTailLeftFinBlock A hk Utail)
                (rectRightGramOrderedHeadTailSigmaFin A hk)
                (rectRightGramOrderedHeadTailRightFinBlock A hk) i j
    _ = ∑ bc : Fin k ⊕ rectRightGramOrderedTailIndex hk,
          term (finSumFinEquiv bc) := hsum
    _ =
        sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk) i (π j) +
          sourceSVDFactorMatrix
            Utail
            (rectRightGramOrderedTailSingularDiagonal A hk)
            (rectRightGramOrderedTailRight A hk) i (π j) := by
            rw [Fintype.sum_sum_type]
            simp [term, rectRightGramOrderedTailSingularDiagonal,
              rectRightGramOrderedHeadTailRightFinBlock_eq_original,
              rectRightGramOrderedHeadTailRightOriginalFinBlock]
            rw [← hhead, ← htail]
            rfl
    _ = A i (π j) :=
          rectRightGramOrdered_source_head_add_tail_replacement_left
            A hk Utail hUtail i (π j)
    _ = rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A i j := rfl

/-- Constructed ordered replacement-tail source split discharges the visible
Frobenius tail-optimality inequality used by LR.1dt.

This is exact-object Eckart--Young/tail lower-bound infrastructure for the
constructed ordered right-Gram split.  It still does not derive randomness or
certify computed non-probability SVD/singular-vector/projector/Gram/inverse/
sketch/product routines. -/
theorem frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (B : Fin m → Fin n → ℝ) (hB : RectRankAtMost m n k B) :
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ≤
      lowRankResidualFrob A B := by
  classical
  obtain ⟨Utail, hagree, hcols, cert⟩ :=
    exists_rectRightGramOrdered_replacement_tail_left_block_certificate_of_last_pos
      A hk hk0 hlast e
  let π := rectRightGramOrderedHeadTailColumnEquiv hk
  let Aπ : Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    rectReindexCols π A
  let Bπ : Fin m →
      Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) → ℝ :=
    rectReindexCols π B
  let Ufin :=
    rectRightGramOrderedHeadTailLeftFinBlock A hk Utail
  let sigmafin :=
    rectRightGramOrderedHeadTailSigmaFin A hk
  let Vfin :=
    rectRightGramOrderedHeadTailRightFinBlock A hk
  have hBπ : RectRankAtMost m
      (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card) k Bπ := by
    simpa [Bπ, π] using
      RectRankAtMost.reindexCols_rectRightGramOrderedHeadTailColumnEquiv
        hk hB
  have hU :
      ∀ a b : Fin (k + ((rectRightGramSelectedIndexSet
        (rectRightGramOrderedTopEmbedding hk))ᶜ).card),
        (∑ i : Fin m, Ufin i a * Ufin i b) =
          idMatrix
            (k + ((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card) a b := by
    intro a b
    simpa [Ufin] using
      rectRightGramOrderedHeadTailLeftFinBlock_col_orthonormal
        A hk Utail hcols a b
  have hV :
      IsOrthogonal
        (k + ((rectRightGramSelectedIndexSet
          (rectRightGramOrderedTopEmbedding hk))ᶜ).card) Vfin := by
    simpa [Vfin] using
      rectRightGramOrderedHeadTailRightFinBlock_isOrthogonal
        A hk cert.right_columns cert.right_rows
  obtain ⟨eta, hhead_gap, htail_gap⟩ :=
    rectRightGramOrdered_head_tail_square_gap A hk hk0
  have hhead :
      ∀ a : Fin k,
        eta ≤ sigmafin
          (Fin.castAdd
            ((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).card a) ^ 2 := by
    intro a
    simpa [sigmafin] using hhead_gap a
  have htail :
      ∀ c : rectRightGramOrderedTailIndex hk,
        sigmafin (Fin.natAdd k c) ^ 2 ≤ eta := by
    intro c
    simpa [sigmafin] using htail_gap c
  have hsrc :
      sourceSVDFactorMatrix Ufin
          (fun a b => if a = b then sigmafin a else 0) Vfin =
        Aπ := by
    simpa [Ufin, sigmafin, Vfin, Aπ, π] using
      sourceSVDFactorMatrix_rectRightGramOrderedHeadTailFinBlock_eq_reindexCols
        A hk Utail hagree
  have hlower :
      Real.sqrt
          (∑ c : rectRightGramOrderedTailIndex hk,
            sigmafin (Fin.natAdd k c) ^ 2) ≤
        lowRankResidualFrob
          (sourceSVDFactorMatrix Ufin
            (fun a b => if a = b then sigmafin a else 0) Vfin) Bπ := by
    simpa [Ufin, sigmafin, Vfin, Bπ] using
      sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap
        Ufin sigmafin Vfin hU hV hhead htail Bπ hBπ
  have htail_norm :
      frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) =
        Real.sqrt
          (∑ c : rectRightGramOrderedTailIndex hk,
            sigmafin (Fin.natAdd k c) ^ 2) := by
    simpa [sigmafin] using
      frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum A hk
  calc
    frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)
        =
          Real.sqrt
            (∑ c : rectRightGramOrderedTailIndex hk,
              sigmafin (Fin.natAdd k c) ^ 2) := htail_norm
    _ ≤
        lowRankResidualFrob
          (sourceSVDFactorMatrix Ufin
            (fun a b => if a = b then sigmafin a else 0) Vfin) Bπ := hlower
    _ =
        lowRankResidualFrob Aπ Bπ := by
          rw [hsrc]
    _ = lowRankResidualFrob A B := by
          simpa [Aπ, Bπ, π] using
            lowRankResidualFrob_rectRightGramOrderedHeadTailColumnEquiv hk A B

/-- Ordered right-Gram replacement-tail relative surface with the Frobenius
tail-optimality hypothesis discharged by the constructed D4 lower-bound route.

The scalar relative-comparison and cross-term radius remain visible, and
randomness/computed non-probability routine certificates remain separate. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) ≤
        rho * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk)) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  exact
    exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos
      A hk hk0 hlast e Z heps hVZ hcrossTerm
      (fun B hB =>
        frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob
          A hk hk0 hlast e B hB)
      hrelative


















/-- Ordered right-Gram replacement-tail relative surface with the scalar
comparison stated as the cleaner coefficient inequality
`2 * sqrt (1 + eps^2) <= rho`.

This removes the raw product-form `hrelative` hypothesis from the LR.1eb
surface by using nonnegativity of the constructed tail Frobenius norm.  The
cross-term radius, randomness, and computed non-probability routine
certificates remain separate obligations. -/
theorem exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k ≤ n) (hk0 : 0 < k)
    (hlast :
      0 < rectSingularValue A (rectTopIndex hk (rectTopLastIndex hk0)))
    (e : Fin k ⊕ rectRightGramOrderedTailIndex hk ↪ Fin m)
    (Z : Fin n → Fin k → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (rectRightGramOrderedHeadRight A hk) Z :
            Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (rectRightGramOrderedTailSingularDiagonal A hk)
            (rightSketchCrossGramRectInvFactor
              (rectRightGramOrderedTailRight A hk) Z
              (rectRightGramOrderedHeadRight A hk))) ≤
        eps * frobNorm (rectRightGramOrderedTailSingularDiagonal A hk))
    (hscalar : 2 * Real.sqrt (1 + eps ^ 2) ≤ rho) :
    ∃ Utail : Fin m → rectRightGramOrderedTailIndex hk → ℝ,
      (∀ i c,
        rectRightGramBasisSingularValue A
            (((rectRightGramSelectedIndexSet
              (rectRightGramOrderedTopEmbedding hk))ᶜ).orderEmbOfFin rfl c)
            ≠ 0 →
          Utail i c = rectRightGramOrderedTailLeft A hk i c) ∧
      (∀ bc bd : Fin k ⊕ rectRightGramOrderedTailIndex hk,
        (∑ i : Fin m,
          leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bc *
            leftBasisBlock (rectRightGramOrderedHeadLeft A hk) Utail i bd) =
          if bc = bd then 1 else 0) ∧
      IsBestRankApproxFrob m n k A
        (sourceSVDFactorMatrix
          (rectRightGramOrderedHeadLeft A hk)
          (rectRightGramOrderedHeadSingularDiagonal A hk)
          (rectRightGramOrderedHeadRight A hk)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix
            (rectRightGramOrderedHeadLeft A hk)
            (rectRightGramOrderedHeadSingularDiagonal A hk)
            (rectRightGramOrderedHeadRight A hk)) =
        frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m n k
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix
                (rectRightGramOrderedHeadLeft A hk)
                (rectRightGramOrderedHeadSingularDiagonal A hk)
                (rectRightGramOrderedHeadRight A hk)) := by
  exact
    exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal
      A hk hk0 hlast e Z heps hVZ hcrossTerm
      (two_sqrt_one_add_sq_mul_tail_le_of_scalar hscalar
        (frobNorm_nonneg (rectRightGramOrderedTailSingularDiagonal A hk)))









































/-- The source-head factor built from the split square SVD diagonal expands to
the head part of the full square SVD sum. -/
theorem sourceSVDFactorMatrix_squareSVDHeadDiagonal
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i j : Fin (r + q)) :
    sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull) i j =
      ∑ a : Fin r,
        Ufull i (Fin.castAdd q a) *
          (sigma (Fin.castAdd q a) * Vfull j (Fin.castAdd q a)) := by
  unfold sourceSVDFactorMatrix squareSVDHeadLeft squareSVDHeadRight
    squareSVDHeadDiagonal
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The source-tail factor built from the split square SVD diagonal expands to
the tail part of the full square SVD sum. -/
theorem sourceSVDFactorMatrix_squareSVDTailDiagonal
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i j : Fin (r + q)) :
    sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
        (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull) i j =
      ∑ c : Fin q,
        Ufull i (Fin.natAdd r c) *
          (sigma (Fin.natAdd r c) * Vfull j (Fin.natAdd r c)) := by
  unfold sourceSVDFactorMatrix squareSVDTailLeft squareSVDTailRight
    squareSVDTailDiagonal
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- A square exact SVD certificate, supplied as full orthogonal tables and a
pointwise representation, constructs the block source-SVD certificate consumed
by the equation-(9) surface.

This remains exact-object source algebra: it does not assert existence of the
SVD, singular-value ordering, Eckart--Young optimality, or any floating-point
routine for computing/storing the singular vectors or diagonal blocks. Those
are tracked separately as non-probability computed-quantity obligations. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate (r + q) (r + q) r q A
      (squareSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) where
  split := by
    intro i j
    rw [hrepr i j]
    rw [Fin.sum_univ_add]
    rw [sourceSVDFactorMatrix_squareSVDHeadDiagonal,
      sourceSVDFactorMatrix_squareSVDTailDiagonal]
  left_columns := by
    intro bc bd
    cases bc with
    | inl a =>
        cases bd with
        | inl b =>
            simpa [leftBasisBlock, squareSVDHeadLeft, idMatrix] using
              hU.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
        | inr c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, squareSVDHeadLeft, squareSVDTailLeft,
              hne] using
              hU.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
    | inr c =>
        cases bd with
        | inl a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, squareSVDHeadLeft, squareSVDTailLeft,
              hne] using
              hU.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
        | inr d =>
            simpa [leftBasisBlock, squareSVDTailLeft, idMatrix] using
              hU.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
  head_diagonal := by
    intro a b
    rfl
  head_nonzero := by
    intro a
    exact hhead_nonzero a
  right_columns := by
    intro bc bd
    cases bc with
    | inl c =>
        cases bd with
        | inl d =>
            simpa [rightBasisBlock, squareSVDTailRight, idMatrix] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
        | inr a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
    | inr a =>
        cases bd with
        | inl c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
        | inr b =>
            simpa [rightBasisBlock, squareSVDHeadRight, idMatrix] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
  right_rows := by
    intro j k
    have hrow := hV.row_orthonormal j k
    rw [Fin.sum_univ_add] at hrow
    calc
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) j bc *
          rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) k bc)
          =
        (∑ c : Fin q,
          Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) +
          (∑ a : Fin r,
            Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) := by
            simp [rightBasisBlock, squareSVDTailRight, squareSVDHeadRight,
              Fintype.sum_sum_type]
      _ =
        (∑ a : Fin r,
          Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) +
          (∑ c : Fin q,
            Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) := by
            ring
      _ = idMatrix (r + q) j k := by
            simpa [idMatrix] using hrow

/-- Square SVD split constructor with a source-style strict-positive head
singular-value hypothesis instead of a raw nonzero-head hypothesis.

This closes only the positivity-to-nonzero handoff; SVD existence,
singular-value ordering, Eckart--Young optimality, randomness, and computed
non-probability routines remain separate obligations. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    BlockDiagonalSourceSVDTailCertificate (r + q) (r + q) r q A
      (squareSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) :=
  BlockDiagonalSourceSVDTailCertificate.of_squareSVD hU hV hrepr
    (squareSVDHeadValues_nonzero_of_pos hhead_pos)

/-- The tail factor obtained by splitting supplied square SVD tables has
Frobenius norm exactly equal to the displayed tail singular-value block.  This
is exact-object algebra; computed singular-vector and product routines remain
separate non-probability FP obligations. -/
theorem frobNormRect_squareSVDTail_eq_sigmaTail
    {r q : ℕ}
    (Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull) :
    frobNormRect
        (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
          (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  frobNormRect_sourceSVDFactorMatrix_orthonormal
    (squareSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
    (squareSVDTailRight Vfull)
    (by
      intro c d
      simpa [squareSVDTailLeft, idMatrix] using
        hU.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))
    (by
      intro c d
      simpa [squareSVDTailRight, idMatrix] using
        hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))

/-- For supplied square SVD-style tables, the source-head residual is exactly
the Frobenius norm of the displayed tail singular-value block. -/
theorem lowRankResidualFrob_squareSVDHead_eq_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    lowRankResidualFrob A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
    hU hV hrepr hhead_nonzero).tail_lowRankResidual_eq_sigma

/-- Supplied square SVD-style data give a Frobenius best-rank certificate once
the tail-optimality inequality is stated with the displayed tail singular-value
block.  This is only a handoff from a visible Eckart--Young-style hypothesis,
not a proof of that hypothesis. -/
theorem isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  have hopt' : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B := by
    intro B hB
    rw [frobNormRect_squareSVDTail_eq_sigmaTail Ufull Vfull sigma hU hV]
    exact hopt B hB
  exact
    (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
      hU hV hrepr hhead_nonzero).isBestRankApproxFrob_of_tail_optimal
        hopt'

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal`. -/
theorem isBestRankApproxFrob_of_squareSVD_head_pos_sigmaTail_optimal
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hopt

/-- Ordered supplied square-SVD data give the tail-optimality inequality for
the displayed tail singular-value block.

The proof uses LR.1dp's q-dimensional exact source-factor lower bound and the
tail-diagonal Frobenius identity.  It is exact-object Eckart--Young assembly
only: it does not construct the SVD, prove ordering from an SVD routine, or
certify computed singular-vector/projector/Gram/sketch/product arithmetic.
Sampling probabilities and laws remain exact mathematical inputs. -/
theorem squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin (r + q) → Fin (r + q) → ℝ)
    (hB : RectRankAtMost (r + q) (r + q) r B) :
    frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B := by
  have hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin (r + q), Ufull i a * Ufull i b) =
          idMatrix (r + q) a b := by
    intro a b
    simpa [idMatrix] using hU.col_orthonormal a b
  have hsource :=
    sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
      Ufull sigma Vfull hUcols hV hmono B hB
  have hsource_eq :
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull =
        A := by
    funext i j
    calc
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull i j
          =
            ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k) := by
              exact sourceSVDFactorMatrix_diagonal_eq_sum Ufull sigma Vfull i j
      _ = A i j := (hrepr i j).symm
  rw [frobNorm_squareSVDTailDiagonal_eq_sqrt_sum]
  simpa [hsource_eq] using hsource

/-- Supplied square SVD-style data with exact ordered singular-square entries
give a Frobenius best rank-`r` source-head certificate.

This removes the formerly visible tail-optimality hypothesis by deriving it
from LR.1dp.  The theorem is exact-law/exact-object only; computed SVD,
singular-vector, projector, Gram, sketch, and product routines remain
non-probability FP/certificate obligations. -/
theorem isBestRankApproxFrob_of_squareSVD_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_sigmaTail_optimal
    hU hV hrepr hhead_nonzero
    (fun B hB =>
      squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hU hV hrepr hmono B hB)

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_squareSVD_antitone`. -/
theorem isBestRankApproxFrob_of_squareSVD_head_pos_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob (r + q) (r + q) r A
      (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_squareSVD_antitone
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hmono

/-- Square-SVD certificate version of the block source-SVD scalar
equation-(9) rank/residual surface.  The exact sampling/sketch matrix `Z` and
sampling law remain mathematical inputs; computing the SVD, sketch, Gram
inverse, projector, and products is a separate FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
        hU hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm

/-- Square-SVD scalar equation-(9) rank/residual surface with a strict-positive
source-head singular-value hypothesis. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_squareSVD
      hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm

/-- Tail-optimal square-SVD certificate version of the scalar-rate relative
equation-(9) surface.  The tail-optimality hypothesis is exactly the remaining
Eckart--Young/SVD-order obligation; computing the displayed SVD objects remains
a non-probability FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
        hU hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Tail-optimal square-SVD scalar-rate relative surface with a strict-positive
source-head singular-value hypothesis.  Tail optimality remains the visible
Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (squareSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD
      hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Square-SVD scalar-rate relative surface with the source-head residual,
tail-optimality hypothesis, and scalar comparison written directly in terms of
the displayed tail singular-value block.  This uses the exact tail norm
identity for supplied SVD-style tables; it is not a proof of SVD existence or
Eckart--Young tail optimality. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    (BlockDiagonalSourceSVDTailCertificate.of_squareSVD
      hU hV hrepr hhead_nonzero)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost (r + q) (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Ordered square-SVD scalar-rate relative surface with the source-head
residual and scalar comparison written directly in terms of the displayed tail
singular-value block.

Compared with
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail`,
the raw tail-optimality hypothesis is discharged by LR.1dq from exact
singular-square antitonicity.  This is still exact-object theorem-surface
propagation; computed SVD/projector/Gram/inverse/sketch/product routines and
randomness-derived cross-term certificates remain separate obligations. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail
    hU hV hrepr hhead_nonzero Z heps hVZ hcrossTerm
    (fun B hB =>
      squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hU hV hrepr hmono B hB)
    hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_head_pos_sigmaTail_antitone
    {r q : ℕ}
    {A : Fin (r + q) → Fin (r + q) → ℝ}
    {Ufull Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hU : IsOrthogonal (r + q) Ufull)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob (r + q) (r + q) r A
        (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost (r + q) (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (squareSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_squareSVD_sigmaTail_antitone
    hU hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hmono hrelative













/-- The source-head factor built from a split thin rectangular SVD table
expands to the head part of the full SVD sum. -/
theorem sourceSVDFactorMatrix_rectangularThinSVDHeadDiagonal
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i : Fin m) (j : Fin (r + q)) :
    sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull) i j =
      ∑ a : Fin r,
        Ufull i (Fin.castAdd q a) *
          (sigma (Fin.castAdd q a) * Vfull j (Fin.castAdd q a)) := by
  unfold sourceSVDFactorMatrix rectangularThinSVDHeadLeft squareSVDHeadRight
    squareSVDHeadDiagonal
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- The source-tail factor built from a split thin rectangular SVD table
expands to the tail part of the full SVD sum. -/
theorem sourceSVDFactorMatrix_rectangularThinSVDTailDiagonal
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (i : Fin m) (j : Fin (r + q)) :
    sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
        (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull) i j =
      ∑ c : Fin q,
        Ufull i (Fin.natAdd r c) *
          (sigma (Fin.natAdd r c) * Vfull j (Fin.natAdd r c)) := by
  unfold sourceSVDFactorMatrix rectangularThinSVDTailLeft squareSVDTailRight
    squareSVDTailDiagonal
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- A thin rectangular exact SVD certificate with a full right orthogonal
basis constructs the block source-SVD certificate consumed by the
equation-(9) surface.

The left table is rectangular and only needs exact column orthonormality; the
right table is square orthogonal and supplies the row-completeness field.  This
still does not prove existence of the rectangular SVD, singular-value ordering,
Eckart--Young optimality, or any floating-point routine for computing/storing
the singular vectors or diagonal blocks. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    BlockDiagonalSourceSVDTailCertificate m (r + q) r q A
      (rectangularThinSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) where
  split := by
    intro i j
    rw [hrepr i j]
    rw [Fin.sum_univ_add]
    rw [sourceSVDFactorMatrix_rectangularThinSVDHeadDiagonal,
      sourceSVDFactorMatrix_rectangularThinSVDTailDiagonal]
  left_columns := by
    intro bc bd
    cases bc with
    | inl a =>
        cases bd with
        | inl b =>
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft, idMatrix] using
              hUcols (Fin.castAdd q a) (Fin.castAdd q b)
        | inr c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft,
              rectangularThinSVDTailLeft, hne] using
              hUcols (Fin.castAdd q a) (Fin.natAdd r c)
    | inr c =>
        cases bd with
        | inl a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [leftBasisBlock, rectangularThinSVDHeadLeft,
              rectangularThinSVDTailLeft, hne] using
              hUcols (Fin.natAdd r c) (Fin.castAdd q a)
        | inr d =>
            simpa [leftBasisBlock, rectangularThinSVDTailLeft, idMatrix] using
              hUcols (Fin.natAdd r c) (Fin.natAdd r d)
  head_diagonal := by
    intro a b
    rfl
  head_nonzero := by
    intro a
    exact hhead_nonzero a
  right_columns := by
    intro bc bd
    cases bc with
    | inl c =>
        cases bd with
        | inl d =>
            simpa [rightBasisBlock, squareSVDTailRight, idMatrix] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d)
        | inr a =>
            have hne : Fin.natAdd r c ≠ Fin.castAdd q a := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.natAdd r c) (Fin.castAdd q a)
    | inr a =>
        cases bd with
        | inl c =>
            have hne : Fin.castAdd q a ≠ Fin.natAdd r c := by
              intro h
              have hs := congrArg finSumFinEquiv.symm h
              simp at hs
            simpa [rightBasisBlock, squareSVDHeadRight, squareSVDTailRight,
              hne] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.natAdd r c)
        | inr b =>
            simpa [rightBasisBlock, squareSVDHeadRight, idMatrix] using
              hV.col_orthonormal (Fin.castAdd q a) (Fin.castAdd q b)
  right_rows := by
    intro j k
    have hrow := hV.row_orthonormal j k
    rw [Fin.sum_univ_add] at hrow
    calc
      (∑ bc : Fin q ⊕ Fin r,
        rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) j bc *
          rightBasisBlock (squareSVDTailRight Vfull)
            (squareSVDHeadRight Vfull) k bc)
          =
        (∑ c : Fin q,
          Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) +
          (∑ a : Fin r,
            Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) := by
            simp [rightBasisBlock, squareSVDTailRight, squareSVDHeadRight,
              Fintype.sum_sum_type]
      _ =
        (∑ a : Fin r,
          Vfull j (Fin.castAdd q a) * Vfull k (Fin.castAdd q a)) +
          (∑ c : Fin q,
            Vfull j (Fin.natAdd r c) * Vfull k (Fin.natAdd r c)) := by
            ring
      _ = idMatrix (r + q) j k := by
            simpa [idMatrix] using hrow

/-- Thin-rectangular SVD split constructor with a source-style strict-positive
head singular-value hypothesis instead of a raw nonzero-head hypothesis.

This remains exact-object source algebra; it closes only the
positivity-to-nonzero field for the supplied SVD-style data. -/
theorem BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a)) :
    BlockDiagonalSourceSVDTailCertificate m (r + q) r q A
      (rectangularThinSVDHeadLeft Ufull) (squareSVDHeadDiagonal sigma)
      (squareSVDHeadValues sigma) (squareSVDHeadRight Vfull)
      (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
      (squareSVDTailRight Vfull) :=
  BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)

/-- The tail factor obtained by splitting supplied thin-rectangular SVD tables
has Frobenius norm exactly equal to the displayed tail singular-value block. -/
theorem frobNormRect_rectangularThinSVDTail_eq_sigmaTail
    {m r q : ℕ}
    (Ufull : Fin m → Fin (r + q) → ℝ)
    (Vfull : Fin (r + q) → Fin (r + q) → ℝ)
    (sigma : Fin (r + q) → ℝ)
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull) :
    frobNormRect
        (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
          (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  frobNormRect_sourceSVDFactorMatrix_orthonormal
    (rectangularThinSVDTailLeft Ufull) (squareSVDTailDiagonal sigma)
    (squareSVDTailRight Vfull)
    (by
      intro c d
      simpa [rectangularThinSVDTailLeft, idMatrix] using
        hUcols (Fin.natAdd r c) (Fin.natAdd r d))
    (by
      intro c d
      simpa [squareSVDTailRight, idMatrix] using
        hV.col_orthonormal (Fin.natAdd r c) (Fin.natAdd r d))

/-- For supplied thin-rectangular SVD-style tables, the source-head residual is
exactly the Frobenius norm of the displayed tail singular-value block. -/
theorem lowRankResidualFrob_rectangularThinSVDHead_eq_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0) :
    lowRankResidualFrob A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
      frobNorm (squareSVDTailDiagonal sigma) :=
  (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
    hUcols hV hrepr hhead_nonzero).tail_lowRankResidual_eq_sigma

/-- Supplied thin-rectangular SVD-style data give a Frobenius best-rank
certificate once the tail-optimality inequality is stated with the displayed
tail singular-value block. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  have hopt' : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B := by
    intro B hB
    rw [frobNormRect_rectangularThinSVDTail_eq_sigmaTail
      Ufull Vfull sigma hUcols hV]
    exact hopt B hB
  exact
    (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
      hUcols hV hrepr hhead_nonzero).isBestRankApproxFrob_of_tail_optimal
        hopt'

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal`. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hopt

/-- Ordered supplied thin-rectangular SVD data give the tail-optimality
inequality for the displayed tail singular-value block.

This is the thin rectangular analogue of
`squareSVD_sigmaTail_le_lowRankResidualFrob_of_antitone`.  It is exact-object
Eckart--Young assembly only and leaves computed singular-vector/projector/
Gram/sketch/product arithmetic as non-probability FP/certificate obligations. -/
theorem rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (B : Fin m → Fin (r + q) → ℝ)
    (hB : RectRankAtMost m (r + q) r B) :
    frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B := by
  have hUcols' :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          idMatrix (r + q) a b := by
    intro a b
    simpa [idMatrix] using hUcols a b
  have hsource :=
    sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_antitone
      Ufull sigma Vfull hUcols' hV hmono B hB
  have hsource_eq :
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull =
        A := by
    funext i j
    calc
      sourceSVDFactorMatrix Ufull
          (fun i j : Fin (r + q) => if i = j then sigma i else 0) Vfull i j
          =
            ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k) := by
              exact sourceSVDFactorMatrix_diagonal_eq_sum Ufull sigma Vfull i j
      _ = A i j := (hrepr i j).symm
  rw [frobNorm_squareSVDTailDiagonal_eq_sqrt_sum]
  simpa [hsource_eq] using hsource

/-- Supplied thin-rectangular SVD-style data with exact ordered
singular-square entries give a Frobenius best rank-`r` source-head
certificate.

The tail-optimality inequality is derived from LR.1dp.  This theorem is
exact-law/exact-object only; computed SVD, singular-vector, projector, Gram,
sketch, and product routines remain non-probability FP/certificate
obligations. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_sigmaTail_optimal
    hUcols hV hrepr hhead_nonzero
    (fun B hB =>
      rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hUcols hV hrepr hmono B hB)

/-- Strict-positive-head version of
`isBestRankApproxFrob_of_rectangularThinSVD_antitone`. -/
theorem isBestRankApproxFrob_of_rectangularThinSVD_head_pos_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2) :
    IsBestRankApproxFrob m (r + q) r A
      (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
        (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  isBestRankApproxFrob_of_rectangularThinSVD_antitone
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos) hmono















/-- The ordered top-`r+1` right-Gram coefficient block has the displayed
one-step rank-`r` truncation as a Frobenius best-rank approximation.

This instantiates the exact-object Eckart--Young handoff for the coefficient
block used in equation (9).  The sampling law is an exact mathematical input by
project convention, and this theorem deliberately does not certify any
computed SVD, singular-vector table, projector, sketch, Gram inverse, or matrix
product routine. -/
theorem isBestRankApproxFrob_of_rectRightGramOrderedHeadDiagonal_succ
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : r + 1 ≤ n)
    (hlast :
      0 < rectSingularValue A
        (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r)))) :
    IsBestRankApproxFrob m (r + 1) r
      (sourceSVDFactorMatrix
        (rectRightGramOrderedHeadLeft A hk)
        (rectRightGramOrderedHeadSingularDiagonal A hk)
        (idMatrix (r + 1)))
      (sourceSVDFactorMatrix
        (rectangularThinSVDHeadLeft (r := r) (q := 1)
          (rectRightGramOrderedHeadLeft A hk))
        (squareSVDHeadDiagonal (r := r) (q := 1)
          (fun a : Fin (r + 1) =>
            rectRightGramBasisSingularValue A
              (rectRightGramOrderedTopEmbedding hk a)))
        (squareSVDHeadRight (r := r) (q := 1) (idMatrix (r + 1)))) := by
  classical
  let Ufull : Fin m → Fin (r + 1) → ℝ :=
    rectRightGramOrderedHeadLeft A hk
  let Vfull : Fin (r + 1) → Fin (r + 1) → ℝ :=
    idMatrix (r + 1)
  let sigmaVals : Fin (r + 1) → ℝ :=
    fun a => rectRightGramBasisSingularValue A
      (rectRightGramOrderedTopEmbedding hk a)
  let Acoeff : Fin m → Fin (r + 1) → ℝ :=
    sourceSVDFactorMatrix Ufull
      (rectRightGramOrderedHeadSingularDiagonal A hk) Vfull
  have hUcols :
      ∀ a b : Fin (r + 1),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0 := by
    intro a b
    simpa [Ufull, idMatrix] using
      rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos
        A hk (Nat.succ_pos r) hlast a b
  have hrepr :
      ∀ i j,
        Acoeff i j =
          ∑ k : Fin (r + 1), Ufull i k *
            (sigmaVals k * Vfull j k) := by
    intro i j
    simp [Acoeff, Ufull, Vfull, sigmaVals, sourceSVDFactorMatrix,
      rectRightGramOrderedHeadSingularDiagonal, idMatrix,
      Finset.sum_ite_eq, Finset.mem_univ]
  have hhead_pos :
      ∀ a : Fin r, 0 < sigmaVals (Fin.castAdd 1 a) := by
    intro a
    exact
      rectRightGramOrderedTopEmbedding_selected_pos_of_last_pos
        A hk (Nat.succ_pos r) hlast (Fin.castAdd 1 a)
  have htail_eq :
      frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigmaVals) =
        rectSingularValue A
          (rectTopIndex hk (rectTopLastIndex (Nat.succ_pos r))) := by
    have htail_nonneg :
        0 ≤ sigmaVals (Fin.natAdd r (0 : Fin 1)) := by
      exact rectRightGramBasisSingularValue_nonneg A _
    rw [frobNorm_squareSVDTailDiagonal_one sigmaVals htail_nonneg]
    have hidx :
        (Fin.natAdd r (0 : Fin 1) : Fin (r + 1)) =
          rectTopLastIndex (Nat.succ_pos r) := by
      apply Fin.ext
      simp [rectTopLastIndex]
    dsimp [sigmaVals]
    rw [(rectRightGramOrderedTopEmbedding_certificate A hk).singularValue_eq
      (Fin.natAdd r (0 : Fin 1))]
    simp [hidx]
  have hopt :
      ∀ B, RectRankAtMost m (r + 1) r B →
        frobNorm (squareSVDTailDiagonal (r := r) (q := 1) sigmaVals) ≤
          lowRankResidualFrob Acoeff B := by
    intro B hB
    rw [htail_eq]
    exact
      rectRankAtMost_lowRankResidualFrob_ge_of_rectRightGramOrderedHeadDiagonal_succ
        A hk hlast B hB
  have hbest :=
    isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal
      (m := m) (r := r) (q := 1) (A := Acoeff)
      (Ufull := Ufull) (Vfull := Vfull) (sigma := sigmaVals)
      hUcols (IsOrthogonal.id (r + 1)) hrepr hhead_pos hopt
  simpa [Acoeff, Ufull, Vfull, sigmaVals,
    rectRightGramOrderedHeadSingularDiagonal] using hbest

/-- Thin-rectangular SVD certificate version of the block source-SVD scalar
equation-(9) rank/residual surface.  The sketch matrix `Z` and sampling law
remain exact mathematical inputs; computing the SVD, sketch, Gram inverse,
projector, and products is a separate FP/certificate obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
        hUcols hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm

/-- Thin-rectangular SVD scalar equation-(9) rank/residual surface with a
strict-positive source-head singular-value hypothesis. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma)) :
    IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          2 *
            (Real.sqrt (1 + eps ^ 2) *
              frobNorm (squareSVDTailDiagonal sigma)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectangularThinSVD
      hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm

/-- Tail-optimal thin-rectangular SVD certificate version of the scalar-rate
relative equation-(9) surface.  Tail optimality remains the visible
Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate
      (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
        hUcols hV hrepr hhead_nonzero)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Tail-optimal thin-rectangular SVD scalar-rate relative surface with a
strict-positive source-head singular-value hypothesis.  Tail optimality remains
the visible Eckart--Young/SVD-order obligation. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ≤
        lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho *
          frobNormRect
            (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
              (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull))) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNormRect
          (sourceSVDFactorMatrix (rectangularThinSVDTailLeft Ufull)
            (squareSVDTailDiagonal sigma) (squareSVDTailRight Vfull)) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) := by
  exact
    columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD
      hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
      Z heps hVZ hcrossTerm hopt hrelative

/-- Thin-rectangular SVD scalar-rate relative surface with the source-head
residual, tail-optimality hypothesis, and scalar comparison written directly
in terms of the displayed tail singular-value block. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_blockDiagonalSourceSVDTailCertificate_sigmaTail
    (BlockDiagonalSourceSVDTailCertificate.of_rectangularThinSVD
      hUcols hV hrepr hhead_nonzero)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hopt : ∀ B, RectRankAtMost m (r + q) r B →
      frobNorm (squareSVDTailDiagonal sigma) ≤ lowRankResidualFrob A B)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hopt hrelative

/-- Ordered thin-rectangular SVD scalar-rate relative surface with the
source-head residual and scalar comparison written directly in terms of the
displayed tail singular-value block.

The visible tail-optimality hypothesis from
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail`
is discharged by LR.1dq from exact singular-square antitonicity.  This remains
exact-object theorem-surface propagation and does not certify computed
SVD/projector/Gram/inverse/sketch/product arithmetic. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_nonzero : ∀ a : Fin r, sigma (Fin.castAdd q a) ≠ 0)
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail
    hUcols hV hrepr hhead_nonzero Z heps hVZ hcrossTerm
    (fun B hB =>
      rectangularThinSVD_sigmaTail_le_lowRankResidualFrob_of_antitone
        hUcols hV hrepr hmono B hB)
    hrelative

/-- Strict-positive-head version of
`columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone`. -/
theorem columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_head_pos_sigmaTail_antitone
    {m r q : ℕ}
    {A : Fin m → Fin (r + q) → ℝ}
    {Ufull : Fin m → Fin (r + q) → ℝ}
    {Vfull : Fin (r + q) → Fin (r + q) → ℝ}
    {sigma : Fin (r + q) → ℝ}
    (hUcols :
      ∀ a b : Fin (r + q),
        (∑ i : Fin m, Ufull i a * Ufull i b) =
          if a = b then 1 else 0)
    (hV : IsOrthogonal (r + q) Vfull)
    (hrepr :
      ∀ i j,
        A i j =
          ∑ k : Fin (r + q), Ufull i k * (sigma k * Vfull j k))
    (hhead_pos : ∀ a : Fin r, 0 < sigma (Fin.castAdd q a))
    (Z : Fin (r + q) → Fin r → ℝ)
    {eps rho : ℝ}
    (heps : 0 ≤ eps)
    (hVZ :
      Matrix.det
          (rightSketchCrossGram (squareSVDHeadRight Vfull) Z :
            Matrix (Fin r) (Fin r) ℝ) ≠ 0)
    (hcrossTerm :
      frobNormRect
          (matMulRectLeft (squareSVDTailDiagonal sigma)
            (rightSketchCrossGramRectInvFactor
              (squareSVDTailRight Vfull) Z (squareSVDHeadRight Vfull))) ≤
        eps * frobNorm (squareSVDTailDiagonal sigma))
    (hmono :
      ∀ i j : Fin (r + q), (i : ℕ) ≤ (j : ℕ) →
        sigma j ^ 2 ≤ sigma i ^ 2)
    (hrelative :
      2 *
          (Real.sqrt (1 + eps ^ 2) *
            frobNorm (squareSVDTailDiagonal sigma)) ≤
        rho * frobNorm (squareSVDTailDiagonal sigma)) :
    IsBestRankApproxFrob m (r + q) r A
        (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
          (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) ∧
      lowRankResidualFrob A
          (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
            (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) =
        frobNorm (squareSVDTailDiagonal sigma) ∧
      IsSymmetricFiniteMatrix (columnSketchGramInverseProjector A Z) ∧
      Nonempty
        (LeftFactorThrough
          (columnSketchGramInverseProjector A Z)
          (columnSketch A Z)) ∧
      (∀ i a,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketch A Z) i a =
          columnSketch A Z i a) ∧
      (∀ i j,
        preconditionRows
            (columnSketchGramInverseProjector A Z)
            (columnSketchGramInverseProjector A Z) i j =
          columnSketchGramInverseProjector A Z i j) ∧
      RectRankAtMost m (r + q) r
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ∧
      lowRankResidualFrob A
        (preconditionRows (columnSketchGramInverseProjector A Z) A) ≤
          rho *
            lowRankResidualFrob A
              (sourceSVDFactorMatrix (rectangularThinSVDHeadLeft Ufull)
                (squareSVDHeadDiagonal sigma) (squareSVDHeadRight Vfull)) :=
  columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectangularThinSVD_sigmaTail_antitone
    hUcols hV hrepr (squareSVDHeadValues_nonzero_of_pos hhead_pos)
    Z heps hVZ hcrossTerm hmono hrelative

end NumStability
