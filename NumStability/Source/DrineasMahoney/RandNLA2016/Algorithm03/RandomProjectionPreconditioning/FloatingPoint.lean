import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.UniformRows
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowComposition
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.FloatingPoint
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRowComposition

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.FloatingPoint

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.UniformRowSamplingFP`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/UniformRowSamplingFP.lean
--
-- Floating-point transfer for Algorithm 3 uniform row sampling after
-- signed-Hadamard preprocessing.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602







namespace NumStability

open scoped BigOperators

/-!
## Floating-point uniform row sketches

The exact Algorithm 3 uniform row sketch samples row `i` and rescales it by
`1 / sqrt(s / m)`, so its Gram matrix is the uniform sample-average matrix
already analyzed in `UniformRowSamplingMGF`.  This file adds the corresponding
rounded row-scaling and rounded Gram-dot-product layer, reusing the repository's
division, row-sketch Gram, and dot-product perturbation lemmas.
-/

-- ============================================================
-- Uniform row-scaling kernels
-- ============================================================




























namespace ComputedUniformRowScaleDen

variable {fp : FPModel} {m s : ℕ}













































































































































































































































































































































































































































































































































































































































































































































































































































































































end ComputedUniformRowScaleDen

/- ============================================================
   Concrete denominator routine used by the final SRHT endpoints
   ============================================================ -/
















































































































































































































































































































































































































































































-- ============================================================
-- Fully floating-point uniform sample Gram
-- ============================================================



























































































































































































































































































































































































































































































































































































-- ============================================================
-- High-probability Frobenius FP transfer for arbitrary uniform-row inputs
-- ============================================================










































































































































































































































































-- ============================================================
-- High-probability floating-point transfer for Algorithm 3
-- ============================================================

















































































































































-- ============================================================
-- Exact right-factor congruence for Algorithm 3 input matrices
-- ============================================================

























































































































































































































































































































































































































































































































/-- Source-sharp logarithmic SRHT preprocessing plus uniform row sampling for
the actual Algorithm 3 input matrix `A = U C`.  The random signs and uniform row
law remain exact; `U` and `C` are exact analysis-only factors. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    {m r n s : ℕ} (H : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
          H U C ε) := by
  have hExactU :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm)
      (signedHadamardUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (m := m) (r := r) (n := n) (s := s) H U C ε hU hm hs))

























/-- Transfer an exact factored-input Algorithm 3 event and a concrete
computed-input perturbation event to the fully floating-point sampled Gram. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent H U C ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp H (preconditionColumns U C) Vhat dhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pmat : Fin m → Fin m → ℝ :=
      matMul m H (diagMatrix (rademacherSignVector x.1))
    let Y : Fin m → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, G] using FiniteProbability.eventProb_mono Pprob hsubset)






















































































































































































































































































































































































































































































































/-- The concrete computed-left preconditioned basis satisfies the generic
computed-`Vhat` perturbation event with probability one under the joint
signed-Hadamard/uniform-row law. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftPreconditionedBasis,
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat x := by
        simp [signedHadamardComputedLeftUniformRowPerturbBudget, V, Vhat, E]

/-- The concrete computed-left preconditioned basis with a computed uniform
row-scale denominator satisfies the computed-denominator perturbation event
with probability one under the joint signed-Hadamard/uniform-row law. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
        dhat
        (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
          fp H U Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftPreconditionedBasis,
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
          fp H U Pihat dhat x := by
        simp [signedHadamardComputedLeftUniformRowComputedDenPerturbBudget,
          V, Vhat, E]






























































































































































































/-- The concrete computed-left finite signed-mixing basis satisfies the
generic computed-`Vhat` perturbation event with probability one. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
        fp G U
        (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
        (signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedMixingComputedLeftPreconditionedBasis,
      signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat x := by
        simp [signedMixingComputedLeftUniformRowPerturbBudget, V, Vhat, E]

/-- The concrete computed-left finite signed-mixing basis satisfies the
computed-denominator perturbation event with probability one. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp G U
        (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
        dhat
        (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
          fp G U Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedMixingComputedLeftPreconditionedBasis,
      signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedMixingComputedLeftUniformRowComputedDenPerturbBudget
          fp G U Pihat dhat x := by
        simp [signedMixingComputedLeftUniformRowComputedDenPerturbBudget,
          V, Vhat, E]

/-- Generic exact-to-computed transfer for finite signed mixing with the exact
mathematical row-scale denominator.  The preprocessing, row divisions, and Gram
arithmetic are charged by the perturbation event. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
            fp G U Vhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  classical
  let P := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowSampleGramTwoSidedEvent G U ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbEvent
      fp G U Vhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
      fp Vhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedMixingUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F, signedMixingComputedPreconditionedFlUniformRowPerturbEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Generic exact-to-computed transfer for finite signed mixing with a computed
uniform row-scale denominator. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowSampleGramTwoSidedEvent G U ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp G U Vhat dhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedMixingUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/- ============================================================
-- CountSketch computed preprocessing plus uniform-row FP transfer
-- ============================================================ -/





















































































































































































































































/-- The sparse computed CountSketch basis satisfies the exact-denominator
uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbEvent
        fp U
        (countSketchSparseComputedPreconditionedBasis fp U)
        (countSketchSparseUniformRowPerturbBudget fp U)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget fp hash sign U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |sign (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [E, countSketchSparseApplyFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      mul_nonneg hcoeff_nonneg hsum_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, countSketchSparseComputedPreconditionedBasis]
      using
        fl_countSketchSparseApply_entry_error_bound
          fp hash sign U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowPerturbBudget fp U x := by
        simp [countSketchSparseUniformRowPerturbBudget, V, Vhat, E,
          hash, sign]

/-- The sparse computed CountSketch basis satisfies the computed-denominator
uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasis fp U)
        dhat
        (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget fp hash sign U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |sign (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [E, countSketchSparseApplyFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      mul_nonneg hcoeff_nonneg hsum_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, countSketchSparseComputedPreconditionedBasis]
      using
        fl_countSketchSparseApply_entry_error_bound
          fp hash sign U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat x := by
        simp [countSketchSparseUniformRowComputedDenPerturbBudget, V, Vhat, E,
          hash, sign]

/-- The stored-sign sparse computed CountSketch basis satisfies the
computed-denominator uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSign
          fp U storedSignOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp U storedSignOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSign
      fp U storedSignOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignFpAbsBudget fp hash sign signhat U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyEntryFpAbsBudget
          fp hash signhat.vector U i j := by
      exact mul_nonneg hcoeff_nonneg hsum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i t) *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i t))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignFpAbsBudget,
      countSketchSparseApplyStoredSignEntryFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSign,
      countSketchSparseApplyStoredSignFpAbsBudget] using
        fl_countSketchSparseApplyWithStoredSign_entry_error_bound
          fp hash sign signhat U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp U storedSignOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp U storedSignOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp U storedSignOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignPerturbBudget,
          V, Vhat, E, hash, sign, signhat]

/-- The stored-sign sparse computed CountSketch basis with exact per-bucket
traversal orders satisfies the computed-denominator uniform-row perturbation
event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
          fp U storedSignOf orderOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp U storedSignOf orderOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let order :
      (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i) := orderOf hash
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
      fp U storedSignOf orderOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignPermutedFpAbsBudget
      fp hash sign signhat U order
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hbase_sum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i (order i t))| *
            |U (countSketchBucketIndex hash i (order i t)) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyPermutedEntryFpAbsBudget
          fp hash signhat.vector U order i j := by
      exact mul_nonneg hcoeff_nonneg hbase_sum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i (order i t)) *
            |U (countSketchBucketIndex hash i (order i t)) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i (order i t)))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignPermutedFpAbsBudget,
      countSketchSparseApplyStoredSignPermutedEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted,
      countSketchSparseApplyStoredSignPermutedFpAbsBudget, hash, sign,
      signhat, order] using
        fl_countSketchSparseApplyWithStoredSignPermuted_entry_error_bound
          fp hash sign signhat U order hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp U storedSignOf orderOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp U storedSignOf orderOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp U storedSignOf orderOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget,
          V, Vhat, E, hash, sign, signhat, order]

/-- The stored-sign sparse computed CountSketch basis with tree-reduced
bucket accumulations satisfies the computed-denominator uniform-row
perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
          fp U storedSignOf treeOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp U storedSignOf treeOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let tree :
      (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1) := treeOf hash
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignTree
      fp U storedSignOf treeOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignTreeFpAbsBudget
      fp hash sign signhat U tree
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (tree i).depth +
            fp.u * gamma fp (tree i).depth := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hdepth hash i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hdepth hash i)))
    have hbase_sum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyTreeEntryFpAbsBudget
          fp hash signhat.vector U tree i j := by
      exact mul_nonneg hcoeff_nonneg hbase_sum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i t) *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i t))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignTreeFpAbsBudget,
      countSketchSparseApplyStoredSignTreeEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree,
      countSketchSparseApplyStoredSignTreeFpAbsBudget, hash, sign, signhat,
      tree] using
        fl_countSketchSparseApplyWithStoredSignTree_entry_error_bound
          fp hash sign signhat U tree (hdepth hash) i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp U storedSignOf treeOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp U storedSignOf treeOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp U storedSignOf treeOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget,
          V, Vhat, E, hash, sign, signhat, tree]

/-- Generic exact-to-computed transfer for CountSketch preprocessing with a
computed uniform row-scale denominator.  The exact event is the collision-free
CountSketch plus exact uniform-row concentration event; the perturbation event
charges computed CountSketch application, computed row scaling, and rounded
Gram dot products. -/
theorem countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε))
    (hComp :
      1 - δComp ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchUniformRowSampleGramTwoSidedEvent U ε
  let F : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp U Vhat dhat τ
  let M : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, countSketchUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)




































































































































































































































































































































/-- Transfer an exact CountSketch factored-input event and a concrete computed
perturbation event to the fully floating-point sampled Gram. -/
theorem countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε))
    (hComp :
      1 - δComp ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchUniformRowFactoredInputSampleGramTwoSidedEvent U C ε
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let F : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A Vhat dhat τ
  let M : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F, A] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let Pmat : Fin r → Fin m → ℝ :=
      countSketchRows x.1.1 (rademacherSignVector x.1.2)
    let Y : Fin r → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, countSketchUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, M] using FiniteProbability.eventProb_mono Pprob hsubset)

























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Nonconditional finite signed-mixing FP endpoint with exact supplied
factors, rounded formation of `G diag(ω)`, rounded formation of
`Vhat = fl((G diag(ω))U)`, rounded row divisions by the exact mathematical
denominator, and rounded Gram dot products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          ε
          (signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)) := by
  intro Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hn hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
          fp G U
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          (signedMixingComputedLeftUniformRowPerturbBudget
            fp G U Pihat)) = 1 := by
    simpa [Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
        fp G U Pihat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
            fp G U
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
            (signedMixingComputedLeftUniformRowPerturbBudget
              fp G U Pihat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
      (hr := hr) (ε := ε) (δExact := δPre + δSample)
      (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Nonconditional finite signed-mixing FP endpoint with exact supplied
factors, rounded formation of `G diag(ω)`, rounded formation of
`Vhat = fl((G diag(ω))U)`, a computed uniform row-scale denominator, rounded
row divisions, and rounded Gram dot products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat dhat)) := by
  intro Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hn hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp G U
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          dhat
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat dhat)) = 1 := by
    simpa [Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp G U Pihat dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G U
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
            dhat
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G U Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := δPre + δSample) (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowComputedDenPerturbBudget
        fp G U Pihat dhat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Concrete-denominator finite signed-mixing FP endpoint with exact supplied
factors.  The denominator used by the implemented row scaling is
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, represented by
`uniformRowFlSqrtMulInvSqrtScaleDen`; exact Rademacher and uniform-row laws
remain mathematical laws. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
      fp G U (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hn hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget





















































































































































/-- Exact finite signed-mixing preprocessing plus uniform row sampling for the
actual Algorithm 3 input matrix `A = U C`.  The signs and uniform row law remain
exact; `U` and `C` are exact analysis factors. -/
theorem signedMixingUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    {r m q n s : ℕ} (G : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
          G U C ε) := by
  have hExactU :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hq hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr)
      (signedMixingUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (r := r) (m := m) (q := q) (n := n) (s := s) G U C ε hU hr hs))

























/-- Transfer an exact finite signed-mixing factored-input event and a concrete
computed perturbation event to the fully floating-point sampled Gram. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
            G U C ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent G U C ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp G (preconditionColumns U C) Vhat dhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pmat : Fin r → Fin m → ℝ :=
      signedMixingRows G (rademacherSignVector x.1)
    let Y : Fin r → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, M] using FiniteProbability.eventProb_mono Pprob hsubset)

/-- Nonconditional finite signed-mixing FP endpoint for an actual Algorithm 3
input factored as `A = U C`, using exact supplied `G`, exact analysis factors
`U,C`, rounded `G diag(ω)`, rounded `Vhat = fl(Pihat * A)`, a computed
uniform row-scale denominator, rounded row divisions, and rounded Gram dot
products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) := by
  intro A Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
            G U C ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U C hr hq hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp G A
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) = 1 := by
    simpa [A, Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp G A Pihat dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G A
            (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
            dhat
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U) (C := C)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := δPre + δSample) (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowComputedDenPerturbBudget
        fp G A Pihat dhat)
      hExact hComp
  simpa [A, Pihat, add_zero] using hTransfer

/-- Total-failure-budget form of the actual-input finite signed-mixing endpoint.

This is the same fully computed theorem as
`..._ge_one_sub_delta_of_entry_sq_le_uniform`, but the preprocessing and sample
failures are combined into a single target `δ`. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample δ : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget : δPre + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - δ ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) := by
  intro A Pihat
  have hbase :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
            dhat
            ε
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G A Pihat dhat)) := by
    simpa [A, Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        fp G U C dhat hr hq hGorth hU halpha hB hs hγm hγs htheta
        hδSample hGcap hpreBudget hsampleBudget
  have hleft : 1 - δ ≤ 1 - (δPre + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator finite signed-mixing FP endpoint for an actual input
factored as `A = U C`.  The theorem instantiates the generic computed
denominator with `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, charging rounded
denominator formation in addition to rounded `G diag(ω)`, `Vhat`, row
division, and Gram-dot arithmetic. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
      fp G U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hq hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget

/-- Total-failure-budget version of the concrete-denominator finite
signed-mixing factored-input FP endpoint. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample δ : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget : δPre + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - δ ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
      fp G U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hq hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget htotalBudget



























/-- The concrete computed-left and computed-input preconditioned basis
satisfies the generic computed-`Vhat` perturbation event with probability one
under the joint signed-Hadamard/uniform-row law.  This theorem charges a
computed basis or singular-vector table through `Uhat` instead of silently using
the exact analysis basis as an implemented object. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat)
        (signedHadamardComputedLeftInputUniformRowPerturbBudget
          fp H Uhat Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftInputEntryErrorBudget_nonneg
          fp (Pihat x.1) Uhat hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftInputPreconditionedBasis,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound
          fp (Pihat x.1) Uhat hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftInputUniformRowPerturbBudget
          fp H Uhat Pihat x := by
        simp [signedHadamardComputedLeftInputUniformRowPerturbBudget, V, Vhat, E]




























/-- The concrete computed-left and computed-input preconditioned basis with a
computed uniform row-scale denominator satisfies the computed-denominator
perturbation event with probability one under the joint signed-Hadamard/uniform
row law.  This theorem charges a computed or stored input matrix through
`Uhat` and does not add any probability-construction loss. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp H U
        (signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat)
        dhat
        (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
          fp H Uhat Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftInputEntryErrorBudget_nonneg
          fp (Pihat x.1) Uhat hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftInputPreconditionedBasis,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound
          fp (Pihat x.1) Uhat hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
          fp H Uhat Pihat dhat x := by
        simp [signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget,
          V, Vhat, E]

/-- Exact/stored signed-Hadamard specialization of the concrete computed-left
perturbation certificate.  This closes the zero-transform-storage baseline for
the SRHT computed-`Vhat` path: the perturbation event still charges rounded
formation of `Vhat`, rounded row scaling, and rounded Gram dot products, but
not preprocessing-matrix storage error. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_exactStoredComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U
          (signedHadamardExactStoredPreconditioner fp H))
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U
          (signedHadamardExactStoredPreconditioner fp H))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp H U (signedHadamardExactStoredPreconditioner fp H) hm hs hγm hγs

/-- Exact signed-Hadamard factors with rounded preconditioner formation still
instantiate the computed-left SRHT perturbation event with probability one.
Compared with `signedHadamardExactStoredPreconditioner`, the transform budget
now includes the rounded product that forms `H * diag(sign)`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U
          (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U
          (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp H U
      (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling and
rounded signed preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The Rademacher and uniform-row laws
remain exact; the budget charges the rounded scale table, `H D_omega`
formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternPreconditioner fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternPreconditioner fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω => signedHadamardScaledPatternPreconditioner fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded storage of the realized Rademacher signs, and rounded signed
preconditioner formation instantiates the computed-left SRHT perturbation
event with probability one.  The Rademacher and uniform-row laws remain exact;
the budget charges the rounded scale table, sign storage, `H D_omega`
formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded add-zero storage of the realized Rademacher signs, and rounded signed
preconditioner formation instantiates the computed-left SRHT perturbation
event with probability one.  The Rademacher and uniform-row laws remain exact;
the budget charges the rounded scale table, add-zero sign storage,
`H D_omega` formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
              fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
              fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
          fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded subtract-zero storage of the realized Rademacher signs, and rounded
signed preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The Rademacher and uniform-row laws
remain exact; the budget charges the rounded scale table, subtract-zero sign
storage, `H D_omega` formation, `Vhat` formation, row scaling, and Gram dot
products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
              fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
              fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
          fp S ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
`sqrt (1 / 2^p)` scaling and rounded signed-preconditioner formation
instantiates the computed-left SRHT perturbation event with probability one.
The bit-parity table, Rademacher law, and uniform-row law are exact; the budget
charges scale formation, `H D_omega` formation, `Vhat` formation, row scaling,
and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternPreconditioner fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternPreconditioner fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternPreconditioner fp ω hγm)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; the
budget charges the generated FHT butterfly schedule, rounded FHT scale,
`Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtSchedulePreconditioner fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtSchedulePreconditioner fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtSchedulePreconditioner fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded add-zero storage/copy after every
FHT pair update instantiates the computed-left SRHT perturbation event with
probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded multiply-one storage/copy after
every FHT pair update instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded subtract-zero storage/copy after
every FHT pair update instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded add-zero writeback
instantiates the computed-left SRHT perturbation event with probability one.
The Rademacher and uniform-row laws remain exact; only non-probability
writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded multiply-one writeback
instantiates the computed-left SRHT perturbation event with probability one.
The Rademacher and uniform-row laws remain exact; only non-probability
writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded subtract-zero
writeback instantiates the computed-left SRHT perturbation event with
probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded Rademacher-sign
storage before the FHT stages instantiates the computed-left SRHT perturbation
event with probability one.  Only non-probability storage/arithmetic is
charged; the Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignPreconditioner fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded add-zero
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded multiply-one
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded subtract-zero
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
add-zero writeback instantiates the computed-left SRHT perturbation event with
probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
multiply-one writeback instantiates the computed-left SRHT perturbation event
with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
subtract-zero writeback instantiates the computed-left SRHT perturbation
event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_mul sign_i 1` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignPreconditioner fp ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_add sign_i 0` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
          fp ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_sub sign_i 0` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
          fp ω hγm)
      hm hs hγm hγs

/-- Generic transfer from the exact signed-Hadamard/uniform-row event to an
implemented preprocessed basis `Vhat`.  The theorem does not assume the
preprocessing arithmetic is exact: all errors in computing `Vhat`, row scaling,
and the final Gram entries are charged by the perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
      fp H U Vhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
      fp Vhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedHadamardUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F, signedHadamardComputedPreconditionedFlUniformRowPerturbEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G,
      signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Generic transfer from the exact signed-Hadamard/uniform-row event to an
implemented preprocessed basis whose uniform row-scale denominator is computed
in floating point.  All non-probability computation is charged by the supplied
computed-denominator perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp H U Vhat dhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedHadamardUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G,
      signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Coordinate-Hoeffding signed-Hadamard preprocessing composed with iid uniform
row sampling, with the sampled Gram matrix formed in floating point.

This is the floating-point transfer for the scoped Algorithm 3 route: it reuses
the exact joint preprocessing-plus-uniform-sampling theorem and the local
division/dot-product perturbation bound above. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε δPre δSample : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedEvent fp H U ε) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardFlUniformRowSampleGramTwoSidedEvent fp H U ε
  have hExact :
      1 - (δPre + δSample) ≤ P.eventProb E := by
    simpa [P, E] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have hsubset : E ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τ : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hpert : frobNorm Delta ≤ τ := by
      simpa [Delta, τ] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hx.1 hx.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G, signedHadamardFlUniformRowSampleGramTwoSidedEvent, V, τ] using
      And.intro hUpper hLower
  exact hExact.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Coordinate-Hoeffding signed-Hadamard preprocessing with an implemented
preprocessed basis `Vhat`.  The additional `δComp` event charges every
floating-point operation used to build `Vhat` and then compute the sampled Gram
from it. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε δPre δSample δComp : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ))
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa [add_assoc] using h

/-- Constant-radius coordinate-Hoeffding wrapper for an implemented
preprocessed basis `Vhat`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε τ δPre δSample δComp : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  simpa [signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent]
    using
      signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
        fp H U Vhat hH hflat hU hm hn hB hlam hs htheta hδSample
        (fun _ => τ) hComp hpreBudget hsampleBudget

/-- Deterministic-radius version of the floating-point uniform-sketch transfer.

If a deterministic budget `τ` dominates the sample-dependent FP perturbation
budget for every joint preprocessing/sampling outcome, then the same joint
probability lower bound holds with radius `ε + τ`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε τ δPre δSample : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hτ :
      ∀ x : RademacherTrace m × RowTrace m s,
        let V : Fin m → Fin n → ℝ :=
          preconditionRows
            (matMul m H (diagMatrix (rademacherSignVector x.1))) U
        uniformRowSampleGramFullFpPerturbBudget fp s V x.2 ≤ τ)
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent fp H U ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent fp H U ε τ
  have hExact :
      1 - (δPre + δSample) ≤ P.eventProb E := by
    simpa [P, E] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have hsubset : E ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τx : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hpert : frobNorm Delta ≤ τx := by
      simpa [Delta, τx] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hx.1 hx.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hτ_le : τx ≤ τ := by
      simpa [V, τx] using hτ x
    have hscalar : ε + τx ≤ ε + τ := by linarith
    have hRhs :
        finiteLoewnerLe
          (fun j k : Fin n => (ε + τx) * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_finiteIdMatrix_mono hscalar
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact finiteLoewnerLe_trans hUpperAdd hRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact finiteLoewnerLe_trans hLowerAdd hRhs
    simpa [G, signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent, V]
      using And.intro hUpper hLower
  exact hExact.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Source-sharp SRHT floating-point transfer with a fixed row-norm-derived
budget.

This theorem does not assume a global perturbation domination hypothesis.  It
uses the same SRHT preprocessing event as the exact source-sharp theorem; on
that event every sampled row has squared norm at most
`S^2 = (sqrt(n / m) + t)^2`, so the local FP perturbation budget is bounded by
`uniformRowSampleGramFullFpConstBudget fp s (m * S^2)`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε δPre δSample : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
    let τ : ℝ :=
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * S ^ 2)
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp H U ε τ) := by
  classical
  intro S τ
  let Psign := rademacherTraceProbability m
  let Q := uniformRowTraceProbability (m := m) (steps := s) hm
  let M : RademacherTrace m → Fin m → Fin n → ℝ :=
    fun ω =>
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector ω))) U
  let Epre : Set (RademacherTrace m) :=
    {ω | ∀ i : Fin m, rowNormSq (M ω) i ≤ S ^ 2}
  let Fsample : RademacherTrace m → Set (RowTrace m s) :=
    fun ω =>
      {samples |
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram (M ω) samples j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram (M ω) samples j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hS_def : S = Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t := rfl
  have hPre : 1 - δPre ≤ Psign.eventProb Epre := by
    have hdelta :=
      rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight
        H U hm hflat hU t ht
    linarith
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hS_pos : 0 < S := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) :=
      Real.sqrt_nonneg _
    dsimp [S]
    linarith
  let L : ℝ := (m : ℝ) * S ^ 2
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos hmRpos (sq_pos_of_ne_zero (ne_of_gt hS_pos))
  have hSample : ∀ ω, ω ∈ Epre → 1 - δSample ≤ Q.eventProb (Fsample ω) := by
    intro ω hω
    have hMorth : HasOrthonormalColumns (M ω) := by
      simpa [M] using
        signedOrthogonalPreconditionRows_hasOrthonormalColumns
          H (rademacherSignVector ω) U hH
          (rademacherSignVector_sq ω) hU
    have hrowBound :
        ∀ i : RowSample m, (m : ℝ) * rowNormSq (M ω) i ≤ L := by
      intro i
      have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hmRpos
      calc
        (m : ℝ) * rowNormSq (M ω) i
            ≤ (m : ℝ) * S ^ 2 :=
              mul_le_mul_of_nonneg_left (hω i) hm_nonneg
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample m,
          finiteLoewnerLe
            (fun j k : Fin n => uniformRowOuterGramSample (M ω) i j k)
            (fun j k : Fin n => L * finiteIdMatrix j k) := by
      intro i
      have hbase :=
        uniformRowOuterGramSample_finiteLoewnerLe_of_rowNormSq_le
          (M ω) i (hω i)
      simpa [L] using hbase
    have hbudget' :
        let betaUpper : ℝ :=
          (Real.exp (theta * L) - theta * L - 1) / L ^ 2
        let betaLower : ℝ := Real.exp theta - theta - 1
        let tailUpper : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
        let tailLower : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
        tailUpper + tailLower ≤ δSample := by
      simpa [S, L] using hsampleBudget
    simpa [Q, Fsample] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
        (s := s) (theta := theta) (ε := ε) (δ := δSample) (L := L)
        (M ω) hMorth hm hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - (δPre + δSample) ≤
        (Psign.prod Q).eventProb
          {x : RademacherTrace m × RowTrace m s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      Psign Q Epre Fsample δPre δSample hδSample hPre hSample
  have hsubset :
      {x : RademacherTrace m × RowTrace m s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
        fp H U ε τ := by
    intro x hx
    let V : Fin m → Fin n → ℝ := M x.1
    let τx : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxsample :
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram V x.2 j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Fsample, V] using hx.2
    have hpert : frobNorm Delta ≤ τx := by
      simpa [Delta, τx, V] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxsample.1 hxsample.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hrow_samples : ∀ r : Fin s, rowNormSq V (x.2 r) ≤ S ^ 2 := by
      intro r
      simpa [V] using hx.1 (x.2 r)
    have hτ_le : τx ≤ τ := by
      have hR_nonneg : 0 ≤ S ^ 2 := sq_nonneg S
      simpa [τ, τx, V] using
        uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le
          fp V x.2 hm hs hγ hR_nonneg hrow_samples
    have hscalar : ε + τx ≤ ε + τ := by linarith
    have hRhs :
        finiteLoewnerLe
          (fun j k : Fin n => (ε + τx) * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_finiteIdMatrix_mono hscalar
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact finiteLoewnerLe_trans hUpperAdd hRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact finiteLoewnerLe_trans hLowerAdd hRhs
    simpa [signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent, V]
      using And.intro hUpper hLower
  exact hprod.trans (by
    simpa [signedHadamardUniformRowTraceProbability, Psign, Q] using
      FiniteProbability.eventProb_mono (Psign.prod Q) hsubset)

/-- Source-sharp SRHT wrapper for an implemented preprocessed basis `Vhat`.
The SRHT concentration is still proved for the exact `H D_ω U`; the additional
`δComp` event is the explicit place where floating-point construction of
`Vhat` is charged. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε δPre δSample δComp : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ))
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
        H U hH hflat hU hm ht hs htheta hδSample
        hpreBudget hsampleBudget
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa [add_assoc] using h

/-- Constant-radius source-sharp SRHT wrapper for an implemented preprocessed
basis `Vhat`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε τ δPre δSample δComp : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  simpa [signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent]
    using
      signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
        fp H U Vhat hH hflat hU hm ht hs htheta hδSample
        (fun _ => τ) hComp hpreBudget hsampleBudget

/-- Logarithmic-preprocessing wrapper for the source-sharp SRHT floating-point
constant-budget theorem. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
    let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
    let τ : ℝ :=
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * S ^ 2)
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp H U ε τ) := by
  intro t S τ
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by
    simpa [t] using
      real_sqrt_eight_log_div_pos_of_pos_lt
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
  have hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre := by
    have heq :=
      real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
    exact le_of_eq (by simpa [t] using heq)
  simpa [t, S, τ] using
    signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
      fp H U hH hflat hU hm ht hs hγ htheta hδSample
      hpreBudget hsampleBudget

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for an implemented
preprocessed basis `Vhat`, with all construction errors charged in the
computed-preprocessing perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε τ δPre δSample δComp : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by
    simpa [t] using
      real_sqrt_eight_log_div_pos_of_pos_lt
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
  have hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre := by
    have heq :=
      real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
    exact le_of_eq (by simpa [t] using heq)
  simpa [t,
    signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
      fp H U Vhat hH hflat hU hm ht hs htheta hδSample
      hComp hpreBudget hsampleBudget

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for a concrete
computed preprocessed basis whose perturbation event has already been proved
with probability one.

This is an intermediate adapter: unlike the constant-budget theorem above, the
radius is the supplied sample-dependent concrete perturbation budget `τ`.  It
removes the artificial `δComp` loss when a later theorem instantiates the
probability-one perturbation certificate for an actual computed SRHT path. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
          fp H U Vhat τ) = 1)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa using h

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for a concrete
computed preprocessed basis with a computed uniform row-scale denominator,
assuming the concrete computed-denominator perturbation event has already been
proved with probability one. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H U Vhat dhat τ) = 1)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H U Vhat dhat τ) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat dhat hm τ hExact hComp
  simpa using h

/-- Final nonconditional exact-denominator SRHT endpoint for the modeled
materialized scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

The random signs and uniform row trace are exact laws.  The computed
non-probability objects are the rounded scale/sign-pattern preconditioner,
the rounded stored signs, the rounded formation of `H D_ω`, the rounded
matrix product forming `Vhat`, the rounded uniform row divisions by the exact
mathematical denominator `sqrt(s/m)`, and the rounded Gram dot products.  All
of these errors are charged by the concrete budget
`signedHadamardComputedLeftUniformRowPerturbBudget`; no perturbation event or
`δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          ε
          (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) := by
  intro H Pihat
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
          fp H U
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) = 1 := by
    simpa [H, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
        fp S U hm hs hγm hγs
  simpa [H, Pihat] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
      fp H U
      (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
      hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
      (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)
      hCompEq hsampleBudget

/-- Final nonconditional computed-denominator SRHT endpoint for the modeled
materialized scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

The random signs and uniform row trace are exact laws.  The computed
non-probability objects are the rounded scale/sign-pattern preconditioner,
rounded stored signs, rounded formation of `H D_ω`, rounded matrix product
forming `Vhat`, the computed nonzero denominator `dhat`, rounded row divisions
by `dhat.den`, and rounded Gram dot products.  All of these errors are charged
by the concrete budget
`signedHadamardComputedLeftUniformRowComputedDenPerturbBudget`; no
perturbation-event or `δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) := by
  intro H Pihat
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H U
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) = 1 := by
    simpa [H, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H U Pihat dhat hm hs hγm hγs
  simpa [H, Pihat] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
      fp H U
      (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
      dhat hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H U Pihat dhat)
      hCompEq hsampleBudget

/-- Final concrete-denominator SRHT endpoint for the modeled materialized
scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

This specializes the computed-denominator endpoint to the actual scalar
routine `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))` for the uniform row-scale
denominator.  Thus the denominator formation, row divisions, and Gram dot
products are all charged by locally proved floating-point bounds, with no
remaining denominator-certificate parameter in the final theorem surface. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    let dhat : ComputedUniformRowScaleDen fp m s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) := by
  intro H Pihat dhat
  simpa [H, Pihat, dhat] using
    signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
      fp S U
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs)
      hH hflat hU hm hδPre_pos hδPre_lt hs hγm hγs htheta hδSample
      hsampleBudget

/-- Final nonconditional computed-denominator SRHT endpoint for the modeled
materialized scaled-pattern path on the actual Algorithm 3 input matrix
`A = U C`.

The exact factors `U` and `C` are analysis-only objects used to state the
source-sharp SRHT row-norm theorem; the algorithm computes with the input
matrix `A = U C` through the rounded product `fl(Pihat * A)`.  The random signs
and uniform row trace are exact laws.  The computed non-probability objects are
the rounded scale/sign-pattern preconditioner, rounded stored signs, rounded
formation of `H D_ω`, rounded matrix product forming `Yhat = fl(Pihat * A)`,
the computed nonzero denominator `dhat`, rounded row divisions by `dhat.den`,
and rounded Gram dot products.  All errors are charged by the concrete budget
`signedHadamardComputedLeftUniformRowComputedDenPerturbBudget`; no perturbation
event or `δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m r n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro H A Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat] using h

/-- Final concrete-denominator SRHT endpoint for the modeled materialized
scaled-pattern path on the actual Algorithm 3 input matrix `A = U C`.

This is the implementation-facing version of the factored-input theorem for
the closed denominator routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))`.  The exact factors `U` and `C`
are analysis-only witnesses for the source-sharp SRHT row-norm theorem, while
the algorithm computes with `A = U C`.  The theorem charges rounded
preconditioner formation, rounded formation of `Yhat = fl(Pihat * A)`, the
concrete computed denominator, rounded row divisions, and rounded Gram dot
products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m r n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    let dhat : ComputedUniformRowScaleDen fp m s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro H A Pihat dhat
  simpa [H, A, Pihat, dhat] using
    signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
      fp S U C
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs)
      hH hflat hU hm hδPre_pos hδPre_lt hs hγm hγs htheta hδSample
      hsampleBudget

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path on the actual Algorithm 3 input matrix `A = U C`.

The exact factors `U` and `C` are analysis-only witnesses for the source-sharp
SRHT row-norm theorem; the algorithm computes with `A = U C`.  The
Sylvester/Walsh table is generated exactly by bit parity, its normalized
orthogonality and flatness are proved locally, and the computed
non-probability path charges rounded Rademacher-sign storage, generated FHT
butterfly arithmetic, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded multiply-one copies before the preconditioned product is
formed.

Compared with
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`,
this theorem charges the additional computed non-probability path
`Ahat_ij = fl_mul A_ij 1` and then forms
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`; the implemented path
uses the stored matrix certificate `ComputedMatrix.flMulOne fp A`.  The
Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputMulOneComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flMulOne fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded add-zero copies before the preconditioned product is formed.

This is the add-zero stored-input sibling of the multiply-one theorem above:
it charges `Ahat_ij = fl_add A_ij 0` before forming
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`, while the implemented
path uses the stored matrix certificate `ComputedMatrix.flAddZeroRight fp A`.
The Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputAddZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flAddZeroRight fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded subtract-zero copies before the preconditioned product is
formed.

This is the subtract-zero stored-input sibling of the multiply-one theorem
above: it charges `Ahat_ij = fl_sub A_ij 0` before forming
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`, while the implemented
path uses the stored matrix certificate `ComputedMatrix.flSubZeroRight fp A`.
The Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputSubZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flSubZeroRight fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded add-zero writeback/copy after every FHT
pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the add-zero writeback specialization of the generated-FHT endpoint
above.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_add y_i 0` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded add-zero writeback/copy, on
the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_add y_i 0` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by bit
parity, its normalized orthogonality and flatness are proved locally, and the
computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate writeback/copy
terms, rounded normalization, rounded formation of `Yhat = fl(Pihat * A)`,
the concrete computed denominator `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt
(2^p)))`, rounded sampled-row divisions, and rounded Gram dot products.  The
Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded multiply-one writeback/copy after every
FHT pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the multiply-one writeback specialization of the generated-FHT
endpoint.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_mul y_i 1` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded subtract-zero writeback/copy after every
FHT pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the subtract-zero writeback specialization of the generated-FHT
endpoint.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_sub y_i 0` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded multiply-one writeback/copy,
on the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_mul y_i 1` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by
bit parity, its normalized orthogonality and flatness are proved locally, and
the computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate multiply-one
writeback/copy terms, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded subtract-zero writeback/copy,
on the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_sub y_i 0` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by
bit parity, its normalized orthogonality and flatness are proved locally, and
the computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate subtract-zero
writeback/copy terms, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

end NumStability
