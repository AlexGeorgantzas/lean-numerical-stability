import NumStability.Algorithms.RandNLA.Preconditioning
import NumStability.Algorithms.RandNLA.UniformRowSamplingMGF
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowComposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRowComposition

/-!
# NumStability.Algorithms.RandNLA.UniformRowSamplingComposition compatibility facade

Historical declaration-bearing W11 facade. The genuine-private reverse closure remains here with its original identity; all movable commands are re-exported from canonical modules.
-/

-- Algorithms/RandNLA/UniformRowSamplingComposition.lean
--
-- Product-law composition for Algorithm 3 signed-Hadamard preprocessing
-- followed by iid uniform row sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602




namespace NumStability

open scoped BigOperators

/-!
## Joint signed-preprocessing and uniform-row sampling law

The preceding files prove two separate probability statements:

* a Rademacher/sign event that makes leverage probabilities small after a flat
  signed-Hadamard preprocessing step;
* a uniform-row trace-MGF theorem for a fixed preconditioned matrix satisfying
  the resulting deterministic one-step row bounds.

This file puts both stages on one product probability space and composes the
events.  It still does not add the floating-point uniform-sketch transfer.
-/









































































































































































































/-- Collision-free CountSketch preprocessing composed with iid uniform-row
matrix concentration.

The only preprocessing failure is the exact hash-collision event, bounded by
`m^2 / r`.  Conditional on collision-freeness, exact Rademacher signs make the
CountSketch table an isometry on the input rows, so an orthonormal-column input
basis remains orthonormal after preprocessing.  Therefore every preconditioned
row has squared norm at most one, and the uniform-row MGF theorem is
instantiated with the explicit radius `L = r`. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
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
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    {x | x.1 ∈ countSketchHashInjectiveEvent (r := r) (m := m)}
  let M : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) U
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      {samples |
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram (M x) samples j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram (M x) samples j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Ph := countSketchHashProbability (r := r) (m := m) hr
  let Pw := rademacherTraceProbability m
  let Ehash : Set (CountSketchHash r m) :=
    countSketchHashInjectiveEvent (r := r) (m := m)
  have hPreBase :
      1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤ Ph.eventProb Ehash := by
    simpa [Ph, Ehash] using
      countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv
        (r := r) (m := m) hr
  have hPre : 1 - (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ ≤ P.eventProb Epre := by
    rw [show P = Ph.prod Pw by rfl]
    rw [show Epre = {x : CountSketchHash r m × RademacherTrace m | x.1 ∈ Ehash} by
      ext x
      rfl]
    rw [FiniteProbability.prod_eventProb_fst_eq Ph Pw Ehash]
    exact hPreBase
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  let L : ℝ := (r : ℝ)
  have hLpos : 0 < L := by
    simpa [L] using hrRpos
  have hSample : ∀ x, x ∈ Epre → 1 - δSample ≤ Q.eventProb (Fsample x) := by
    intro x hx
    have hhash : Function.Injective x.1 := by
      simpa [Epre, Ehash, countSketchHashInjectiveEvent] using hx
    have hMorth : HasOrthonormalColumns (M x) := by
      simpa [M] using
        countSketchRows_preconditionRows_hasOrthonormalColumns_of_hash_injective
          x.1 (rademacherSignVector x.2) U hhash
          (rademacherSignVector_sq x.2) hU
    have hrowOne : ∀ i : RowSample r, rowNormSq (M x) i ≤ 1 := by
      intro i
      exact rowNormSq_le_one_of_hasOrthonormalColumns (M x) hMorth i
    have hrowBound :
        ∀ i : RowSample r, (r : ℝ) * rowNormSq (M x) i ≤ L := by
      intro i
      calc
        (r : ℝ) * rowNormSq (M x) i
            ≤ (r : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (hrowOne i) (le_of_lt hrRpos)
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample r,
          finiteLoewnerLe
            (fun j k : Fin n => uniformRowOuterGramSample (M x) i j k)
            (fun j k : Fin n => L * finiteIdMatrix j k) := by
      intro i
      have hbase :=
        uniformRowOuterGramSample_finiteLoewnerLe_of_rowNormSq_le
          (M x) i (hrowOne i)
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
      simpa [L] using hsampleBudget
    simpa [Q, Fsample] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
        (s := s) (theta := theta) (ε := ε) (δ := δSample) (L := L)
        (M x) hMorth hr hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (P.prod Q).eventProb
          {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample
      ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹) δSample
      hδSample hPre hSample
  have hsubset :
      {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      countSketchUniformRowSampleGramTwoSidedEvent U ε := by
    intro x hx
    exact hx.2
  exact hprod.trans (by
    simpa [countSketchUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)














































































































































































































































































































































end NumStability
