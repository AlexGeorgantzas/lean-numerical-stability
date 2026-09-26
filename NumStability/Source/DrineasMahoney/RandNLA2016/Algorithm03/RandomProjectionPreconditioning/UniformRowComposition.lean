import NumStability.Algorithms.RandomizedLinearAlgebra.Concentration.TraceMGF.UniformRows
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowComposition
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.Core
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixConcentration
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRows
import NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRowComposition

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.UniformRowSamplingComposition`; the historical path re-exports this module.
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



































/-- Exact signed-mixing preprocessing composed with iid uniform-row matrix
concentration.

The deterministic exact mixing table `G` is assumed to be a rectangular
isometry (`GᵀG = I`) and to satisfy the visible entry-square cap
`G i k ^ 2 <= alpha ^ 2`.  The first failure budget controls the exact
Rademacher signed-mixing row-norm event, and the second failure budget controls
the conditional iid exact uniform row-sampling concentration theorem.  This is
not a floating-point theorem: applying or storing `G`, forming `G D U`, and
forming the sample Gram in floating point are separate computed-quantity
obligations. -/
theorem signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    {r m n s : ℕ} (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
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
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
  classical
  let P := rademacherTraceProbability m
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let M : RademacherTrace m → Fin r → Fin n → ℝ :=
    fun ω =>
      preconditionRows
        (signedMixingRows G (rademacherSignVector ω)) U
  let Epre : Set (RademacherTrace m) :=
    {ω | ∀ i : Fin r, rowNormSq (M ω) i ≤ (n : ℝ) * B ^ 2}
  let Fsample : RademacherTrace m → Set (RowTrace r s) :=
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
  have hPreBase :
      1 -
          (∑ i : Fin r,
            ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        P.eventProb Epre := by
    simpa [P, M, Epre] using
      rademacherTraceProbability_eventProb_forall_rowNormSq_signedMixingRows_entry_sq_le_uniform_ge_one_sub_sum_sum_two_mul_exp_neg_sq_div
        (G := G) (U := U)
        (α := fun _i : Fin r => alpha) (B := fun _i : Fin r => B)
        (fun _i => halpha) (fun _i => hB)
        (by
          intro i k
          simpa using hGcap i k)
        hU
  have hPre : 1 - δPre ≤ P.eventProb Epre := by
    linarith
  have hrRpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
  let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
  have hLpos : 0 < L := by
    have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero (ne_of_gt hB)
    exact mul_pos hrRpos (mul_pos hnRpos hBsq)
  have hSample : ∀ ω, ω ∈ Epre → 1 - δSample ≤ Q.eventProb (Fsample ω) := by
    intro ω hω
    have hMorth : HasOrthonormalColumns (M ω) := by
      simpa [M] using
        signedMixingRows_preconditionRows_hasOrthonormalColumns
          G U (rademacherSignVector ω) hGorth
          (rademacherSignVector_sq ω) hU
    have hrowBound :
        ∀ i : RowSample r, (r : ℝ) * rowNormSq (M ω) i ≤ L := by
      intro i
      calc
        (r : ℝ) * rowNormSq (M ω) i
            ≤ (r : ℝ) * ((n : ℝ) * B ^ 2) :=
              mul_le_mul_of_nonneg_left (hω i) (le_of_lt hrRpos)
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample r,
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
      simpa [L] using hsampleBudget
    simpa [Q, Fsample] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
        (s := s) (theta := theta) (ε := ε) (δ := δSample) (L := L)
        (M ω) hMorth hr hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - (δPre + δSample) ≤
        (P.prod Q).eventProb
          {x : RademacherTrace m × RowTrace r s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δPre δSample hδSample hPre hSample
  have hsubset :
      {x : RademacherTrace m × RowTrace r s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      signedMixingUniformRowSampleGramTwoSidedEvent G U ε := by
    intro x hx
    exact hx.2
  exact hprod.trans (by
    simpa [signedMixingUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)





















































































































































































/-- Coordinate-Hoeffding signed-Hadamard preprocessing composed with iid
uniform-row matrix concentration.

This is the exact-arithmetic joint-probability composition for the weaker
coordinate-Hoeffding Algorithm 3 route.  The first failure budget controls the
Rademacher preprocessing event.  The second failure budget controls the
conditional iid uniform row-sampling event for each preconditioned matrix on
that event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε δPre δSample : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
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
        (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
  classical
  let P := rademacherTraceProbability m
  let Q := uniformRowTraceProbability (m := m) (steps := s) hm
  let M : RademacherTrace m → Fin m → Fin n → ℝ :=
    fun ω =>
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector ω))) U
  let Epre : Set (RademacherTrace m) :=
    {ω | ∀ i : Fin m, leverageScoreProb (M ω) i ≤ B ^ 2}
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
  have hPre : 1 - δPre ≤ P.eventProb Epre := by
    simpa [P, M, Epre] using
      rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta
        H U hH hflat hU hn (le_of_lt hB) hlam hpreBudget
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hn
  let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
  have hLpos : 0 < L := by
    have hBsq : 0 < B ^ 2 := sq_pos_of_ne_zero (ne_of_gt hB)
    exact mul_pos hmRpos (mul_pos hnRpos hBsq)
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
      have hprob_eq :
          leverageScoreProb (M ω) i =
            rowNormSq (M ω) i / (n : ℝ) := by
        simpa [leverageScore] using
          leverageScoreProb_eq_rowNormSq_div_nat (M ω) hMorth i
      have hrow : rowNormSq (M ω) i ≤ (n : ℝ) * B ^ 2 := by
        have hmul :
            (n : ℝ) * (rowNormSq (M ω) i / (n : ℝ)) ≤
              (n : ℝ) * B ^ 2 :=
          mul_le_mul_of_nonneg_left (by simpa [hprob_eq] using hω i)
            (le_of_lt hnRpos)
        have hcancel :
            (n : ℝ) * (rowNormSq (M ω) i / (n : ℝ)) =
              rowNormSq (M ω) i := by
          field_simp [ne_of_gt hnRpos]
        simpa [hcancel] using hmul
      have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hmRpos
      calc
        (m : ℝ) * rowNormSq (M ω) i
            ≤ (m : ℝ) * ((n : ℝ) * B ^ 2) :=
              mul_le_mul_of_nonneg_left hrow hm_nonneg
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample m,
          finiteLoewnerLe
            (fun j k : Fin n => uniformRowOuterGramSample (M ω) i j k)
            (fun j k : Fin n => L * finiteIdMatrix j k) := by
      intro i
      have hbase :=
        uniformRowOuterGramSample_finiteLoewnerLe_of_leverageScoreProb_le
          (M ω) hMorth hn i (hω i)
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
        (M ω) hMorth hm hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - (δPre + δSample) ≤
        (P.prod Q).eventProb
          {x : RademacherTrace m × RowTrace m s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δPre δSample hδSample hPre hSample
  have hsubset :
      {x : RademacherTrace m × RowTrace m s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      signedHadamardUniformRowSampleGramTwoSidedEvent H U ε := by
    intro x hx
    exact hx.2
  exact hprod.trans (by
    simpa [signedHadamardUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)

/-- Source-sharp signed-Hadamard preprocessing composed with iid uniform-row
matrix concentration.

This variant replaces the older coordinate-Hoeffding preprocessing event by
the locally proved Ledoux/Herbst row-norm flattening bound.  The preprocessing
failure budget is `m * exp(-m t^2 / 8)`, and the conditional uniform-sampling
matrix Chernoff step uses the Loewner radius
`L = m * (sqrt(n / m) + t)^2`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε δPre δSample : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ))
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
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
  classical
  let P := rademacherTraceProbability m
  let Q := uniformRowTraceProbability (m := m) (steps := s) hm
  let M : RademacherTrace m → Fin m → Fin n → ℝ :=
    fun ω =>
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector ω))) U
  let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
  let L : ℝ := (m : ℝ) * S ^ 2
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
  have hPre : 1 - δPre ≤ P.eventProb Epre := by
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
        (P.prod Q).eventProb
          {x : RademacherTrace m × RowTrace m s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δPre δSample hδSample hPre hSample
  have hsubset :
      {x : RademacherTrace m × RowTrace m s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      signedHadamardUniformRowSampleGramTwoSidedEvent H U ε := by
    intro x hx
    exact hx.2
  exact hprod.trans (by
    simpa [signedHadamardUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)

/-- Logarithmic preprocessing-budget version of the source-sharp SRHT plus
iid uniform-row sampling theorem.

This wrapper chooses
`t = sqrt (8 * log (m / δPre) / m)`, so the SRHT preprocessing failure budget
is exactly `δPre`.  The remaining sample-budget hypothesis is the same
trace-MGF condition as in the explicit-`t` theorem, with this logarithmic
radius substituted into `L`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
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
        (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
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
  simpa [t] using
    signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
      H U hH hflat hU hm ht hs htheta hδSample hpreBudget hsampleBudget

end NumStability
