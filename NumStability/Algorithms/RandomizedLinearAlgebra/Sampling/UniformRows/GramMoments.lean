import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRows
import NumStability.Source.Higham.Chapter04.Problem04

/-!
Relocated from the historical wave owners NumStability.Algorithms.RandNLA.UniformRowSampling under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

/-!
## Uniform row-sampling outer products

After Algorithm 3 preconditions a matrix so that its leverage scores are nearly
uniform, the next randomized sketch samples rows uniformly.  This file contains
the exact one-step rank-one facts for that route.

For an orthonormal-column matrix `U`, uniform row sampling uses the one-step
estimator

`m * U_i*^T U_i*`.

Its expectation is `I`, and a row leverage bound
`leverageScoreProb U i <= B^2` gives the Loewner bound
`m n B^2 I`.  These are the deterministic hypotheses needed before proving the
remaining uniform row-sampling concentration inequality.
-/

-- ============================================================
-- One-step uniform row outer products
-- ============================================================













































































































































-- ============================================================
-- Uniform product law and sample averages
-- ============================================================












































































































































/-- Product-law pointwise factorization for two distinct coordinates of an iid
    uniform row trace. -/
private theorem uniformRowTraceProbMass_two_point_factor
    {m steps : ℕ} (t u : Fin steps) (htu : t ≠ u)
    (f g : Fin m → ℝ) (x : RowTrace m steps) :
    (∏ r : Fin steps,
      if r = t then uniformRowProb (x r) * f (x r)
      else if r = u then uniformRowProb (x r) * g (x r)
      else uniformRowProb (x r)) =
    (∏ r : Fin steps, uniformRowProb (x r)) *
      f (x t) * g (x u) := by
  classical
  have hfactor : ∀ r : Fin steps,
      (if r = t then uniformRowProb (x r) * f (x r)
      else if r = u then uniformRowProb (x r) * g (x r)
      else uniformRowProb (x r)) =
      uniformRowProb (x r) *
        (if r = t then f (x r) else if r = u then g (x r) else 1) := by
    intro r
    by_cases hrt : r = t
    · simp [hrt]
    · by_cases hru : r = u
      · simp [hru]
      · simp [hrt, hru]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
    (s := (Finset.univ : Finset (Fin steps))) t
    (fun r : Fin steps =>
      if r = t then f (x r) else if r = u then g (x r) else 1)
    (by intro h; simp at h)
  simp at hprod_t
  have hfac :
      (∏ x_1 : Fin steps,
        if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1) else 1)
      = f (x t) * g (x u) := by
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
          else 1) = g (x u) := by
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then f (x r) else if r = u then g (x r) else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [Finset.sdiff_singleton_eq_erase]
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  rw [hfac]
  ring

/-- Two distinct coordinates of the iid uniform row trace have product
    expectation equal to the product of their one-step expectations. -/
theorem uniformRowTraceProbMass_marginal_two_ne {m steps : ℕ}
    (hm : 0 < m) (t u : Fin steps) (htu : t ≠ u)
    (f g : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      uniformRowTraceProbMass samples *
        (f (samples t) * g (samples u))) =
      (∑ i : Fin m, uniformRowProb i * f i) *
      (∑ i : Fin m, uniformRowProb i * g i) := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun r x =>
        if r = t then uniformRowProb x * f x
        else if r = u then uniformRowProb x * g x
        else uniformRowProb x)
  have hleft :
      (∏ r : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if r = t then uniformRowProb x * f x
          else if r = u then uniformRowProb x * g x
          else uniformRowProb x)) =
      (∑ i : Fin m, uniformRowProb i * f i) *
      (∑ i : Fin m, uniformRowProb i * g i) := by
    simp [uniformRowProb_sum_eq_one hm]
    have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t
      (fun r : Fin steps =>
        if r = t then ∑ i : Fin m, uniformRowProb i * f i
        else if r = u then ∑ i : Fin m, uniformRowProb i * g i
        else 1)
      (by intro h; simp at h)
    simp at hprod_t
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then ∑ i : Fin m, uniformRowProb i * f i
          else if x_1 = u then ∑ i : Fin m, uniformRowProb i * g i
          else 1) =
        ∑ i : Fin m, uniformRowProb i * g i := by
      rw [Finset.sdiff_singleton_eq_erase]
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then ∑ i : Fin m, uniformRowProb i * f i
          else if r = u then ∑ i : Fin m, uniformRowProb i * g i
          else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then ∑ i : Fin m, uniformRowProb i * f i
            else if x_1 = u then ∑ i : Fin m, uniformRowProb i * g i
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ r, (if r = t then uniformRowProb (x r) * f (x r)
          else if r = u then uniformRowProb (x r) * g (x r)
          else uniformRowProb (x r)))
        = ∑ samples : RowTrace m steps,
          uniformRowTraceProbMass samples *
            (f (samples t) * g (samples u)) := by
    simp [uniformRowTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    simpa [mul_assoc] using
      uniformRowTraceProbMass_two_point_factor t u htu f g x
  rw [← hright, ← hprod]
  exact hleft

/-- Under iid uniform row sampling, two distinct trace coordinates collide
    with exact probability `1 / m`. -/
theorem uniformRowTraceProbability_eventProb_pair_collision_eq_inv
    {m steps : ℕ} (hm : 0 < m) (t u : Fin steps) (htu : t ≠ u) :
    (uniformRowTraceProbability (m := m) (steps := steps) hm).eventProb
      {samples | samples t = samples u} = (m : ℝ)⁻¹ := by
  classical
  let P := uniformRowTraceProbability (m := m) (steps := steps) hm
  have hdecomp :
      P.eventProb {samples : RowTrace m steps | samples t = samples u} =
        ∑ q : Fin m,
          P.expectationReal (fun samples =>
            (if samples t = q then 1 else 0) *
              (if samples u = q then 1 else 0)) := by
    unfold P FiniteProbability.eventProb FiniteProbability.expectationReal
      uniformRowTraceProbability
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro samples _
    by_cases hcoll : samples t = samples u
    · simp [hcoll, Finset.sum_ite_eq, Finset.mem_univ]
    · have hzero : ∀ q : Fin m,
        (if samples t = q then (1 : ℝ) else 0) *
          (if samples u = q then (1 : ℝ) else 0) = 0 := by
        intro q
        by_cases htq : samples t = q
        · have huq : samples u ≠ q := by
            intro huq
            exact hcoll (htq.trans huq.symm)
          simp [htq, huq]
        · simp [htq]
      simp [hcoll, hzero]
  have hq : ∀ q : Fin m,
      P.expectationReal (fun samples =>
        (if samples t = q then 1 else 0) *
          (if samples u = q then 1 else 0)) =
        uniformRowProb q * uniformRowProb q := by
    intro q
    have hbase :=
      uniformRowTraceProbMass_marginal_two_ne
        (m := m) (steps := steps) hm t u htu
        (fun i : Fin m => if i = q then (1 : ℝ) else 0)
        (fun i : Fin m => if i = q then (1 : ℝ) else 0)
    have hleft :
        P.expectationReal (fun samples =>
          (if samples t = q then 1 else 0) *
            (if samples u = q then 1 else 0)) =
        ∑ samples : RowTrace m steps,
          uniformRowTraceProbMass samples *
            ((if samples t = q then 1 else 0) *
              (if samples u = q then 1 else 0)) := rfl
    have hright0 :
        (∑ i : Fin m,
          uniformRowProb i * (if i = q then (1 : ℝ) else 0)) =
        uniformRowProb q := by
      simp [Finset.mem_univ]
    rw [hleft, hbase, hright0]
  have hsum_prob :
      (∑ q : Fin m, uniformRowProb q * uniformRowProb q) = (m : ℝ)⁻¹ := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    calc
      (∑ q : Fin m, uniformRowProb q * uniformRowProb q)
          = ∑ _q : Fin m, (m : ℝ)⁻¹ * (m : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro q _
              rfl
      _ = (m : ℝ) * ((m : ℝ)⁻¹ * (m : ℝ)⁻¹) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = (m : ℝ)⁻¹ := by
              field_simp [hmR]
  rw [hdecomp]
  calc
    (∑ q : Fin m,
        P.expectationReal (fun samples =>
          (if samples t = q then 1 else 0) *
            (if samples u = q then 1 else 0)))
        = ∑ q : Fin m, uniformRowProb q * uniformRowProb q := by
            apply Finset.sum_congr rfl
            intro q _
            rw [hq q]
    _ = (m : ℝ)⁻¹ := hsum_prob































































/-- For any scalar quantity attached to a uniformly sampled row, the centered
sum over an iid uniform row trace has second moment equal to `s` times the
one-step centered second moment. -/
theorem uniformRowTraceProbability_expectationReal_centered_sum_sq
    {m s : ℕ} (hm : 0 < m) (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, uniformRowProb i * f i
    (uniformRowTraceProbability (m := m) (steps := s) hm).expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) =
      (s : ℝ) * ∑ i : Fin m, uniformRowProb i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, uniformRowProb i * f i
  let P := uniformRowTraceProbability (m := m) (steps := s) hm
  have hcenter : ∑ i : Fin m, uniformRowProb i * (f i - μ) = 0 := by
    unfold μ
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [uniformRowProb_sum_eq_one hm]
    ring
  have hsame : ∀ t : Fin s,
      P.expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples t) - μ)) =
        ∑ i : Fin m, uniformRowProb i * (f i - μ) ^ 2 := by
    intro t
    unfold P FiniteProbability.expectationReal uniformRowTraceProbability
    calc
      ∑ samples : RowTrace m s,
          uniformRowTraceProbMass samples *
            ((f (samples t) - μ) * (f (samples t) - μ))
          = ∑ i : Fin m, uniformRowProb i *
              ((f i - μ) * (f i - μ)) :=
            uniformRowTraceProbMass_marginal_one hm t
              (fun i => (f i - μ) * (f i - μ))
      _ = ∑ i : Fin m, uniformRowProb i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hdiff : ∀ t u : Fin s, t ≠ u →
      P.expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) = 0 := by
    intro t u htu
    unfold P FiniteProbability.expectationReal uniformRowTraceProbability
    calc
      ∑ samples : RowTrace m s,
          uniformRowTraceProbMass samples *
            ((f (samples t) - μ) * (f (samples u) - μ))
          = (∑ i : Fin m, uniformRowProb i * (f i - μ)) *
            (∑ i : Fin m, uniformRowProb i * (f i - μ)) :=
            uniformRowTraceProbMass_marginal_two_ne hm t u htu
              (fun i => f i - μ) (fun i => f i - μ)
      _ = 0 := by rw [hcenter]; ring
  have hsquare : ∀ samples : RowTrace m s,
      (∑ t : Fin s, (f (samples t) - μ)) ^ 2 =
        ∑ t : Fin s, ∑ u : Fin s,
          (f (samples t) - μ) * (f (samples u) - μ) := by
    intro samples
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  calc
    P.expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2)
        = P.expectationReal
            (fun samples => ∑ t : Fin s, ∑ u : Fin s,
              (f (samples t) - μ) * (f (samples u) - μ)) := by
            congr 1
            ext samples
            exact hsquare samples
    _ = ∑ t : Fin s, ∑ u : Fin s,
          P.expectationReal
            (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) := by
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ t : Fin s, ∑ i : Fin m,
          uniformRowProb i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            calc
              (∑ u : Fin s,
                P.expectationReal
                  (fun samples =>
                    (f (samples t) - μ) * (f (samples u) - μ)))
                  = P.expectationReal
                      (fun samples =>
                        (f (samples t) - μ) * (f (samples t) - μ)) := by
                    apply Finset.sum_eq_single t
                    · intro u _ hut
                      exact hdiff t u hut.symm
                    · intro ht_not
                      exact False.elim (ht_not (Finset.mem_univ t))
              _ = ∑ i : Fin m,
                    uniformRowProb i * (f i - μ) ^ 2 := hsame t
    _ = (s : ℝ) * ∑ i : Fin m,
          uniformRowProb i * (f i - μ) ^ 2 := by
            rw [Finset.sum_const]
            simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Sample-average form of the iid uniform-row variance calculation. -/
theorem uniformRowTraceProbability_expectationReal_sampleAverage_sub_mean_sq
    {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ)) (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, uniformRowProb i * f i
    (uniformRowTraceProbability (m := m) (steps := s) hm).expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, uniformRowProb i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, uniformRowProb i * f i
  let P := uniformRowTraceProbability (m := m) (steps := s) hm
  have hcentered :=
    uniformRowTraceProbability_expectationReal_centered_sum_sq (m := m) (s := s) hm f
  have hpoint : ∀ samples : RowTrace m s,
      (∑ t : Fin s, f (samples t)) / (s : ℝ) - μ =
        (∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ) := by
    intro samples
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hs]
  calc
    P.expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2)
        = P.expectationReal
            (fun samples =>
              ((∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ)) ^ 2) := by
            congr 1
            ext samples
            rw [hpoint samples]
    _ = P.expectationReal
          (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) /
            (s : ℝ) ^ 2 := by
          unfold P FiniteProbability.expectationReal
          simp_rw [div_eq_mul_inv]
          calc
            ∑ samples : RowTrace m s,
                (uniformRowTraceProbability (m := m) (steps := s) hm).prob samples *
                  ((∑ t : Fin s, (f (samples t) - μ)) * (s : ℝ)⁻¹) ^ 2
                = ∑ samples : RowTrace m s,
                    ((uniformRowTraceProbability (m := m) (steps := s) hm).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                      ((s : ℝ) ^ 2)⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro samples _
                    ring
            _ = (∑ samples : RowTrace m s,
                    (uniformRowTraceProbability (m := m) (steps := s) hm).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                    ((s : ℝ) ^ 2)⁻¹ := by
                    rw [Finset.sum_mul]
    _ = ((s : ℝ) * ∑ i : Fin m,
          uniformRowProb i * (f i - μ) ^ 2) / (s : ℝ) ^ 2 := by
          rw [hcentered]
    _ = (1 / (s : ℝ)) *
        ∑ i : Fin m, uniformRowProb i * (f i - μ) ^ 2 := by
          field_simp [ne_of_gt hs]

/-- Coordinate second-moment formula for iid uniform-row Gram sampling around
the exact Gram `UᵀU`. -/
theorem uniformRowTraceProbability_expectationReal_uniformRowSampleGram_entry_error_sq
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (j k : Fin n) :
    (uniformRowTraceProbability (m := m) (steps := s) hm).expectationReal
      (fun samples => (uniformRowSampleGram U samples j k - rowGram U j k) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, uniformRowProb i *
          (uniformRowOuterGramSample U i j k - rowGram U j k) ^ 2 := by
  classical
  have hvar :=
    uniformRowTraceProbability_expectationReal_sampleAverage_sub_mean_sq
      (m := m) (s := s) hm hs
      (fun i => uniformRowOuterGramSample U i j k)
  have hmean := uniform_rowOuterGramSample_mean_eq_rowGram U hm j k
  simpa [uniformRowSampleGram, hmean] using hvar



















































































/-- Squared-Frobenius second-moment bound for iid uniform-row sample Grams:
`E ||Ghat - UᵀU||_F² ≤ (m/s) * sum_i ||U_i||²⁴`. -/
theorem uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (uniformRowTraceProbability (m := m) (steps := s) hm).expectationReal
      (fun samples =>
        frobNormSq (fun j k => uniformRowSampleGram U samples j k - rowGram U j k)) ≤
      ((m : ℝ) / (s : ℝ)) * ∑ i : Fin m, rowNormSq U i ^ 2 := by
  classical
  let P := uniformRowTraceProbability (m := m) (steps := s) hm
  have hcoord := fun j k =>
    uniformRowTraceProbability_expectationReal_uniformRowSampleGram_entry_error_sq
      U hm hs j k
  have hcenter_le : ∀ j k : Fin n,
      ∑ i : Fin m, uniformRowProb i *
          (uniformRowOuterGramSample U i j k - rowGram U j k) ^ 2 ≤
        ∑ i : Fin m, uniformRowProb i *
          uniformRowOuterGramSample U i j k ^ 2 := by
    intro j k
    exact weighted_centered_sq_le_sq
      (fun i : Fin m => uniformRowProb i)
      (fun i : Fin m => uniformRowOuterGramSample U i j k)
      (rowGram U j k)
      (uniformRowProb_sum_eq_one hm)
      (by
        symm
        exact uniform_rowOuterGramSample_mean_eq_rowGram U hm j k)
  calc
    P.expectationReal
      (fun samples =>
        frobNormSq (fun j k => uniformRowSampleGram U samples j k - rowGram U j k))
        =
      ∑ j : Fin n, ∑ k : Fin n,
        P.expectationReal
          (fun samples => (uniformRowSampleGram U samples j k - rowGram U j k) ^ 2) := by
          unfold frobNormSq
          rw [FiniteProbability.expectationReal_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [FiniteProbability.expectationReal_sum]
    _ =
      ∑ j : Fin n, ∑ k : Fin n,
        (1 / (s : ℝ)) *
          ∑ i : Fin m, uniformRowProb i *
            (uniformRowOuterGramSample U i j k - rowGram U j k) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [hcoord j k]
    _ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        (1 / (s : ℝ)) *
          ∑ i : Fin m, uniformRowProb i *
            uniformRowOuterGramSample U i j k ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hcenter_le j k)
            (by positivity)
    _ =
      (1 / (s : ℝ)) *
        (∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
          uniformRowProb i * uniformRowOuterGramSample U i j k ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ =
      ((m : ℝ) / (s : ℝ)) * ∑ i : Fin m, rowNormSq U i ^ 2 := by
          rw [uniformRowOuterGramSample_total_second_moment U hm]
          ring

/-- Readable squared-Frobenius second-moment bound using only `||U||_F`. -/
theorem uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le_frobNorm
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (uniformRowTraceProbability (m := m) (steps := s) hm).expectationReal
      (fun samples =>
        frobNormSq (fun j k => uniformRowSampleGram U samples j k - rowGram U j k)) ≤
      ((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2 := by
  have hbase :=
    uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le
      U hm hs
  have hsum := rowNormSq_sq_sum_le_frobNormSqRect_sq U
  have hfactor_nonneg : 0 ≤ (m : ℝ) / (s : ℝ) :=
    div_nonneg (Nat.cast_nonneg m) (le_of_lt hs)
  exact hbase.trans (mul_le_mul_of_nonneg_left hsum hfactor_nonneg)

/-- High-probability Frobenius/Markov form for iid uniform-row sample Grams. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        {samples |
          frobNorm
            (fun j k => uniformRowSampleGram U samples j k - rowGram U j k) ≤ η} := by
  classical
  let P := uniformRowTraceProbability (m := m) (steps := s) hm
  let Z : RowTrace m s → ℝ := fun samples =>
    frobNorm (fun j k => uniformRowSampleGram U samples j k - rowGram U j k)
  have hZ : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNorm_nonneg _
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z η hZ hη
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        ((m : ℝ) / (s : ℝ)) * ∑ i : Fin m, rowNormSq U i ^ 2 := by
    have h :=
      uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le
        U hm hs
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples =>
              frobNormSq
                (fun j k => uniformRowSampleGram U samples j k - rowGram U j k)) := by
      unfold Z
      congr 1
      ext samples
      exact frobNorm_sq _
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 ≤
        (((m : ℝ) / (s : ℝ)) *
          ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 := by
    exact div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  calc
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples | Z samples ≤ η} := hprob

/-- Readable high-probability uniform-row Frobenius bound using only
`||U||_F`. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        {samples |
          frobNorm
            (fun j k => uniformRowSampleGram U samples j k - rowGram U j k) ≤ η} := by
  classical
  let Bsum : ℝ := ((m : ℝ) / (s : ℝ)) *
    ∑ i : Fin m, rowNormSq U i ^ 2
  let Bfrob : ℝ := ((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2
  have hsum := rowNormSq_sq_sum_le_frobNormSqRect_sq U
  have hfactor_nonneg : 0 ≤ (m : ℝ) / (s : ℝ) :=
    div_nonneg (Nat.cast_nonneg m) (le_of_lt hs)
  have hbudget : Bsum ≤ Bfrob := by
    simpa [Bsum, Bfrob] using
      mul_le_mul_of_nonneg_left hsum hfactor_nonneg
  have hbase :
      1 - Bsum / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          {samples |
            frobNorm
              (fun j k => uniformRowSampleGram U samples j k - rowGram U j k) ≤ η} := by
    simpa [Bsum] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
        U hm hs η hη
  have hleft : 1 - Bfrob / η ^ 2 ≤ 1 - Bsum / η ^ 2 := by
    have hdiv : Bsum / η ^ 2 ≤ Bfrob / η ^ 2 :=
      div_le_div_of_nonneg_right hbudget (sq_nonneg η)
    linarith
  exact hleft.trans hbase

end NumStability
