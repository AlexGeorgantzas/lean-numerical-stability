import NumStability.Algorithms.TestMatrices.Higham28GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreComplexPairs

/-!
# Higham28GinibreComplexPairs (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

open MeasureTheory Polynomial

open scoped ComplexConjugate

local instance ginibreComplexPairsMeasurableSpace (n : ℕ) :
    MeasurableSpace (GinibreRawMatrix n) :=
  MeasurableSpace.pi

private theorem card_partition_by_im (s : Multiset ℂ) :
    s.card =
      (s.filter fun z => z.im = 0).card +
      (s.filter fun z => 0 < z.im).card +
      (s.filter fun z => z.im < 0).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · simp [hneg, hneg.ne, not_lt.mpr hneg.le, ih]
        omega
      · simp [hzero, ih]
        omega
      · simp [hpos, hpos.ne', not_lt.mpr hpos.le, ih]
        omega

private theorem card_filter_im_neg_eq_pos_of_map_conj
    (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) :
    (s.filter fun z => z.im < 0).card =
      (s.filter fun z => 0 < z.im).card := by
  calc
    (s.filter fun z => z.im < 0).card =
        ((s.map (starRingEnd ℂ)).filter fun z => z.im < 0).card := by rw [hs]
    _ = ((s.filter fun z => ((starRingEnd ℂ) z).im < 0).map
        (starRingEnd ℂ)).card := by
      simp only [Multiset.filter_map, Function.comp_apply]
    _ = (s.filter fun z => 0 < z.im).card := by
      simp only [Multiset.card_map, Complex.conj_im, neg_lt_zero]

/-- Every nonreal characteristic root belongs to one conjugate pair.  This
identity counts every root with its algebraic multiplicity. -/
theorem realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount
    (n : ℕ) (A : GinibreRawMatrix n) :
    realEigenvalueCount n A + 2 * complexUpperEigenvalueCount n A = n := by
  let s := (complexMatrixCharpoly A).roots
  have hpart := card_partition_by_im s
  have hconj : s.map (starRingEnd ℂ) = s :=
    roots_complexMatrixCharpoly_map_conj A
  have hupdown := card_filter_im_neg_eq_pos_of_map_conj s hconj
  have hcard : s.card = n := by
    dsimp [s]
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_complexMatrixCharpoly]
  have hreal : (s.filter fun z => z.im = 0).card =
      realEigenvalueCount n A := by
    exact card_filter_im_eq_zero_complexMatrixCharpoly A
  unfold complexUpperEigenvalueCount
  dsimp [s] at hpart hcard hreal hupdown
  omega

theorem complexUpperEigenvalueCount_eq
    (n : ℕ) (A : GinibreRawMatrix n) :
    complexUpperEigenvalueCount n A = (n - realEigenvalueCount n A) / 2 := by
  have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  omega

theorem complexUpperEigenvalueCount_le
    (n : ℕ) (A : GinibreRawMatrix n) :
    complexUpperEigenvalueCount n A ≤ n := by
  have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  omega

/-- The conjugate-pair count is Borel measurable in the matrix entries. -/
theorem measurable_complexUpperEigenvalueCount (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => complexUpperEigenvalueCount n A) := by
  have hfun : (fun A : GinibreRawMatrix n => complexUpperEigenvalueCount n A) =
      fun A => (n - realEigenvalueCount n A) / 2 := by
    funext A
    exact complexUpperEigenvalueCount_eq n A
  rw [hfun]
  exact (measurable_of_countable (fun k : ℕ => (n - k) / 2)).comp
    (measurable_realEigenvalueCount n)

theorem measurable_complexUpperEigenvalueCount_real (n : ℕ) :
    Measurable
      (fun A : GinibreRawMatrix n => (complexUpperEigenvalueCount n A : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_complexUpperEigenvalueCount n)

/-- The number of nonreal conjugate pairs is integrable under the normalized
real Ginibre law. -/
theorem integrable_complexUpperEigenvalueCount (n : ℕ) :
    Integrable
      (fun A : GinibreRawMatrix n => (complexUpperEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine @Integrable.of_bound _ _ _ _ _ this _
    (measurable_complexUpperEigenvalueCount_real n).aestronglyMeasurable n ?_
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast complexUpperEigenvalueCount_le n A

end NumStability

end
