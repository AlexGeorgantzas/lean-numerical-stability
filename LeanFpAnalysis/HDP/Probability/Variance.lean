import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Variance Identities

Finite-dimensional algebraic versions of the variance identities highlighted in
HDP Exercise 0.0.3. Probability-specific uses can instantiate these identities
after proving the corresponding expectation and cross-term hypotheses.
-/

open scoped BigOperators

namespace LeanFpAnalysis.HDP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Product weight on the finite product sample space `Fin k → ι`. If `w` is a
probability mass function on `ι`, then this is the mass function of `k`
independent samples with law `w`. -/
def productWeight {ι : Type*} {k : ℕ} [Fintype ι] (w : ι → ℝ) (ω : Fin k → ι) : ℝ :=
  ∏ j : Fin k, w (ω j)

lemma productWeight_snoc {ι : Type*} [Fintype ι] {k : ℕ}
    (w : ι → ℝ) (ω : Fin k → ι) (i : ι) :
    productWeight w (Fin.snoc ω i) = productWeight w ω * w i := by
  unfold productWeight
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma sum_productWeight {ι : Type*} [Fintype ι] {k : ℕ}
    {w : ι → ℝ} (hw₁ : ∑ i, w i = 1) :
    ∑ ω : Fin k → ι, productWeight w ω = 1 := by
  classical
  have h := Finset.sum_prod_piFinset (R := ℝ) (ι := Fin k)
    (s := (Finset.univ : Finset ι)) (g := fun _ i => w i)
  simpa [productWeight, hw₁] using h

/-- Deterministic orthogonal-sum identity underlying Exercise 0.0.3(a). -/
theorem norm_sum_sq_of_pairwise_inner_zero {k : ℕ} (u : Fin k → E)
    (horth : ∀ i j : Fin k, i ≠ j → inner ℝ (u i) (u j) = 0) :
    ‖∑ j : Fin k, u j‖ ^ 2 = ∑ j : Fin k, ‖u j‖ ^ 2 := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      have hinner : inner ℝ (∑ j : Fin k, u j.castSucc) (u (Fin.last k)) = 0 := by
        rw [sum_inner]
        exact Finset.sum_eq_zero fun j _ => horth j.castSucc (Fin.last k) (by simp)
      have hih :
          ‖∑ j : Fin k, u j.castSucc‖ ^ 2 = ∑ j : Fin k, ‖u j.castSucc‖ ^ 2 := by
        exact ih (fun j : Fin k => u j.castSucc)
          (fun i j hij => horth i.castSucc j.castSucc (by simpa using hij))
      calc
        ‖(∑ j : Fin k, u j.castSucc) + u (Fin.last k)‖ ^ 2
            = ‖∑ j : Fin k, u j.castSucc‖ ^ 2
                + 2 * inner ℝ (∑ j : Fin k, u j.castSucc) (u (Fin.last k))
                + ‖u (Fin.last k)‖ ^ 2 := by
              rw [norm_add_sq_real]
        _ = ∑ j : Fin k, ‖u j.castSucc‖ ^ 2 + ‖u (Fin.last k)‖ ^ 2 := by
              simp [hinner, hih]
        _ = ∑ j : Fin (k + 1), ‖u j‖ ^ 2 := by
              rw [Fin.sum_univ_castSucc]

/-- Finite product-distribution form of HDP Exercise 0.0.3(a). If `u` has
mean zero under weights `w`, then the expected squared norm of the sum of `k`
independent samples is the sum of the expected squared norms. -/
theorem weighted_variance_sum_independent {ι : Type*} [Fintype ι] {k : ℕ}
    {w : ι → ℝ} {u : ι → E}
    (_hw₀ : ∀ i, 0 ≤ w i)
    (hw₁ : ∑ i, w i = 1)
    (hmean : ∑ i, w i • u i = 0) :
    ∑ ω : Fin k → ι,
        productWeight w ω *
          ‖∑ j : Fin k, u (ω j)‖ ^ 2
      =
    ∑ _j : Fin k, ∑ i : ι, w i * ‖u i‖ ^ 2 := by
  classical
  induction k with
  | zero =>
      simp [productWeight]
  | succ k ih =>
      let S : (Fin k → ι) → E := fun ω => ∑ j : Fin k, u (ω j)
      let A : (Fin k → ι) → ℝ := fun ω => productWeight w ω
      let B : ι → ℝ := fun i => w i
      have hsplit :
          (∑ ω : Fin (k + 1) → ι,
              productWeight w ω * ‖∑ j : Fin (k + 1), u (ω j)‖ ^ 2)
            =
          ∑ p : ι × (Fin k → ι),
              A p.2 * B p.1 * ‖S p.2 + u p.1‖ ^ 2 := by
        let e := Fin.snocEquiv (fun _ : Fin (k + 1) => ι)
        calc
          (∑ ω : Fin (k + 1) → ι,
              productWeight w ω * ‖∑ j : Fin (k + 1), u (ω j)‖ ^ 2)
              = ∑ p : ι × (Fin k → ι),
                  productWeight w (e p) * ‖∑ j : Fin (k + 1), u (e p j)‖ ^ 2 := by
                exact (Fintype.sum_equiv e
                  (fun p : ι × (Fin k → ι) =>
                    productWeight w (e p) * ‖∑ j : Fin (k + 1), u (e p j)‖ ^ 2)
                  (fun ω : Fin (k + 1) → ι =>
                    productWeight w ω * ‖∑ j : Fin (k + 1), u (ω j)‖ ^ 2)
                  (fun p => rfl)).symm
          _ = ∑ p : ι × (Fin k → ι),
                  A p.2 * B p.1 * ‖S p.2 + u p.1‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                rintro ⟨i, ω⟩ _
                have hsum :
                    (∑ j : Fin (k + 1), u (e (i, ω) j)) = S ω + u i := by
                  rw [Fin.sum_univ_castSucc]
                  simp [e, S, Fin.snoc_castSucc, Fin.snoc_last]
                have hweight : productWeight w (e (i, ω)) = A ω * B i := by
                  change productWeight w (Fin.snoc ω i) = productWeight w ω * w i
                  exact productWeight_snoc w ω i
                rw [hweight, hsum]
      have hA_sum : ∑ ω : Fin k → ι, A ω = 1 := by
        simpa [A] using (sum_productWeight (k := k) (w := w) hw₁)
      have hcross :
          ∑ i : ι, ∑ ω : Fin k → ι,
              A ω * B i * inner ℝ (S ω) (u i) = 0 := by
        calc
          ∑ i : ι, ∑ ω : Fin k → ι,
              A ω * B i * inner ℝ (S ω) (u i)
              = inner ℝ (∑ ω : Fin k → ι, A ω • S ω) (∑ i : ι, B i • u i) := by
                simp [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
                  A, B, mul_comm, mul_assoc]
          _ = 0 := by simp [B, hmean]
      have hmain :
          (∑ p : ι × (Fin k → ι),
              A p.2 * B p.1 * ‖S p.2 + u p.1‖ ^ 2)
            =
          (∑ ω : Fin k → ι, A ω * ‖S ω‖ ^ 2)
            + (∑ i : ι, B i * ‖u i‖ ^ 2) := by
        rw [Fintype.sum_prod_type]
        simp_rw [norm_add_sq_real, mul_add, Finset.sum_add_distrib]
        have hfirst :
            ∑ i : ι, ∑ ω : Fin k → ι, A ω * B i * ‖S ω‖ ^ 2 =
              ∑ ω : Fin k → ι, A ω * ‖S ω‖ ^ 2 := by
          calc
            ∑ i : ι, ∑ ω : Fin k → ι, A ω * B i * ‖S ω‖ ^ 2
                = ∑ ω : Fin k → ι, ∑ i : ι, A ω * B i * ‖S ω‖ ^ 2 := by
                  rw [Finset.sum_comm]
            _ = ∑ ω : Fin k → ι, A ω * ‖S ω‖ ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  calc
                    ∑ i : ι, A ω * B i * ‖S ω‖ ^ 2
                        = ∑ i : ι, B i * (A ω * ‖S ω‖ ^ 2) := by
                          refine Finset.sum_congr rfl ?_
                          intro i _
                          ring
                    _ = (∑ i : ι, B i) * (A ω * ‖S ω‖ ^ 2) := by
                          rw [Finset.sum_mul]
                    _ = A ω * ‖S ω‖ ^ 2 := by
                          simp [B, hw₁]
        have hthird :
            ∑ i : ι, ∑ ω : Fin k → ι, A ω * B i * ‖u i‖ ^ 2 =
              ∑ i : ι, B i * ‖u i‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          calc
            ∑ ω : Fin k → ι, A ω * B i * ‖u i‖ ^ 2
                = ∑ ω : Fin k → ι, A ω * (B i * ‖u i‖ ^ 2) := by
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  ring
            _ = (∑ ω : Fin k → ι, A ω) * (B i * ‖u i‖ ^ 2) := by
                  rw [Finset.sum_mul]
            _ = B i * ‖u i‖ ^ 2 := by
                  simp [hA_sum]
        have hsecond :
            ∑ i : ι, ∑ ω : Fin k → ι, A ω * B i * (2 * inner ℝ (S ω) (u i)) = 0 := by
          calc
            ∑ i : ι, ∑ ω : Fin k → ι, A ω * B i * (2 * inner ℝ (S ω) (u i))
                = 2 * (∑ i : ι, ∑ ω : Fin k → ι,
                    A ω * B i * inner ℝ (S ω) (u i)) := by
                  rw [Finset.mul_sum]
                  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
            _ = 0 := by simp [hcross]
        rw [hfirst, hsecond, hthird]
        ring
      calc
        ∑ ω : Fin (k + 1) → ι,
            productWeight w ω * ‖∑ j : Fin (k + 1), u (ω j)‖ ^ 2
            = (∑ ω : Fin k → ι, A ω * ‖S ω‖ ^ 2)
                + (∑ i : ι, B i * ‖u i‖ ^ 2) := hsplit.trans hmain
        _ = (∑ _j : Fin k, ∑ i : ι, w i * ‖u i‖ ^ 2)
                + (∑ i : ι, w i * ‖u i‖ ^ 2) := by
              simp only [A, S, B]
              rw [ih]
        _ = ∑ j : Fin (k + 1), ∑ i : ι, w i * ‖u i‖ ^ 2 := by
              rw [Fin.sum_univ_castSucc]

/-- Weighted finite-distribution form of `E‖Z - EZ‖² = E‖Z‖² - ‖EZ‖²`,
the identity used in Exercise 0.0.3(b). -/
theorem weighted_variance_identity {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → E)
    (hw₁ : ∑ i, w i = 1) :
    (∑ i, w i * ‖z i - (∑ j, w j • z j)‖ ^ 2)
      = (∑ i, w i * ‖z i‖ ^ 2) - ‖∑ i, w i • z i‖ ^ 2 := by
  classical
  let μ : E := ∑ j, w j • z j
  have hinner_sum : ∑ i, w i * inner ℝ (z i) μ = inner ℝ μ μ := by
    calc
      ∑ i, w i * inner ℝ (z i) μ
          = inner ℝ (∑ i, w i • z i) μ := by
              simp [sum_inner, real_inner_smul_left]
      _ = inner ℝ μ μ := by simp [μ]
  have hconst : ∑ i, w i * ‖μ‖ ^ 2 = ‖μ‖ ^ 2 * ∑ i, w i := by
    rw [← Finset.sum_mul]
    ring
  calc
    ∑ i, w i * ‖z i - (∑ j, w j • z j)‖ ^ 2
        = ∑ i, w i * (‖z i‖ ^ 2 - 2 * inner ℝ (z i) μ + ‖μ‖ ^ 2) := by
          simp [μ, norm_sub_sq_real]
    _ = (∑ i, w i * ‖z i‖ ^ 2)
          - 2 * (∑ i, w i * inner ℝ (z i) μ)
          + (∑ i, w i) * ‖μ‖ ^ 2 := by
          simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]
          rw [hconst]
          ring_nf
    _ = (∑ i, w i * ‖z i‖ ^ 2) - ‖μ‖ ^ 2 := by
          rw [hinner_sum, hw₁]
          rw [← real_inner_self_eq_norm_sq]
          ring
    _ = (∑ i, w i * ‖z i‖ ^ 2) - ‖∑ i, w i • z i‖ ^ 2 := by
          simp [μ]

end LeanFpAnalysis.HDP
