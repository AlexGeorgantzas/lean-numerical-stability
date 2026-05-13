import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def stationaryLocalError (n : ℕ)
    (M N : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, M i j * xhat (k + 1) j -
    (∑ j : Fin n, N i j * xhat k j + b i)

theorem templates_stationary_iteration_residual_bound
    (n : ℕ) (hn : 0 < n)
    (A M N M_inv : Fin n → Fin n → ℝ) (b x : Fin n → ℝ)
    (xhat : ℕ → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1)
    (hH : infNorm hn (dualIterMatrix n N M_inv) ≤ q)
    (mu : ℝ) (hmu_nonneg : 0 ≤ mu)
    (hlocal :
      ∀ k, infNormVec hn (stationaryLocalError n M N b xhat k) ≤ mu) :
    ∀ m : ℕ,
      infNormVec hn (fun i => b i - ∑ j : Fin n, A i j * xhat (m + 1) j) ≤
        q ^ (m + 1) *
            infNormVec hn (fun i => b i - ∑ j : Fin n, A i j * xhat 0 j) +
          mu * infNorm hn (matSub_id n (dualIterMatrix n N M_inv)) / (1 - q) := by
  let r : ℕ → Fin n → ℝ := fun k i => b i - ∑ j : Fin n, A i j * xhat k j
  let ξ : ℕ → Fin n → ℝ := fun k => stationaryLocalError n M N b xhat k
  let H : Fin n → Fin n → ℝ := dualIterMatrix n N M_inv
  let K : Fin n → Fin n → ℝ := matSub_id n H
  have abs_sum_le_sum_abs_local :
      ∀ {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℝ),
        |∑ x ∈ s, f x| ≤ ∑ x ∈ s, |f x| := by
    intro α _ s f
    induction s using Finset.induction_on with
    | empty =>
        simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact (abs_add_le (f a) (∑ x ∈ s, f x)).trans
          (add_le_add (le_refl _) ih)
  have vec_entry_le_norm :
      ∀ (v : Fin n → ℝ) (i : Fin n), |v i| ≤ infNormVec hn v := by
    intro v i
    unfold infNormVec
    exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i)
  have vec_norm_nonneg : ∀ (v : Fin n → ℝ), 0 ≤ infNormVec hn v := by
    intro v
    exact le_trans (abs_nonneg (v ⟨0, hn⟩)) (vec_entry_le_norm v ⟨0, hn⟩)
  have mat_row_le_norm :
      ∀ (B : Fin n → Fin n → ℝ) (i : Fin n),
        (∑ j : Fin n, |B i j|) ≤ infNorm hn B := by
    intro B i
    unfold infNorm
    exact Finset.le_sup' (fun i => ∑ j : Fin n, |B i j|) (Finset.mem_univ i)
  have mat_norm_nonneg : ∀ (B : Fin n → Fin n → ℝ), 0 ≤ infNorm hn B := by
    intro B
    have hrow : 0 ≤ ∑ j : Fin n, |B ⟨0, hn⟩ j| := by
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (B ⟨0, hn⟩ j))
    exact le_trans hrow (mat_row_le_norm B ⟨0, hn⟩)
  have matVec_bound :
      ∀ (B : Fin n → Fin n → ℝ) (v : Fin n → ℝ),
        infNormVec hn (fun i => ∑ j : Fin n, B i j * v j) ≤
          infNorm hn B * infNormVec hn v := by
    intro B v
    apply (Finset.sup'_le_iff (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) _).mpr
    intro i hi
    have htri : |∑ j : Fin n, B i j * v j| ≤ ∑ j : Fin n, |B i j * v j| := by
      simpa using
        abs_sum_le_sum_abs_local (Finset.univ : Finset (Fin n))
          (fun j => B i j * v j)
    have hterm : (∑ j : Fin n, |B i j * v j|) ≤
        ∑ j : Fin n, |B i j| * infNormVec hn v := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (vec_entry_le_norm v j) (abs_nonneg (B i j))
    have hrow : (∑ j : Fin n, |B i j| * infNormVec hn v) ≤
        infNorm hn B * infNormVec hn v := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (mat_row_le_norm B i) (vec_norm_nonneg v)
    exact htri.trans (hterm.trans hrow)
  have vec_sub_bound :
      ∀ (v w : Fin n → ℝ),
        infNormVec hn (fun i => v i - w i) ≤ infNormVec hn v + infNormVec hn w := by
    intro v w
    apply (Finset.sup'_le_iff (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) _).mpr
    intro i hi
    have htri : |v i - w i| ≤ |v i| + |w i| := by
      simpa [sub_eq_add_neg] using abs_add_le (v i) (-w i)
    exact htri.trans (add_le_add (vec_entry_le_norm v i) (vec_entry_le_norm w i))
  have id_sum : ∀ (i : Fin n) (v : Fin n → ℝ),
      (∑ j : Fin n, (if i = j then 1 else 0) * v j) = v i := by
    intro i v
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      by_cases h : i = j
      · exact (hji h.symm).elim
      · simp [h]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hrex : ∀ k l, r k l + ξ k l =
      ∑ j : Fin n, M l j * (xhat (k + 1) j - xhat k j) := by
    intro k l
    dsimp [r, ξ, stationaryLocalError]
    simp_rw [hS.splitting]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring_nf
  have hxdiff : ∀ k i, xhat (k + 1) i - xhat k i =
      ∑ l : Fin n, M_inv i l * (r k l + ξ k l) := by
    intro k i
    symm
    calc
      (∑ l : Fin n, M_inv i l * (r k l + ξ k l))
          = ∑ l : Fin n, M_inv i l *
              (∑ j : Fin n, M l j * (xhat (k + 1) j - xhat k j)) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hrex]
      _ = ∑ j : Fin n, (∑ l : Fin n, M_inv i l * M l j) *
              (xhat (k + 1) j - xhat k j) := by
              calc
                (∑ l : Fin n, M_inv i l *
                    (∑ j : Fin n, M l j * (xhat (k + 1) j - xhat k j)))
                    = ∑ l : Fin n, ∑ j : Fin n,
                        M_inv i l * (M l j * (xhat (k + 1) j - xhat k j)) := by
                        apply Finset.sum_congr rfl
                        intro l hl
                        rw [Finset.mul_sum]
                _ = ∑ j : Fin n, ∑ l : Fin n,
                        M_inv i l * (M l j * (xhat (k + 1) j - xhat k j)) := by
                        rw [Finset.sum_comm]
                _ = ∑ j : Fin n, (∑ l : Fin n, M_inv i l * M l j) *
                        (xhat (k + 1) j - xhat k j) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_mul]
                        apply Finset.sum_congr rfl
                        intro l hl
                        ring
      _ = ∑ j : Fin n, (if i = j then 1 else 0) *
              (xhat (k + 1) j - xhat k j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hS.inv_left i j]
      _ = xhat (k + 1) i - xhat k i :=
              id_sum i (fun j => xhat (k + 1) j - xhat k j)
  have hres_next_diff : ∀ k i, r (k + 1) i =
      (∑ l : Fin n, N i l * (xhat (k + 1) l - xhat k l)) - ξ k i := by
    intro k i
    dsimp [r, ξ, stationaryLocalError]
    simp_rw [hS.splitting]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    abel
  have hrec_eq : ∀ k i, r (k + 1) i =
      (∑ j : Fin n, H i j * r k j) - ∑ j : Fin n, K i j * ξ k j := by
    intro k i
    rw [hres_next_diff k i]
    calc
      (∑ l : Fin n, N i l * (xhat (k + 1) l - xhat k l)) - ξ k i
          = (∑ l : Fin n, N i l *
              (∑ j : Fin n, M_inv l j * (r k j + ξ k j))) - ξ k i := by
              apply congrArg (fun z => z - ξ k i)
              apply Finset.sum_congr rfl
              intro l hl
              rw [hxdiff]
      _ = (∑ j : Fin n, H i j * (r k j + ξ k j)) - ξ k i := by
              apply congrArg (fun z => z - ξ k i)
              calc
                (∑ l : Fin n, N i l *
                    (∑ j : Fin n, M_inv l j * (r k j + ξ k j)))
                    = ∑ l : Fin n, ∑ j : Fin n,
                        N i l * (M_inv l j * (r k j + ξ k j)) := by
                        apply Finset.sum_congr rfl
                        intro l hl
                        rw [Finset.mul_sum]
                _ = ∑ j : Fin n, ∑ l : Fin n,
                        N i l * (M_inv l j * (r k j + ξ k j)) := by
                        rw [Finset.sum_comm]
                _ = ∑ j : Fin n, (∑ l : Fin n, N i l * M_inv l j) *
                        (r k j + ξ k j) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_mul]
                        apply Finset.sum_congr rfl
                        intro l hl
                        ring
                _ = ∑ j : Fin n, H i j * (r k j + ξ k j) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        dsimp [H, dualIterMatrix, matMul]
      _ = (∑ j : Fin n, H i j * r k j) - ∑ j : Fin n, K i j * ξ k j := by
              have hK_expand : (∑ j : Fin n, K i j * ξ k j) =
                  ξ k i - ∑ j : Fin n, H i j * ξ k j := by
                dsimp [K, matSub_id, idMatrix]
                simp_rw [sub_mul]
                rw [Finset.sum_sub_distrib]
                rw [id_sum i (ξ k)]
              rw [hK_expand]
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib]
              abel
  have hlocalξ : ∀ k, infNormVec hn (ξ k) ≤ mu := by
    intro k
    simpa [ξ] using hlocal k
  have hH_bound : infNorm hn H ≤ q := by
    simpa [H] using hH
  have hrec_bound : ∀ k, infNormVec hn (r (k + 1)) ≤
      q * infNormVec hn (r k) + mu * infNorm hn K := by
    intro k
    have hfun : r (k + 1) =
        fun i => (∑ j : Fin n, H i j * r k j) - ∑ j : Fin n, K i j * ξ k j := by
      funext i
      exact hrec_eq k i
    calc
      infNormVec hn (r (k + 1))
          = infNormVec hn
              (fun i => (∑ j : Fin n, H i j * r k j) - ∑ j : Fin n, K i j * ξ k j) := by
              rw [hfun]
      _ ≤ infNormVec hn (fun i => ∑ j : Fin n, H i j * r k j) +
            infNormVec hn (fun i => ∑ j : Fin n, K i j * ξ k j) :=
              vec_sub_bound
                (fun i => ∑ j : Fin n, H i j * r k j)
                (fun i => ∑ j : Fin n, K i j * ξ k j)
      _ ≤ infNorm hn H * infNormVec hn (r k) +
            infNorm hn K * infNormVec hn (ξ k) := by
              exact add_le_add (matVec_bound H (r k)) (matVec_bound K (ξ k))
      _ ≤ q * infNormVec hn (r k) + mu * infNorm hn K := by
              have hHpart : infNorm hn H * infNormVec hn (r k) ≤
                  q * infNormVec hn (r k) := by
                exact mul_le_mul_of_nonneg_right hH_bound (vec_norm_nonneg (r k))
              have hKpart : infNorm hn K * infNormVec hn (ξ k) ≤
                  mu * infNorm hn K := by
                calc
                  infNorm hn K * infNormVec hn (ξ k)
                      = infNormVec hn (ξ k) * infNorm hn K := by ring
                  _ ≤ mu * infNorm hn K :=
                      mul_le_mul_of_nonneg_right (hlocalξ k) (mat_norm_nonneg K)
              exact add_le_add hHpart hKpart
  let D : ℝ := mu * infNorm hn K / (1 - q)
  have hden_pos : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (mul_nonneg hmu_nonneg (mat_norm_nonneg K)) (le_of_lt hden_pos)
  have hCeq : mu * infNorm hn K = (1 - q) * D := by
    dsimp [D]
    have hne : 1 - q ≠ 0 := ne_of_gt hden_pos
    field_simp [hne]
  have hbound_all : ∀ t : ℕ,
      infNormVec hn (r t) ≤ q ^ t * infNormVec hn (r 0) + D := by
    intro t
    induction t with
    | zero =>
        have hbase : infNormVec hn (r 0) ≤ infNormVec hn (r 0) + D := by
          linarith
        simpa using hbase
    | succ t ih =>
        have hstep := hrec_bound t
        have hmono : q * infNormVec hn (r t) ≤
            q * (q ^ t * infNormVec hn (r 0) + D) := by
          exact mul_le_mul_of_nonneg_left ih hq_nonneg
        calc
          infNormVec hn (r (t + 1))
              ≤ q * infNormVec hn (r t) + mu * infNorm hn K := hstep
          _ ≤ q * (q ^ t * infNormVec hn (r 0) + D) + mu * infNorm hn K := by
              exact add_le_add hmono (le_refl _)
          _ = q ^ (t + 1) * infNormVec hn (r 0) + D := by
              rw [hCeq, pow_succ]
              ring
  intro m
  simpa [r, H, K, D] using hbound_all (m + 1)

end LeanFpAnalysis.FP
