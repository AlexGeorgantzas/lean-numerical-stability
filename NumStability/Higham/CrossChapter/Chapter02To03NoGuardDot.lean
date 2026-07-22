import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapters 2 -> 3: no-guard-digit dot products

Chapter 3 states that equations (3.3)--(3.5) remain valid under the
no-guard-digit model (2.6).  The two perturbations in a no-guard addition are
tracked separately below.  The concrete left-to-right executor is then shown
to have one multiplicative local factor per input term, with at most `n`
primitive factors in each local factor.
-/

/-- The actual left-to-right dot-product executor using the Chapter 2
no-guard-digit operations. -/
noncomputable def fl_noGuardDotProduct (fp : NoGuardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | m + 1 =>
      Fin.foldl m
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Unrolling a no-guard addition fold exposes the accumulator perturbation
`alpha` and the incoming-operand perturbation `beta` separately. -/
lemma noGuard_add_fold_unroll (fp : NoGuardFPModel) (m : ℕ)
    (a : Fin m → ℝ) (c : ℝ) :
    ∃ (alpha beta : Fin m → ℝ),
      (∀ k, |alpha k| ≤ fp.u) ∧
      (∀ k, |beta k| ≤ fp.u) ∧
      Fin.foldl m (fun acc t => fp.fl_add acc (a t)) c =
        c * ∏ k : Fin m, (1 + alpha k) +
          ∑ t : Fin m, a t * (1 + beta t) *
            ∏ k : Fin m, if t.val < k.val then (1 + alpha k) else 1 := by
  induction m generalizing c with
  | zero =>
      refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · simp
  | succ m ih =>
      obtain ⟨alpha', beta', halpha', hbeta', hfold_m⟩ :=
        ih (fun i => a i.castSucc) c
      have hfold_last :
          Fin.foldl (m + 1) (fun acc t => fp.fl_add acc (a t)) c =
            fp.fl_add
              (Fin.foldl m (fun acc t => fp.fl_add acc (a t.castSucc)) c)
              (a (Fin.last m)) :=
        Fin.foldl_succ_last _ _
      obtain ⟨alphaNew, betaNew, hadd⟩ :=
        fp.model_add
          (Fin.foldl m (fun acc t => fp.fl_add acc (a t.castSucc)) c)
          (a (Fin.last m))
      let alpha : Fin (m + 1) → ℝ := Fin.lastCases alphaNew alpha'
      let beta : Fin (m + 1) → ℝ := Fin.lastCases betaNew beta'
      refine ⟨alpha, beta, ?_, ?_, ?_⟩
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simpa [alpha] using hadd.1
        · intro j; simpa [alpha] using halpha' j
      · intro k
        refine Fin.lastCases ?_ ?_ k
        · simpa [beta] using hadd.2.1
        · intro j; simpa [beta] using hbeta' j
      · rw [hfold_last, noGuardAddWitness_value hadd, hfold_m]
        have hP :
            ∏ k : Fin (m + 1), (1 + alpha k) =
              (∏ k : Fin m, (1 + alpha' k)) * (1 + alphaNew) := by
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp [alpha]
          · simp [alpha]
        have hTP_cast : ∀ t : Fin m,
            ∏ k : Fin (m + 1),
                (if t.castSucc.val < k.val then (1 + alpha k) else 1) =
              (∏ k : Fin m,
                (if t.val < k.val then (1 + alpha' k) else 1)) *
                (1 + alphaNew) := by
          intro t
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro k _
            simp [alpha]
          · simp [alpha, t.isLt]
        have hTP_last :
            ∏ k : Fin (m + 1),
                (if (Fin.last m).val < k.val then (1 + alpha k) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro k _
          have hk : ¬ (Fin.last m).val < k.val :=
            Nat.not_lt.mpr (Nat.le_of_lt_succ k.isLt)
          exact if_neg hk
        rw [hP, Fin.sum_univ_castSucc]
        simp only [beta, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [hTP_last]
        have hsum_cast :
            (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ∏ k : Fin (m + 1),
                    (if t.castSucc.val < k.val then (1 + alpha k) else 1)) =
              ∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ((∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                    (1 + alphaNew)) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [hTP_cast t]
        rw [hsum_cast]
        have hsum_factor :
            (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ((∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                    (1 + alphaNew))) =
              (∑ t : Fin m,
                a t.castSucc * (1 + beta' t) *
                  ∏ k : Fin m,
                    (if t.val < k.val then (1 + alpha' k) else 1)) *
                (1 + alphaNew) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          ring
        rw [hsum_factor]
        ring

/-- The concrete no-guard executor expanded into one local factor per input
term.  The first term carries every accumulator perturbation; every later term
carries its own incoming-operand perturbation and only the later accumulator
perturbations. -/
theorem noGuardDot_factor_expansion_succ (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ) :
    ∃ (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ),
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |alpha i| ≤ fp.u) ∧
      (∀ i, |beta i| ≤ fp.u) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        x 0 * y 0 * (1 + mulDelta 0) *
            (∏ k : Fin m, (1 + alpha k)) +
          ∑ t : Fin m,
            x t.succ * y t.succ * (1 + mulDelta t.succ) *
              (1 + beta t) *
              ∏ k : Fin m,
                if t.val < k.val then (1 + alpha k) else 1 := by
  let z : Fin (m + 1) → ℝ := fun i => fp.fl_mul (x i) (y i)
  have hmul : ∀ i, ∃ d, |d| ≤ fp.u ∧ z i = x i * y i * (1 + d) := by
    intro i
    obtain ⟨d, hd, heq⟩ := fp.model_mul_signedRelErrorWitness (x i) (y i)
    exact ⟨d, hd, heq⟩
  let mulDelta : Fin (m + 1) → ℝ := fun i => Classical.choose (hmul i)
  have hmulBound : ∀ i, |mulDelta i| ≤ fp.u := fun i =>
    (Classical.choose_spec (hmul i)).1
  have hmulEq : ∀ i, z i = x i * y i * (1 + mulDelta i) := fun i =>
    (Classical.choose_spec (hmul i)).2
  obtain ⟨alpha, beta, halpha, hbeta, hfold⟩ :=
    noGuard_add_fold_unroll fp m (fun i => z i.succ) (z 0)
  refine ⟨mulDelta, alpha, beta, hmulBound, halpha, hbeta, ?_⟩
  change Fin.foldl m (fun acc i => fp.fl_add acc (z i.succ)) (z 0) = _
  rw [hfold, hmulEq 0]
  apply congrArg₂ (· + ·)
  · rfl
  · apply Finset.sum_congr rfl
    intro t _
    rw [hmulEq t.succ]

/-- A standard-model proxy used only for the Chapter 3 `gamma` product
calculus.  Its unit roundoff is definitionally the no-guard model's unit
roundoff; none of its arithmetic operations are used by the executor. -/
noncomputable def noGuardDotGammaProxy (fp : NoGuardFPModel) : FPModel :=
  FPModel.exactWithUnitRoundoff fp.u (le_of_lt fp.u_pos)

/-- `gamma_k` for a no-guard dot product. -/
noncomputable abbrev noGuardDotGamma (fp : NoGuardFPModel) (k : ℕ) : ℝ :=
  gamma (noGuardDotGammaProxy fp) k

/-- The standard `k*u < 1` validity condition for the no-guard dot bound. -/
abbrev noGuardDotGammaValid (fp : NoGuardFPModel) (k : ℕ) : Prop :=
  gammaValid (noGuardDotGammaProxy fp) k

namespace SumTree

/-- Evaluate an arbitrary binary summation tree with the Chapter 2 no-guard
addition operation.  Leaves are exact inputs; every internal node is an actual
call to `fp.fl_add`. -/
noncomputable def noGuardEval (fp : NoGuardFPModel) :
    SumTree n → (Fin n → ℝ) → ℝ
  | .leaf, v => v ⟨0, by norm_num⟩
  | .node l r, v =>
      fp.fl_add
        (noGuardEval fp l (fun i => v (Fin.castAdd _ i)))
        (noGuardEval fp r (fun i => v (Fin.natAdd _ i)))

/-- Arbitrary-tree backward error for no-guard summation.  A leaf in the left
subtree receives the top node's `alpha` factor, while a leaf in the right
subtree receives its `beta` factor.  Thus each leaf accumulates one local
factor per node on its path, and the radius is `gamma(depth)`. -/
theorem noGuard_backward_error (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) :
    ∀ (_ : noGuardDotGammaValid fp t.depth) (v : Fin n → ℝ),
      ∃ eta : Fin n → ℝ,
        (∀ i, |eta i| ≤ noGuardDotGamma fp t.depth) ∧
        noGuardEval fp t v = ∑ i : Fin n, v i * (1 + eta i) := by
  induction t with
  | leaf =>
      intro hvalid v
      refine ⟨fun _ => 0, ?_, by simp [noGuardEval]⟩
      intro i
      simp only [abs_zero]
      exact gamma_nonneg (noGuardDotGammaProxy fp) hvalid
  | node l r ihl ihr =>
      rename_i m k
      intro hvalid v
      simp only [depth] at hvalid
      have hldepth : l.depth ≤ max l.depth r.depth + 1 :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
      have hrdepth : r.depth ≤ max l.depth r.depth + 1 :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
      have hvalidL : noGuardDotGammaValid fp l.depth :=
        gammaValid_mono (noGuardDotGammaProxy fp) hldepth hvalid
      have hvalidR : noGuardDotGammaValid fp r.depth :=
        gammaValid_mono (noGuardDotGammaProxy fp) hrdepth hvalid
      have hvalid1 : noGuardDotGammaValid fp 1 :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.succ_le_succ (Nat.zero_le _)) hvalid
      have hvalidL1 : noGuardDotGammaValid fp (l.depth + 1) :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.add_le_add_right (Nat.le_max_left _ _) 1) hvalid
      have hvalidR1 : noGuardDotGammaValid fp (r.depth + 1) :=
        gammaValid_mono (noGuardDotGammaProxy fp)
          (Nat.add_le_add_right (Nat.le_max_right _ _) 1) hvalid
      obtain ⟨etaL, hetaL, hleft⟩ :=
        ihl hvalidL (fun i => v (Fin.castAdd k i))
      obtain ⟨etaR, hetaR, hright⟩ :=
        ihr hvalidR (fun i => v (Fin.natAdd m i))
      obtain ⟨alpha, beta, hadd⟩ :=
        fp.model_add
          (noGuardEval fp l (fun i => v (Fin.castAdd k i)))
          (noGuardEval fp r (fun i => v (Fin.natAdd m i)))
      have halpha1 : |alpha| ≤ noGuardDotGamma fp 1 := by
        exact le_trans hadd.1
          (u_le_gamma (noGuardDotGammaProxy fp) one_pos hvalid1)
      have hbeta1 : |beta| ≤ noGuardDotGamma fp 1 := by
        exact le_trans hadd.2.1
          (u_le_gamma (noGuardDotGammaProxy fp) one_pos hvalid1)
      refine ⟨
        Fin.addCases
          (fun i => etaL i + alpha + etaL i * alpha)
          (fun i => etaR i + beta + etaR i * beta), ?_, ?_⟩
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simp only [Fin.addCases_left]
          obtain ⟨e, he, heq⟩ :=
            gamma_mul (noGuardDotGammaProxy fp) l.depth 1
              (etaL j) alpha (hetaL j) halpha1 hvalidL1
          have heq' : e = etaL j + alpha + etaL j * alpha := by
            have hring :
                (1 + etaL j) * (1 + alpha) =
                  1 + (etaL j + alpha + etaL j * alpha) := by ring
            linarith [heq, hring]
          rw [← heq']
          exact le_trans he
            (gamma_mono (noGuardDotGammaProxy fp)
              (Nat.add_le_add_right (Nat.le_max_left _ _) 1) hvalid)
        · intro j
          simp only [Fin.addCases_right]
          obtain ⟨e, he, heq⟩ :=
            gamma_mul (noGuardDotGammaProxy fp) r.depth 1
              (etaR j) beta (hetaR j) hbeta1 hvalidR1
          have heq' : e = etaR j + beta + etaR j * beta := by
            have hring :
                (1 + etaR j) * (1 + beta) =
                  1 + (etaR j + beta + etaR j * beta) := by ring
            linarith [heq, hring]
          rw [← heq']
          exact le_trans he
            (gamma_mono (noGuardDotGammaProxy fp)
              (Nat.add_le_add_right (Nat.le_max_right _ _) 1) hvalid)
      · show
          fp.fl_add
              (noGuardEval fp l (fun i => v (Fin.castAdd k i)))
              (noGuardEval fp r (fun i => v (Fin.natAdd m i))) =
            ∑ i : Fin (m + k),
              v i *
                (1 + Fin.addCases
                  (fun i => etaL i + alpha + etaL i * alpha)
                  (fun i => etaR i + beta + etaR i * beta) i)
        rw [noGuardAddWitness_value hadd, hleft, hright]
        conv_rhs => rw [Fin.sum_univ_add]
        rw [Finset.sum_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          simp only [Fin.addCases_left]
          ring
        · apply Finset.sum_congr rfl
          intro i _
          simp only [Fin.addCases_right]
          ring

end SumTree

/-- An actual no-guard dot-product evaluation with arbitrary binary tree shape
and arbitrary leaf permutation.  Together, `t` and `perm` represent every
pairwise evaluation order of a nonempty dot product. -/
noncomputable def fl_noGuardDotProductTree (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ) : ℝ :=
  t.noGuardEval fp (fun i => fp.fl_mul (x (perm i)) (y (perm i)))

/-- Tree-depth form of the no-guard dot-product backward error.  The extra one
in `depth + 1` is the rounded multiplication at each leaf. -/
theorem noGuardDotTree_factor_backward_error (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp (t.depth + 1)) :
    ∃ eta : Fin n → ℝ,
      (∀ i, |eta i| ≤ noGuardDotGamma fp (t.depth + 1)) ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, x i * y i * (1 + eta i) := by
  let z : Fin n → ℝ :=
    fun i => fp.fl_mul (x (perm i)) (y (perm i))
  have hdepthValid : noGuardDotGammaValid fp t.depth :=
    gammaValid_mono (noGuardDotGammaProxy fp) (Nat.le_succ t.depth) hvalid
  have hOneValid : noGuardDotGammaValid fp 1 :=
    gammaValid_mono (noGuardDotGammaProxy fp)
      (Nat.succ_le_succ (Nat.zero_le t.depth)) hvalid
  obtain ⟨sumEta, hsumEta, hsum⟩ :=
    SumTree.noGuard_backward_error fp t hdepthValid z
  have hmul : ∀ i : Fin n, ∃ d : ℝ,
      |d| ≤ fp.u ∧
      z i = x (perm i) * y (perm i) * (1 + d) := by
    intro i
    obtain ⟨d, hd, heq⟩ :=
      fp.model_mul_signedRelErrorWitness (x (perm i)) (y (perm i))
    exact ⟨d, hd, heq⟩
  let mulDelta : Fin n → ℝ := fun i => Classical.choose (hmul i)
  have hmulBound : ∀ i, |mulDelta i| ≤ fp.u :=
    fun i => (Classical.choose_spec (hmul i)).1
  have hmulEq : ∀ i,
      z i = x (perm i) * y (perm i) * (1 + mulDelta i) :=
    fun i => (Classical.choose_spec (hmul i)).2
  have hvalidComm :
      noGuardDotGammaValid fp (1 + t.depth) := by
    simpa [Nat.add_comm] using hvalid
  let leafEta : Fin n → ℝ :=
    fun i => mulDelta i + sumEta i + mulDelta i * sumEta i
  have hleafEta : ∀ i,
      |leafEta i| ≤ noGuardDotGamma fp (t.depth + 1) := by
    intro i
    have hmulGamma : |mulDelta i| ≤ noGuardDotGamma fp 1 :=
      le_trans (hmulBound i)
        (u_le_gamma (noGuardDotGammaProxy fp) one_pos hOneValid)
    obtain ⟨e, he, heq⟩ :=
      gamma_mul (noGuardDotGammaProxy fp) 1 t.depth
        (mulDelta i) (sumEta i) hmulGamma (hsumEta i) hvalidComm
    have heq' : e = leafEta i := by
      have hring :
          (1 + mulDelta i) * (1 + sumEta i) = 1 + leafEta i := by
        simp only [leafEta]
        ring
      linarith [heq, hring]
    rw [heq'] at he
    simpa [Nat.add_comm] using he
  have hleafSum :
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n,
          x (perm i) * y (perm i) * (1 + leafEta i) := by
    change SumTree.noGuardEval fp t z = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hmulEq i]
    simp only [leafEta]
    ring
  let eta : Fin n → ℝ := fun i => leafEta (perm.symm i)
  refine ⟨eta, ?_, ?_⟩
  · intro i
    simpa [eta] using hleafEta (perm.symm i)
  · rw [hleafSum]
    exact Fintype.sum_equiv perm
      (fun i : Fin n => x (perm i) * y (perm i) * (1 + leafEta i))
      (fun i : Fin n => x i * y i * (1 + eta i))
      (fun i => by simp [eta])

/-- Equation (3.4), literally for any pairwise evaluation order: every binary
tree shape and every input permutation computes the exact inner product after
a componentwise perturbation of either input bounded by `gamma_n`. -/
theorem higham3_4_noGuard_any_order_backward_error
    (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp n) :
    ∃ deltaX deltaY : Fin n → ℝ,
      (∀ i, |deltaX i| ≤ noGuardDotGamma fp n * |x i|) ∧
      (∀ i, |deltaY i| ≤ noGuardDotGamma fp n * |y i|) ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, (x i + deltaX i) * y i ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, x i * (y i + deltaY i) := by
  have hdepth : t.depth + 1 ≤ n := by
    have hn := SumTree.n_pos t
    have hd := SumTree.depth_le t
    omega
  have hdepthValid : noGuardDotGammaValid fp (t.depth + 1) :=
    gammaValid_mono (noGuardDotGammaProxy fp) hdepth hvalid
  obtain ⟨eta, hetaLocal, hfl⟩ :=
    noGuardDotTree_factor_backward_error fp t perm x y hdepthValid
  have heta : ∀ i, |eta i| ≤ noGuardDotGamma fp n := by
    intro i
    exact le_trans (hetaLocal i)
      (gamma_mono (noGuardDotGammaProxy fp) hdepth hvalid)
  let deltaX : Fin n → ℝ := fun i => x i * eta i
  let deltaY : Fin n → ℝ := fun i => y i * eta i
  refine ⟨deltaX, deltaY, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [deltaX, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (heta i) (abs_nonneg (x i))
  · intro i
    simp only [deltaY, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (heta i) (abs_nonneg (y i))
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaX]
    ring
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaY]
    ring

/-- Equation (3.5) for every no-guard binary-tree/permuted evaluation order. -/
theorem higham3_5_noGuard_any_order_forward_error
    (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp n) :
    |(∑ i : Fin n, x i * y i) -
        fl_noGuardDotProductTree fp t perm x y| ≤
      noGuardDotGamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  obtain ⟨deltaX, _deltaY, hdeltaX, _hdeltaY, hback, _⟩ :=
    higham3_4_noGuard_any_order_backward_error fp t perm x y hvalid
  rw [hback, ← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin n, (x i * y i - (x i + deltaX i) * y i)| ≤
        ∑ i : Fin n, |x i * y i - (x i + deltaX i) * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |deltaX i| * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show x i * y i - (x i + deltaX i) * y i = -deltaX i * y i by ring,
        abs_mul, abs_neg]
    _ ≤ ∑ i : Fin n,
        (noGuardDotGamma fp n * |x i|) * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hdeltaX i) (abs_nonneg _)
    _ = noGuardDotGamma fp n *
        ∑ i : Fin n, |x i| * |y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The multiplicative factor attached to each exact input product in the
no-guard expansion. -/
noncomputable def noGuardDotLocalFactor (m : ℕ)
    (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.cases
    ((1 + mulDelta 0) * ∏ k : Fin m, (1 + alpha k))
    (fun t =>
      (1 + mulDelta t.succ) * (1 + beta t) *
        ∏ k : Fin m, if t.val < k.val then (1 + alpha k) else 1)

/-- Single-sum form of the actual no-guard local-factor expansion. -/
theorem noGuardDot_factor_expansion_sum_succ (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ) :
    ∃ (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ),
      (∀ i, |mulDelta i| ≤ fp.u) ∧
      (∀ i, |alpha i| ≤ fp.u) ∧
      (∀ i, |beta i| ≤ fp.u) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1),
          x i * y i * noGuardDotLocalFactor m mulDelta alpha beta i := by
  obtain ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, hfl⟩ :=
    noGuardDot_factor_expansion_succ fp m x y
  refine ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, ?_⟩
  rw [hfl, Fin.sum_univ_succ]
  simp [noGuardDotLocalFactor]
  ring_nf

/-- Every local factor in an `m+1` term no-guard dot product differs from one
by at most `gamma_(m+1)`.  The incoming `beta` factor replaces, rather than
adds to, the current accumulator factor, exactly as described after (3.5). -/
theorem noGuardDotLocalFactor_abs_sub_one_le (fp : NoGuardFPModel) (m : ℕ)
    (mulDelta : Fin (m + 1) → ℝ) (alpha beta : Fin m → ℝ)
    (hmul : ∀ i, |mulDelta i| ≤ fp.u)
    (halpha : ∀ i, |alpha i| ≤ fp.u)
    (hbeta : ∀ i, |beta i| ≤ fp.u)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    ∀ i, |noGuardDotLocalFactor m mulDelta alpha beta i - 1| ≤
      noGuardDotGamma fp (m + 1) := by
  let gfp := noGuardDotGammaProxy fp
  have hgu : gfp.u = fp.u := rfl
  intro i
  refine Fin.cases ?_ ?_ i
  · let delta : Fin (m + 1) → ℝ := Fin.cases (mulDelta 0) alpha
    have hdelta : ∀ j, |delta j| ≤ gfp.u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [delta, hgu] using hmul 0
      · intro k
        simpa [delta, hgu] using halpha k
    obtain ⟨eta, heta, hprod⟩ := prod_error_bound gfp (m + 1) delta hdelta hvalid
    have hfactor :
        noGuardDotLocalFactor m mulDelta alpha beta 0 = 1 + eta := by
      rw [← hprod, Fin.prod_univ_succ]
      simp [noGuardDotLocalFactor, delta]
    rw [hfactor]
    simpa using heta
  · intro t
    let tail : Fin m → ℝ := fun k =>
      if k.val = 0 then beta t
      else if t.val < k.val then alpha k else 0
    let delta : Fin (m + 1) → ℝ := Fin.cases (mulDelta t.succ) tail
    have htail : ∀ k, |tail k| ≤ fp.u := by
      intro k
      by_cases hk0 : k.val = 0
      · simp only [tail, hk0, if_pos]
        exact hbeta t
      · by_cases htk : t.val < k.val
        · simp only [tail, hk0, if_false, htk, if_pos]
          exact halpha k
        · have hu : 0 ≤ fp.u := le_of_lt fp.u_pos
          simp only [tail, hk0, if_false, htk, abs_zero]
          exact hu
    have hdelta : ∀ j, |delta j| ≤ gfp.u := by
      intro j
      refine Fin.cases ?_ ?_ j
      · simpa [delta, hgu] using hmul t.succ
      · intro k
        simpa [delta, hgu] using htail k
    obtain ⟨eta, heta, hprod⟩ := prod_error_bound gfp (m + 1) delta hdelta hvalid
    have hmpos : 0 < m := Nat.pos_of_ne_zero fun hm0 => by
      subst m
      exact Fin.elim0 t
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    have htailProd :
        (∏ k : Fin (q + 1), (1 + tail k)) =
          (1 + beta t) *
            ∏ k : Fin (q + 1),
              if t.val < k.val then (1 + alpha k) else 1 := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [tail, Fin.val_zero, if_pos, Nat.not_lt_zero, if_false, one_mul]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      by_cases hle : t.val ≤ k.val <;> simp [hle]
    have hfactor :
        noGuardDotLocalFactor (q + 1) mulDelta alpha beta t.succ = 1 + eta := by
      rw [← hprod, Fin.prod_univ_succ]
      simp only [delta, Fin.cases_zero, Fin.cases_succ]
      rw [htailProd]
      simp [noGuardDotLocalFactor]
      ring
    rw [hfactor]
    simpa using heta

/-- Equations (3.3)--(3.4) for the concrete no-guard executor: the computed
dot product is exact after perturbing either input vector componentwise by at
most `gamma_n`. -/
theorem higham3_3_3_4_noGuard_backward_error (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    ∃ deltaX deltaY : Fin (m + 1) → ℝ,
      (∀ i, |deltaX i| ≤ noGuardDotGamma fp (m + 1) * |x i|) ∧
      (∀ i, |deltaY i| ≤ noGuardDotGamma fp (m + 1) * |y i|) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1), (x i + deltaX i) * y i ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1), x i * (y i + deltaY i) := by
  obtain ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, hfl⟩ :=
    noGuardDot_factor_expansion_sum_succ fp m x y
  let factor := noGuardDotLocalFactor m mulDelta alpha beta
  have hfactor : ∀ i, |factor i - 1| ≤ noGuardDotGamma fp (m + 1) :=
    noGuardDotLocalFactor_abs_sub_one_le fp m mulDelta alpha beta
      hmul halpha hbeta hvalid
  let deltaX : Fin (m + 1) → ℝ := fun i => x i * (factor i - 1)
  let deltaY : Fin (m + 1) → ℝ := fun i => y i * (factor i - 1)
  refine ⟨deltaX, deltaY, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [deltaX, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfactor i) (abs_nonneg (x i))
  · intro i
    simp only [deltaY, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfactor i) (abs_nonneg (y i))
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaX, factor]
    ring
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaY, factor]
    ring

/-- Equation (3.5) for the actual no-guard executor. -/
theorem higham3_5_noGuard_forward_error (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    |(∑ i : Fin (m + 1), x i * y i) -
        fl_noGuardDotProduct fp (m + 1) x y| ≤
      noGuardDotGamma fp (m + 1) *
        ∑ i : Fin (m + 1), |x i| * |y i| := by
  obtain ⟨deltaX, _deltaY, hdeltaX, _hdeltaY, hback, _⟩ :=
    higham3_3_3_4_noGuard_backward_error fp m x y hvalid
  rw [hback, ← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin (m + 1),
        (x i * y i - (x i + deltaX i) * y i)| ≤
        ∑ i : Fin (m + 1),
          |x i * y i - (x i + deltaX i) * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (m + 1), |deltaX i| * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show x i * y i - (x i + deltaX i) * y i = -deltaX i * y i by ring,
        abs_mul, abs_neg]
    _ ≤ ∑ i : Fin (m + 1),
        (noGuardDotGamma fp (m + 1) * |x i|) * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hdeltaX i) (abs_nonneg _)
    _ = noGuardDotGamma fp (m + 1) *
        ∑ i : Fin (m + 1), |x i| * |y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end NumStability
