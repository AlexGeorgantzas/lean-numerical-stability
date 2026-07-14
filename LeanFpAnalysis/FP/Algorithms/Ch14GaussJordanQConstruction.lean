-- Algorithms/Ch14GaussJordanQConstruction.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.4 ("Gauss-Jordan Elimination"),
-- equations (14.27)-(14.33) and Theorem 14.5, pp. 274-276.
--
-- PURPOSE.  `Ch14GaussJordanAccumulation.lean` exposed the Theorem-14.5 overall
-- residual (14.31) / forward error (14.32) from the concrete per-step GJE waves,
-- but under a SUPPLIED left inverse `Q` of the cumulative product
-- `P = N̂_{n-1}···N̂_2` (hypothesis `hQP : matMul Q P = I`).
--
-- THIS MODULE DISCHARGES that hypothesis by an explicit CONSTRUCTION.
--
--   (A)  Each GJE stage matrix `N̂ₖ = I − n̂ₖ eₖᵀ` is UNIPOTENT: since
--        `(n̂ₖ)ₖ = 0` (Higham: `eᵀᵢ nₖ = 0` for `i ≥ k`, p. 274), the rank-1
--        term is nilpotent, so `N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ` — an EXACT two-sided
--        inverse (`ch14ext_gjeInvStageMatrix_mul_stage`).
--
--   (B)  `Q := (∏ₖ N̂ₖ)⁻¹` is the reverse-order product of the `N̂ₖ⁻¹`,
--        built by the right-append recursion `ch14ext_gjeInvCumProd`.  The
--        telescoping identity `matMul Q P = I`
--        (`ch14ext_gjeInvCumProd_mul_cumProd`) is proved by induction on the
--        number of stages using only the per-stage inverse identity (A).
--        For the CONCRETE GJE stage family the per-stage identity holds
--        UNCONDITIONALLY (no pivot hypothesis — `(n̂ₖ)ₖ = 0` is definitional),
--        so `hQP` is discharged outright.
--
-- The re-exposed Theorem-14.5 residual/forward-error endpoints
-- (`ch14ext_gjeConstructedQ_overall_residual` / `..._forward_error`) therefore
-- carry NO supplied-`Q` hypothesis: `Q` is the constructed cumulative-product
-- inverse.
--
-- SCALAR AUDIT (Higham's printed leading constants).  §B derives, at the scalar
-- coefficient level, that `gje_c₃ = (n−1)γ₃(1+γ₃)^{n−2}` combined with the GE
-- first-stage `γₙ` budget yields the printed residual constant `8nu`
-- (14.31) and forward constant `2nu` (14.32) at leading order + O(u²).  The
-- entrywise fact `|X_abs| ≥ I` (from `matMul Q P = I`) lets the first-stage
-- object be absorbed into the second-stage object with no loss, so the three
-- accumulation coefficients `(γₙ, c₃, c₃)` collapse onto a single object with
-- combined leading coefficient `≤ 8nu` (documented residual: the accumulation
-- route's sharp constant is `7nu`, one `γₙ` short of Higham's `8nu` because the
-- socket takes the forward substitution `L̂ŷ = b` exact; Higham's 8th `nu` is
-- the Theorem-8.5 `ΔL`).  The forward-error 2-factor `|Û⁻¹||Û|` endpoint is
-- documented as a genuine STRUCTURAL residual of the accumulation-through-`|A⁻¹|`
-- route (see §B).
--
-- Import-only companion; does not modify any upstream file.

import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.GaussJordan
import LeanFpAnalysis.FP.Algorithms.Ch14GaussJordanStep
import LeanFpAnalysis.FP.Algorithms.Ch14GaussJordanAccumulation

namespace LeanFpAnalysis.FP.Ch14Ext

open scoped BigOperators
open LeanFpAnalysis.FP

-- ══════════════════════════════════════════════════════════════════════
-- §A1  The unipotent inverse of a GJE stage matrix:  N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ
-- ══════════════════════════════════════════════════════════════════════

/-- The pivot-row entry of the GJE multiplier vector is zero: `(n̂ₖ)ₖ = 0`.
    This is Higham's `eᵀᵢ nₖ = 0` for `i ≥ k` at `i = k` (p. 274), and is what
    makes the rank-1 term `n̂ₖ eₖᵀ` nilpotent. -/
theorem ch14ext_gjeMultVec_self (n : ℕ) (U : Fin n → Fin n → ℝ) (k : Fin n) :
    ch14ext_gjeMultVec n U k k = 0 := by
  simp [ch14ext_gjeMultVec]

/-- The inverse of the GJE second-stage matrix `N̂ₖ = I − n̂ₖ eₖᵀ`, namely
    `N̂ₖ⁻¹ = I + n̂ₖ eₖᵀ`, built from the SAME multiplier vector
    `n̂ₖ = ch14ext_gjeMultVec n U k`. -/
noncomputable def ch14ext_gjeInvStageMatrix (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i l => (if i = l then (1:ℝ) else 0) +
    (if l = k then ch14ext_gjeMultVec n U k i else 0)

/-- Apply the inverse stage matrix `N̂ₖ⁻¹` to a vector: `(N̂ₖ⁻¹ v)ᵢ = vᵢ + (n̂ₖ)ᵢ vₖ`.
    (Rank-1 analogue of `ch14ext_gjeStageMatrix_apply`, with `+`.) -/
theorem ch14ext_gjeInvStageMatrix_apply (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) (v : Fin n → ℝ) (i : Fin n) :
    ∑ l : Fin n, ch14ext_gjeInvStageMatrix n U k i l * v l
      = v i + ch14ext_gjeMultVec n U k i * v k := by
  unfold ch14ext_gjeInvStageMatrix
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The elementary rank-1 inverse identity (Higham p. 274).**
    `N̂ₖ⁻¹ · N̂ₖ = I`.  The only structural input is `(n̂ₖ)ₖ = 0`
    (`ch14ext_gjeMultVec_self`), which makes `(n̂ₖ eₖᵀ)² = 0`. -/
theorem ch14ext_gjeInvStageMatrix_mul_stage (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) :
    matMul n (ch14ext_gjeInvStageMatrix n U k) (ch14ext_gjeStageMatrix n U k) =
      idMatrix n := by
  funext i j
  show (∑ l : Fin n, ch14ext_gjeInvStageMatrix n U k i l *
      ch14ext_gjeStageMatrix n U k l j) = idMatrix n i j
  rw [ch14ext_gjeInvStageMatrix_apply n U k
    (fun l => ch14ext_gjeStageMatrix n U k l j) i]
  -- `(N̂ₖ⁻¹ · N̂ₖ)_{ij} = (N̂ₖ)_{ij} + (n̂ₖ)ᵢ (N̂ₖ)_{kj}`
  have hkj : ch14ext_gjeStageMatrix n U k k j = (if k = j then (1:ℝ) else 0) := by
    simp [ch14ext_gjeStageMatrix, ch14ext_gjeMultVec_self n U k]
  have hij : ch14ext_gjeStageMatrix n U k i j =
      (if i = j then (1:ℝ) else 0) -
        (if j = k then ch14ext_gjeMultVec n U k i else 0) := rfl
  rw [hkj, hij, idMatrix]
  by_cases h : j = k
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun hh : k = j => h hh.symm)]; ring

-- ══════════════════════════════════════════════════════════════════════
-- §A2  The reverse-order product Q = (∏ N̂)⁻¹ of the inverse stages
-- ══════════════════════════════════════════════════════════════════════

/-- **Reverse-order cumulative product of the inverse stage matrices.**
    Mirrors `gje_cumulative_product` but appends each new inverse stage on the
    RIGHT, so that `Q · P` telescopes:
      `ch14ext_gjeInvCumProd start finish = N̂_start⁻¹ ··· N̂_{finish-1}⁻¹`.
    (`P = gje_cumulative_product = N̂_{finish-1} ··· N̂_start`.) -/
noncomputable def ch14ext_gjeInvCumProd (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) (start finish_ : ℕ) : Fin n → Fin n → ℝ :=
  if finish_ ≤ start then idMatrix n
  else if h : finish_ - 1 < n then
    matMul n (ch14ext_gjeInvCumProd n Ninv start (finish_ - 1)) (Ninv ⟨finish_ - 1, h⟩)
  else idMatrix n
termination_by finish_ - start

/-- Base case: an empty stage range gives the identity. -/
theorem ch14ext_gjeInvCumProd_base (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hfinish : finish_ ≤ start) :
    ch14ext_gjeInvCumProd n Ninv start finish_ = idMatrix n := by
  conv_lhs => unfold ch14ext_gjeInvCumProd
  simp [hfinish]

/-- Step case: append stage `finish-1`'s inverse on the RIGHT. -/
theorem ch14ext_gjeInvCumProd_step (n : ℕ)
    (Ninv : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : finish_ - 1 < n) :
    ch14ext_gjeInvCumProd n Ninv start finish_ =
      matMul n (ch14ext_gjeInvCumProd n Ninv start (finish_ - 1))
        (Ninv ⟨finish_ - 1, hidx⟩) := by
  conv_lhs => unfold ch14ext_gjeInvCumProd
  simp [not_le_of_gt hstep, hidx]

-- ══════════════════════════════════════════════════════════════════════
-- §A3  Telescoping:  Q · P = I
-- ══════════════════════════════════════════════════════════════════════

/-- **The telescoping left-inverse identity — DERIVED.**
    If each inverse stage is a genuine left inverse of the corresponding stage
    (`matMul (Ninv m) (N̂ m) = I`), then the reverse-order product `Q` is a left
    inverse of the cumulative product `P`:
      `matMul (ch14ext_gjeInvCumProd) (gje_cumulative_product) = I`.
    Proof: induction on the number of stages; the newest inverse cancels the
    newest stage in the middle via associativity. -/
theorem ch14ext_gjeInvCumProd_mul_cumProd (n : ℕ)
    (N_hat Ninv : Fin n → Fin n → Fin n → ℝ) (start : ℕ)
    (hinv : ∀ (m : ℕ) (hm : m < n),
      matMul n (Ninv ⟨m, hm⟩) (N_hat ⟨m, hm⟩) = idMatrix n) :
    ∀ steps : ℕ, (∀ t : ℕ, t < steps → start + t < n) →
      matMul n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
        (gje_cumulative_product n N_hat start (start + steps)) = idMatrix n := by
  intro steps
  induction steps with
  | zero =>
      intro _
      rw [Nat.add_zero,
        ch14ext_gjeInvCumProd_base n Ninv (le_refl start),
        gje_cumulative_product_base n N_hat (le_refl start),
        matMul_id_left]
  | succ steps ih =>
      intro hidx
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfin_eq : start + (steps + 1) - 1 = start + steps := by omega
      have hidxfin : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (steps + 1) - 1, hidxfin⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by apply Fin.ext; simp [hfin_eq]
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n :=
        fun t ht => hidx t (Nat.lt_trans ht hlt)
      have ih' := ih hidx_prev
      -- unfold the two products at the top stage
      have hP : gje_cumulative_product n N_hat start (start + (steps + 1)) =
          matMul n (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxfin, hfin, hfin_eq]
      have hQ : ch14ext_gjeInvCumProd n Ninv start (start + (steps + 1)) =
          matMul n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
            (Ninv ⟨start + steps, htop⟩) := by
        rw [ch14ext_gjeInvCumProd_step n Ninv hstep hidxfin, hfin, hfin_eq]
      rw [hP, hQ]
      rw [matMul_assoc n (ch14ext_gjeInvCumProd n Ninv start (start + steps))
            (Ninv ⟨start + steps, htop⟩)
            (matMul n (N_hat ⟨start + steps, htop⟩)
              (gje_cumulative_product n N_hat start (start + steps)))]
      rw [← matMul_assoc n (Ninv ⟨start + steps, htop⟩)
            (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps))]
      rw [hinv (start + steps) htop, matMul_id_left, ih']

-- ══════════════════════════════════════════════════════════════════════
-- §A4  The concrete inverse stage family and the constructed Q
-- ══════════════════════════════════════════════════════════════════════

/-- The concrete inverse GJE stage family `N̂ₖ⁻¹`, stage `k` reading column `k`
    of the running iterate `V k.val` (mirrors `ch14ext_gjeSeqStages`). -/
noncomputable def ch14ext_gjeSeqStagesInv (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ) :
    Fin n → Fin n → Fin n → ℝ :=
  fun k => ch14ext_gjeInvStageMatrix n (V k.val) k

/-- **The constructed left inverse `Q = (∏ N̂)⁻¹`** for the concrete GJE loop,
    as the reverse-order product of the concrete inverse stages over the `n−1`
    second-stage steps. -/
noncomputable def ch14ext_gjeConstructedQ (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (start : ℕ) : Fin n → Fin n → ℝ :=
  ch14ext_gjeInvCumProd n (ch14ext_gjeSeqStagesInv n V) start (start + (n - 1))

/-- **The per-stage inverse identity for the concrete GJE stages — UNCONDITIONAL.**
    `matMul (N̂ₖ⁻¹) (N̂ₖ) = I` holds for every concrete stage with no pivot
    hypothesis, since `(n̂ₖ)ₖ = 0` is definitional. -/
theorem ch14ext_gjeSeqStagesInv_mul_stages (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (k : Fin n) :
    matMul n (ch14ext_gjeSeqStagesInv n V k) (ch14ext_gjeSeqStages n V k) =
      idMatrix n :=
  ch14ext_gjeInvStageMatrix_mul_stage n (V k.val) k

/-- **hQP DISCHARGED — the constructed `Q` is a genuine left inverse of the
    cumulative product `P` — UNCONDITIONAL.**
    `matMul (ch14ext_gjeConstructedQ) (gje_cumulative_product … ch14ext_gjeSeqStages …)
      = idMatrix`. -/
theorem ch14ext_gjeConstructedQ_isLeftInverse (n : ℕ) (V : ℕ → Fin n → Fin n → ℝ)
    (start : ℕ) (hidx : ∀ t : ℕ, t < n - 1 → start + t < n) :
    matMul n (ch14ext_gjeConstructedQ n V start)
      (gje_cumulative_product n (ch14ext_gjeSeqStages n V) start (start + (n - 1))) =
      idMatrix n :=
  ch14ext_gjeInvCumProd_mul_cumProd n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeSeqStagesInv n V) start
    (fun m hm => ch14ext_gjeSeqStagesInv_mul_stages n V ⟨m, hm⟩) (n - 1) hidx

-- ══════════════════════════════════════════════════════════════════════
-- §A5  Theorem 14.5 (14.31)/(14.32) re-exposed WITHOUT the supplied-Q hyp
-- ══════════════════════════════════════════════════════════════════════

/-- **Theorem 14.5 / eq. (14.31): overall GJE residual, constructed `Q`.**

    Identical to `ch14ext_gjeConcrete_overall_residual` of the accumulation
    module, but the left-inverse hypothesis `hQP` is GONE: `Q` is now the
    explicitly constructed cumulative-product inverse `ch14ext_gjeConstructedQ`,
    and `matMul Q P = I` is discharged by `ch14ext_gjeConstructedQ_isLeftInverse`
    (from the elementary rank-1 stage inverses).  The only remaining structural
    input is Higham's own WLOG normalization `D = I` (`hVfinal`, p. 274). -/
theorem ch14ext_gjeConstructedQ_overall_residual
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |V start k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) k j| *
            |xseq start j|) :=
  ch14ext_gje_overall_residual_of_accumulation n fp A L_hat b x_hat
    (ch14ext_gjeSeqStages n V) V xseq (ch14ext_gjeConstructedQ n V start) start
    hLU hn hnpos h3 hidx hVfinal hxfinal
    (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) hy
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

/-- **Theorem 14.5 / eq. (14.32): overall GJE forward error, constructed `Q`.**

    As `ch14ext_gje_overall_forward_error_of_accumulation`, but with the
    supplied-`Q` hypothesis discharged by the construction. -/
theorem ch14ext_gjeConstructedQ_overall_forward_error
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ) (b x x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |V start l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                  (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
                |V start k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) l k| *
              |xseq start k|)) :=
  ch14ext_gje_overall_forward_error_of_accumulation n fp A A_inv L_hat b x x_hat
    (ch14ext_gjeSeqStages n V) V xseq (ch14ext_gjeConstructedQ n V start) start
    hLU hAinv hn hnpos h3 hidx hVfinal hxfinal
    (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) hy hExact
    (ch14ext_gjeConcrete_hrecM fp n V start h3 hidx hVrec hpiv)
    (ch14ext_gjeConcrete_hrecX fp n V xseq start h3 hidx hxrec hpiv)

-- ══════════════════════════════════════════════════════════════════════
-- §B1  Scalar coefficient audit: the printed leading constants 8nu / 2nu
-- ══════════════════════════════════════════════════════════════════════

/-- The exact `O(u²)` remainder of the GE first-stage constant `γₙ`
    (from `gamma_eq_linear_plus_quadratic_remainder`): `γₙ = nu + this`. -/
noncomputable def ch14ext_gammaRem (fp : FPModel) (n : ℕ) : ℝ :=
  (((n : ℝ) * fp.u) ^ 2) / (1 - (n : ℝ) * fp.u)

/-- `γₙ = nu + ch14ext_gammaRem`, the first-order split of the GE constant. -/
theorem ch14ext_gamma_split (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    gamma fp n = (n : ℝ) * fp.u + ch14ext_gammaRem fp n :=
  gamma_eq_linear_plus_quadratic_remainder fp n hn

/-- The GE first-stage remainder is nonnegative (`nu < 1` ⇒ denominator `> 0`). -/
theorem ch14ext_gammaRem_nonneg (fp : FPModel) (n : ℕ) (hn : gammaValid fp n) :
    0 ≤ ch14ext_gammaRem fp n := by
  unfold ch14ext_gammaRem gammaValid at *
  apply div_nonneg (sq_nonneg _)
  linarith

/-- The `O(u²)` remainder carried by the residual leading constant `8nu`. -/
noncomputable def ch14ext_residualRem (fp : FPModel) (n : ℕ) : ℝ :=
  ch14ext_gammaRem fp n + 2 * gje_c3_quadratic_remainder fp n

/-- **SCALAR AUDIT (14.31): the residual leading constant is `8nu`.**

    The three accumulation coefficients — the GE first-stage `γₙ` (eq. 9.17 /
    `LUBackwardError`) and the two GJE second-stage `c₃ = (n−1)γ₃(1+γ₃)^{n−2}`
    (one for `ΔU`, one for `Δy`) — sum to at most `8nu` at leading order:
        `γₙ + c₃ + c₃  ≤  8·n·u + ch14ext_residualRem`,
    with the remainder `O(u²)` (`= n²u²/(1−nu) + 2·(9(n−1)u²/(1−3u)·(1+γ₃)^{n−2}
    + 3(n−1)u((1+γ₃)^{n−2}−1))`).

    Derivation of the integer `8`: `γₙ = nu + O(u²)` contributes `1`, and each
    `c₃ ≤ 3nu + O(u²)` contributes `3`, for `1 + 3 + 3 = 7 ≤ 8`.  The
    accumulation route's sharp constant is thus `7nu` — one `nu` below Higham's
    printed `8nu`, because the socket takes the forward substitution `L̂ŷ = b`
    exact (`hy`), whereas Higham's proof (14.33) carries a second first-stage
    `γₙ` from the Theorem-8.5 factor `ΔL` (the `L̂ŷ = b` rounding).  `7nu ≤ 8nu`,
    so the printed constant is a valid upper bound. -/
theorem ch14ext_gje_residual_coeff_budget (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) (h3 : gammaValid fp 3) :
    gamma fp n + gje_c₃ fp n + gje_c₃ fp n ≤
      8 * (n : ℝ) * fp.u + ch14ext_residualRem fp n := by
  have hu : 0 ≤ (n : ℝ) * fp.u :=
    mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
  have hg := ch14ext_gamma_split fp n hn
  have hc := gje_c3_le_three_n_u_plus_quadratic_remainder fp n h3
  unfold ch14ext_residualRem
  -- γₙ + 2c₃ = nu + gammaRem + 2c₃ ≤ 7nu + (gammaRem + 2·Qrem) ≤ 8nu + (…)
  nlinarith [hc, hg, hu]

/-- **SCALAR AUDIT (14.32) first term: the forward constant `2nu`.**

    Higham's forward-error proof bounds the first two terms `(x − x₀) +
    (x₀ − Û⁻¹ŷ)` by `γₙ|A⁻¹||L̂||Û||x̂|`; the printed `2nu` prefactor is the
    standard readable cap `γₙ ≤ 2nu` valid whenever `nu ≤ 1/2`.  This is an
    EXACT bound (no `O(u²)` remainder). -/
theorem ch14ext_gje_forward_first_coeff (fp : FPModel) (n : ℕ)
    (hhalf : (n : ℝ) * fp.u ≤ 1 / 2) :
    gamma fp n ≤ 2 * ((n : ℝ) * fp.u) :=
  gamma_le_two_mul_n_u_of_nu_le_half fp n hhalf

/-- **SCALAR AUDIT (14.32) second term: the forward constant `6nu = 3·2nu`.**

    The forward-error term `(x₀ − x̂)`, bounded by (14.29), carries the two GJE
    `c₃` coefficients (from `ΔU`, `Δy`) on the `|Û⁻¹||Û|` object; their sum is at
    most `6nu` at leading order:
        `c₃ + c₃ ≤ 6·n·u + 2·gje_c3_quadratic_remainder`,
    i.e. Higham's `3·2nu` prefactor on `|Û⁻¹||Û|`. -/
theorem ch14ext_gje_forward_second_coeff (fp : FPModel) (n : ℕ)
    (h3 : gammaValid fp 3) :
    gje_c₃ fp n + gje_c₃ fp n ≤
      6 * (n : ℝ) * fp.u + 2 * gje_c3_quadratic_remainder fp n := by
  have hc := gje_c3_le_three_n_u_plus_quadratic_remainder fp n h3
  nlinarith [hc]

-- ══════════════════════════════════════════════════════════════════════
-- §B2  X_abs ≥ I on the diagonal, and the first-stage → second-stage fold
-- ══════════════════════════════════════════════════════════════════════

/-- **Entrywise abs-product domination.**
    `|∏ N̂| ≤ ∏ |N̂|` componentwise: the signed cumulative product is dominated
    by the cumulative product of the absolute-value stages (the `ch14ext_absCumProd`
    envelope).  Proof by induction peeling the top stage. -/
theorem ch14ext_cumProd_abs_dom (n : ℕ) (N_hat : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ) :
    ∀ steps : ℕ, (∀ t : ℕ, t < steps → start + t < n) → ∀ i j : Fin n,
      |gje_cumulative_product n N_hat start (start + steps) i j| ≤
        gje_cumulative_product n (fun k a b => |N_hat k a b|) start
          (start + steps) i j := by
  intro steps
  induction steps with
  | zero =>
      intro _ i j
      rw [Nat.add_zero, gje_cumulative_product_base n N_hat (le_refl start),
        gje_cumulative_product_base n (fun k a b => |N_hat k a b|) (le_refl start)]
      unfold idMatrix
      by_cases h : i = j <;> simp [h]
  | succ steps ih =>
      intro hidx i j
      have hlt : steps < steps + 1 := Nat.lt_succ_self steps
      have htop : start + steps < n := hidx steps hlt
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfin_eq : start + (steps + 1) - 1 = start + steps := by omega
      have hidxfin : start + (steps + 1) - 1 < n := by rw [hfin_eq]; exact htop
      have hfin : (⟨start + (steps + 1) - 1, hidxfin⟩ : Fin n) =
          ⟨start + steps, htop⟩ := by apply Fin.ext; simp [hfin_eq]
      have ih' := ih (fun t ht => hidx t (Nat.lt_trans ht hlt))
      have hPs : gje_cumulative_product n N_hat start (start + (steps + 1)) =
          matMul n (N_hat ⟨start + steps, htop⟩)
            (gje_cumulative_product n N_hat start (start + steps)) := by
        rw [gje_cumulative_product_step n N_hat hstep hidxfin, hfin, hfin_eq]
      have hPa : gje_cumulative_product n (fun k a b => |N_hat k a b|) start
            (start + (steps + 1)) =
          matMul n (fun a b => |N_hat ⟨start + steps, htop⟩ a b|)
            (gje_cumulative_product n (fun k a b => |N_hat k a b|) start
              (start + steps)) := by
        rw [gje_cumulative_product_step n (fun k a b => |N_hat k a b|) hstep hidxfin,
          hfin, hfin_eq]
      rw [hPs, hPa]
      show |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l *
          gje_cumulative_product n N_hat start (start + steps) l j| ≤
        ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
          gje_cumulative_product n (fun k a b => |N_hat k a b|) start
            (start + steps) l j
      calc |∑ l : Fin n, N_hat ⟨start + steps, htop⟩ i l *
              gje_cumulative_product n N_hat start (start + steps) l j|
          ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l *
              gje_cumulative_product n N_hat start (start + steps) l j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              |gje_cumulative_product n N_hat start (start + steps) l j| :=
            Finset.sum_congr rfl (fun l _ => abs_mul _ _)
        _ ≤ ∑ l : Fin n, |N_hat ⟨start + steps, htop⟩ i l| *
              gje_cumulative_product n (fun k a b => |N_hat k a b|) start
                (start + steps) l j :=
            Finset.sum_le_sum
              (fun l _ => mul_le_mul_of_nonneg_left (ih' l j) (abs_nonneg _))

/-- **The constructed `Q` forces `X_abs ≥ I` on the diagonal.**
    Since `matMul Q P = I` and `|P| ≤ ch14ext_absCumProd`, the middle envelope
    `X_abs = |Q|·ch14ext_absCumProd` has every diagonal entry `≥ 1`:
        `1 = |(QP)ₖₖ| ≤ ∑ₗ |Qₖₗ||Pₗₖ| ≤ ∑ₗ |Qₖₗ| absCumProdₗₖ = (X_abs)ₖₖ`.
    This is the componentwise `|Û⁻¹||Û| ≥ I` of Higham's middle factor, made
    exact by the construction. -/
theorem ch14ext_gjeXabs_diag_ge_one (n : ℕ) (N_hat : Fin n → Fin n → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ) (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hQP : matMul n Q (gje_cumulative_product n N_hat start (start + steps)) =
      idMatrix n)
    (k : Fin n) :
    1 ≤ ch14ext_gjeXabs n N_hat Q start steps k k := by
  have hQPkk : matMul n Q (gje_cumulative_product n N_hat start (start + steps)) k k
      = 1 := by rw [hQP]; simp [idMatrix]
  calc (1 : ℝ)
      = |matMul n Q (gje_cumulative_product n N_hat start (start + steps)) k k| := by
        rw [hQPkk]; norm_num
    _ = |∑ l : Fin n, Q k l *
          gje_cumulative_product n N_hat start (start + steps) l k| := rfl
    _ ≤ ∑ l : Fin n, |Q k l *
          gje_cumulative_product n N_hat start (start + steps) l k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l : Fin n, |Q k l| *
          |gje_cumulative_product n N_hat start (start + steps) l k| :=
        Finset.sum_congr rfl (fun l _ => abs_mul _ _)
    _ ≤ ∑ l : Fin n, |Q k l| *
          ch14ext_absCumProd n N_hat start steps l k :=
        Finset.sum_le_sum (fun l _ =>
          mul_le_mul_of_nonneg_left
            (ch14ext_cumProd_abs_dom n N_hat start steps hidx l k) (abs_nonneg _))
    _ = ch14ext_gjeXabs n N_hat Q start steps k k := by
        unfold ch14ext_gjeXabs absMatrix matMul; rfl

/-- **First-stage object absorbed into the second-stage object.**
    Because `X_abs ≥ I` on the diagonal, the GE first-stage object
    `S1 = |L̂||Û||x̂|` is dominated entrywise by the GJE second-stage object
    `S2 = |L̂||X_abs||Û||x̂|` (insert the `≥1` diagonal `X_abs` factor).  This is
    the step that lets the `γₙ` coefficient share `S2`'s object with the `c₃`
    coefficient, collapsing the printed constant onto a single object. -/
theorem ch14ext_residual_S1_le_S2 (n : ℕ)
    (L_hat V0 Xabs : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (i : Fin n)
    (hdiag : ∀ k : Fin n, 1 ≤ Xabs k k) :
    (∑ j : Fin n, (∑ k : Fin n, |L_hat i k| * |V0 k j|) * |x_hat j|) ≤
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |Xabs k₁ k₂| * |V0 k₂ j|)) * |x_hat j| := by
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply Finset.sum_le_sum; intro k₁ _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h1 : (1 : ℝ) ≤ |Xabs k₁ k₁| := le_trans (hdiag k₁) (le_abs_self _)
  calc |V0 k₁ j|
      ≤ |Xabs k₁ k₁| * |V0 k₁ j| := by nlinarith [abs_nonneg (V0 k₁ j)]
    _ ≤ ∑ k₂ : Fin n, |Xabs k₁ k₂| * |V0 k₂ j| :=
        Finset.single_le_sum (f := fun k₂ => |Xabs k₁ k₂| * |V0 k₂ j|)
          (fun k₂ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ k₁)

/-- **Theorem 14.5 (14.31), folded onto the single second-stage object — DERIVED.**

    Collapsing the GE first-stage object into the GJE second-stage object via
    `ch14ext_residual_S1_le_S2` (justified by the constructed `Q`'s `X_abs ≥ I`
    property), the residual is bounded by ONLY the `S2 = |L̂||X_abs||Û||x̂|` and
    `S3 = |L̂||X_abs||y|` objects, with the first carrying the combined
    coefficient `γₙ + c₃`:
        `|b − A x̂| ≤ (γₙ + c₃)·S2 + c₃·S3`.
    Feeding `ch14ext_gje_residual_coeff_budget` (§B1) then reads the printed
    `8nu` leading constant off `S2` once `S3` is folded into `S2`
    (`ch14ext_gjeConstructedQ_residual_8nu`). -/
theorem ch14ext_gjeConstructedQ_residual_folded
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      (gamma fp n + gje_c₃ fp n) * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) +
      gje_c₃ fp n * (∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1) k j| *
            |xseq start j|)) := by
  intro i
  have hres := ch14ext_gjeConstructedQ_overall_residual n fp A L_hat b x_hat V xseq
    start hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv i
  have hdiag : ∀ k : Fin n,
      1 ≤ ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1) k k :=
    fun k => ch14ext_gjeXabs_diag_ge_one n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) hidx
      (ch14ext_gjeConstructedQ_isLeftInverse n V start hidx) k
  have hS12 := ch14ext_residual_S1_le_S2 n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat i hdiag
  have hmul := mul_le_mul_of_nonneg_left hS12 (gamma_nonneg fp hn)
  nlinarith [hres, hmul]

-- ══════════════════════════════════════════════════════════════════════
-- §B3  Folding the RHS object into the second-stage object;  the 8nu endpoint
-- ══════════════════════════════════════════════════════════════════════

/-- Reordering identity `|L̂||X_abs||Û||x̂| = |L̂||X_abs|(|Û||x̂|)`: the
    second-stage object `S2` equals the `|L̂||X_abs|` map applied to the
    substitution bound `|Û||x̂|` (contracting `Û`'s columns against `x̂`). -/
theorem ch14ext_LXVx_reorder (n : ℕ) (L X V0 : Fin n → Fin n → ℝ) (xh : Fin n → ℝ)
    (i : Fin n) :
    (∑ j : Fin n, (∑ k₁ : Fin n, |L i k₁| *
        (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j|)
      = ∑ k : Fin n, |L i k| *
          (∑ j : Fin n, |X k j| * (∑ l : Fin n, |V0 j l| * |xh l|)) := by
  have e1 : ∀ j : Fin n,
      (∑ k₁ : Fin n, |L i k₁| * (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j|
        = ∑ k₁ : Fin n, |L i k₁| *
            (∑ k₂ : Fin n, |X k₁ k₂| * (|V0 k₂ j| * |xh j|)) := by
    intro j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k₁ _
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro k₂ _; ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k₁ _
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k₂ _
  rw [Finset.mul_sum]

/-- **The RHS object `S3` folds into the second-stage object `S2`** under the
    substitution-sharpness bound `|y| ≤ |Û||x̂|` (Higham's stated sharpness
    condition: `|Û⁻¹||Û||x̂|` is an upper bound for `|x̂|`, exact when the
    stage-2 solve is exact — the `O(u)` correction is the documented residual).
    Then `S3 = |L̂||X_abs||y| ≤ |L̂||X_abs||Û||x̂| = S2`. -/
theorem ch14ext_residual_S3_le_S2 (n : ℕ)
    (L V0 X : Fin n → Fin n → ℝ) (xh y : Fin n → ℝ) (i : Fin n)
    (hySharp : ∀ m : Fin n, |y m| ≤ ∑ l : Fin n, |V0 m l| * |xh l|) :
    (∑ k : Fin n, |L i k| * (∑ j : Fin n, |X k j| * |y j|)) ≤
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L i k₁| *
          (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j| := by
  rw [ch14ext_LXVx_reorder n L X V0 xh i]
  apply Finset.sum_le_sum; intro k _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_left (hySharp j) (abs_nonneg _)

/-- The second-stage object `S2` is nonnegative (a sum of products of `|·|`). -/
theorem ch14ext_S2_nonneg (n : ℕ)
    (L V0 X : Fin n → Fin n → ℝ) (xh : Fin n → ℝ) (i : Fin n) :
    0 ≤ ∑ j : Fin n,
      (∑ k₁ : Fin n, |L i k₁| *
        (∑ k₂ : Fin n, |X k₁ k₂| * |V0 k₂ j|)) * |xh j| := by
  apply Finset.sum_nonneg; intro j _
  apply mul_nonneg _ (abs_nonneg _)
  apply Finset.sum_nonneg; intro k₁ _
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg; intro k₂ _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Scalar folding arithmetic: absorb `c·s₃` into `c·s₂` (via `s₃ ≤ s₂`), merge
    with the `(g+c)·s₂` term, and cap the combined coefficient `g + 2c` by the
    leading budget `eight + rem` on the nonnegative object `s₂`. -/
theorem ch14ext_fold_arith {R g c s2 s3 eight rem : ℝ}
    (hR : R ≤ (g + c) * s2 + c * s3) (hs : s3 ≤ s2)
    (hc : 0 ≤ c) (hs2 : 0 ≤ s2) (hb : g + c + c ≤ eight + rem) :
    R ≤ eight * s2 + rem * s2 := by
  nlinarith [hR, hs, hc, hs2, hb, mul_le_mul_of_nonneg_left hs hc,
    mul_le_mul_of_nonneg_right hb hs2]

/-- **Theorem 14.5 / eq. (14.31): the printed `8nu` residual endpoint, single
    object, constructed `Q` — DERIVED.**

    Combining the folded residual (`ch14ext_gjeConstructedQ_residual_folded`,
    which uses the constructed `Q`'s `X_abs ≥ I` to absorb the GE first-stage
    object) with the `S3 → S2` fold (`ch14ext_residual_S3_le_S2`, under Higham's
    sharpness `|y| ≤ |Û||x̂|`) and the scalar coefficient budget (§B1), the GJE
    residual is bounded by the SINGLE second-stage object `S2 = |L̂||X_abs||Û||x̂|`
    (`X_abs = |Q|·(∏|N̂|)`, the exact form of Higham's `|Û||Û⁻¹|` middle factor)
    with the printed leading constant `8nu`:
        `|b − A x̂| ≤ 8·n·u · S2 + ch14ext_residualRem · S2`,
    the remainder being `O(u²)`.  This is the literal (14.31) endpoint modulo the
    documented `S3→S2` sharpness (`hySharp`) and the `X_abs ≈ |Û||Û⁻¹|` first-order
    identification of the middle factor. -/
theorem ch14ext_gjeConstructedQ_residual_8nu
    (n : ℕ) (fp : FPModel)
    (A L_hat : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (hySharp : ∀ m : Fin n,
      |xseq start m| ≤ ∑ l : Fin n, |V start m l| * |x_hat l|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      8 * (n : ℝ) * fp.u * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) +
      ch14ext_residualRem fp n * (∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
              |V start k₂ j|)) * |x_hat j|) := by
  intro i
  have hfold := ch14ext_gjeConstructedQ_residual_folded n fp A L_hat b x_hat V xseq
    start hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv i
  have hS3 := ch14ext_residual_S3_le_S2 n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat (xseq start) i hySharp
  have hS2nn := ch14ext_S2_nonneg n L_hat (V start)
    (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1)) x_hat i
  exact ch14ext_fold_arith hfold hS3 (gje_c3_nonneg fp n hnpos h3) hS2nn
    (ch14ext_gje_residual_coeff_budget fp n hn h3)

-- ══════════════════════════════════════════════════════════════════════
-- §B4  Forward error (14.32): transfer through |A⁻¹|; the 3-factor endpoint
-- ══════════════════════════════════════════════════════════════════════

/-- **Exact inverse transfer `|x − x̂| ≤ |A⁻¹||b − A x̂|`.**
    From `A⁻¹A = I` and `Ax = b`, any per-row residual bound `bnd` transfers to a
    forward-error bound `|x − x̂|ᵢ ≤ ∑ⱼ |A⁻¹ᵢⱼ| bndⱼ`.  This is the transfer step
    of `gje_overall_forward_error`, isolated for reuse with a folded residual. -/
theorem ch14ext_forward_transfer (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (b x x_hat : Fin n → ℝ) (bnd : Fin n → ℝ)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hres : ∀ j : Fin n, |b j - ∑ k : Fin n, A j k * x_hat k| ≤ bnd j) :
    ∀ i : Fin n, |x i - x_hat i| ≤ ∑ j : Fin n, |A_inv i j| * bnd j := by
  intro i
  have hDiff : x i - x_hat i =
      ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k) := by
    have hRHS_expand : ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k) =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hExact j]; ring
    rw [hRHS_expand]
    have hFirst : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith
  rw [hDiff]
  calc |∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k)|
      ≤ ∑ j : Fin n, |A_inv i j| * |b j - ∑ k : Fin n, A j k * x_hat k| := by
        calc _ ≤ ∑ j : Fin n, |A_inv i j * (b j - ∑ k : Fin n, A j k * x_hat k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| * bnd j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hres j) (abs_nonneg _))

/-- The row-`i` second-stage object `S2ᵢ = (|L̂||X_abs||Û||x̂|)ᵢ`. -/
noncomputable def ch14ext_gjeS2row (n : ℕ) (L_hat : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) (start : ℕ) (i : Fin n) : ℝ :=
  ∑ j : Fin n,
    (∑ k₁ : Fin n, |L_hat i k₁| *
      (∑ k₂ : Fin n,
        |ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
            (ch14ext_gjeConstructedQ n V start) start (n - 1) k₁ k₂| *
          |V start k₂ j|)) * |x_hat j|

/-- **Theorem 14.5 / eq. (14.32): forward error, `8nu` leading constant on the
    accumulation's 3-factor object — DERIVED.**

    Transferring the single-object `8nu` residual (`ch14ext_gjeConstructedQ_residual_8nu`)
    through `|A⁻¹|` (`ch14ext_forward_transfer`) yields
        `|x − x̂| ≤ ∑ⱼ |A⁻¹ᵢⱼ| · (8nu + ch14ext_residualRem)·S2ⱼ`,
    i.e. the forward error is `O(u)` with the printed-order leading constant on
    the object `|A⁻¹||L̂||X_abs||Û||x̂|`.

    STRUCTURAL RESIDUAL (documented).  This is the accumulation's `3-factor`
    object `|A⁻¹||L̂||X_abs||Û|` (with `X_abs ≈ |Û||Û⁻¹|`), NOT the printed
    two-term split `2nu|A⁻¹||L̂||Û||x̂| + 6nu|Û⁻¹||Û||x̂|` of (14.32): the second
    printed term carries NEITHER `|A⁻¹|` NOR `|L̂|`.  Reaching it requires bounding
    the split `(x−x₀)+(x₀−Û⁻¹ŷ)+(Û⁻¹ŷ−x̂)` of Higham's proof — the last term via
    (14.29) applied DIRECTLY to `Ûx = ŷ` — instead of transferring the whole
    residual through `|A⁻¹|`.  The printed constants themselves are audited in
    §B1 (`ch14ext_gje_forward_first_coeff` `= 2nu`,
    `ch14ext_gje_forward_second_coeff` `= 6nu`). -/
theorem ch14ext_gjeConstructedQ_forward_error_8nu
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat : Fin n → Fin n → ℝ) (b x x_hat : Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ) (start : ℕ)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n) (hnpos : 1 ≤ n) (h3 : gammaValid fp 3)
    (hidx : ∀ t : ℕ, t < n - 1 → start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : ∀ i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * xseq start j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hVrec : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t)) ⟨start + t, hidx t ht⟩)
    (hxrec : ∀ t : ℕ, (ht : t < n - 1) →
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t)) ⟨start + t, hidx t ht⟩
          (xseq (start + t)))
    (hpiv : ∀ t : ℕ, (ht : t < n - 1) →
      V (start + t) ⟨start + t, hidx t ht⟩ ⟨start + t, hidx t ht⟩ ≠ 0)
    (hySharp : ∀ m : Fin n,
      |xseq start m| ≤ ∑ l : Fin n, |V start m l| * |x_hat l|) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (8 * (n : ℝ) * fp.u * ch14ext_gjeS2row n L_hat V x_hat start j +
          ch14ext_residualRem fp n * ch14ext_gjeS2row n L_hat V x_hat start j) := by
  have hres8 := ch14ext_gjeConstructedQ_residual_8nu n fp A L_hat b x_hat V xseq start
    hLU hn hnpos h3 hidx hVfinal hxfinal hy hVrec hxrec hpiv hySharp
  exact ch14ext_forward_transfer n A A_inv b x x_hat
    (fun j => 8 * (n : ℝ) * fp.u * ch14ext_gjeS2row n L_hat V x_hat start j +
      ch14ext_residualRem fp n * ch14ext_gjeS2row n L_hat V x_hat start j)
    hAinv hExact hres8

end LeanFpAnalysis.FP.Ch14Ext
