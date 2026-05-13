import LeanFpAnalysis.FP

namespace LeanFpAnalysis.FP

open scoped BigOperators

noncomputable def lapackFerrDenom (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  |fl_residual fp n A x b i| +
    gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x j|)

noncomputable def lapackFerrNumerator (fp : FPModel) (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j : Fin n, |A_inv i j| * lapackFerrDenom fp n A x b j

noncomputable def lapackFerrBound (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) : ℝ :=
  infNormVec hnpos (lapackFerrNumerator fp n A A_inv x b) /
    infNormVec hnpos x

theorem lapack_ferr_forward_error_bound
    (fp : FPModel) (n : ℕ) (hnpos : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1))
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hxhat_norm_pos : 0 < infNormVec hnpos xhat) :
    infNormVec hnpos (fun i => x i - xhat i) /
        infNormVec hnpos xhat ≤
      lapackFerrBound fp n hnpos A A_inv xhat b := by
  have gamma_nonneg : ∀ m : ℕ, gammaValid fp m → 0 ≤ gamma fp m := by
    intro m h
    unfold gamma gammaValid at *
    have hden : 0 < 1 - (m : ℝ) * fp.u := by linarith
    have hnum : 0 ≤ (m : ℝ) * fp.u := by
      exact mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg
    exact div_nonneg hnum hden.le
  have gamma_u_le : ∀ m : ℕ, 0 < m → gammaValid fp m → fp.u ≤ gamma fp m := by
    intro m hm h
    unfold gamma gammaValid at *
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hden : 0 < 1 - (m : ℝ) * fp.u := by linarith
    rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hmreal hu, mul_nonneg (Nat.cast_nonneg m) hu]
  have gamma_step_mul : ∀ m : ℕ, gammaValid fp (m + 1) →
      (1 + fp.u) * (1 + gamma fp m) ≤ 1 + gamma fp (m + 1) := by
    intro m h
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hvalidm : gammaValid fp m := by
      unfold gammaValid at *
      have hle : (m : ℝ) * fp.u ≤ ((m + 1 : ℕ) : ℝ) * fp.u := by
        have hmle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_right hmle hu
      linarith
    have hdenm : 0 < 1 - (m : ℝ) * fp.u := by
      unfold gammaValid at hvalidm
      linarith
    have hdenmp : 0 < 1 - ((m + 1 : ℕ) : ℝ) * fp.u := by
      unfold gammaValid at h
      linarith
    have hone_m : 1 + gamma fp m = 1 / (1 - (m : ℝ) * fp.u) := by
      unfold gamma
      field_simp [hdenm.ne']
      ring
    have hone_mp : 1 + gamma fp (m + 1) =
        1 / (1 - ((m + 1 : ℕ) : ℝ) * fp.u) := by
      unfold gamma
      field_simp [hdenmp.ne']
      ring
    rw [hone_m, hone_mp]
    rw [one_div, one_div]
    rw [mul_comm (1 + fp.u)]
    rw [inv_mul_le_iff₀ hdenm]
    rw [mul_comm (1 - (m : ℝ) * fp.u)]
    rw [le_inv_mul_iff₀ hdenmp]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
    have hcoef : 0 ≤ (((1 + m : ℕ) : ℝ)) := by positivity
    have hsqu : 0 ≤ fp.u ^ 2 := sq_nonneg fp.u
    have hprod : 0 ≤ ((1 + m : ℕ) : ℝ) * fp.u ^ 2 := mul_nonneg hcoef hsqu
    nlinarith
  have gamma_square_le : ∀ m : ℕ, 2 ≤ m → gammaValid fp m →
      (1 + fp.u) * (1 + fp.u) ≤ 1 + gamma fp m := by
    intro m hm h
    unfold gamma gammaValid at *
    have hden : 0 < 1 - (m : ℝ) * fp.u := by linarith
    have hmreal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [show 1 + (m : ℝ) * fp.u / (1 - (m : ℝ) * fp.u) =
        1 / (1 - (m : ℝ) * fp.u) by
      field_simp [hden.ne']
      ring]
    rw [one_div]
    rw [← mul_one ((1 - (m : ℝ) * fp.u)⁻¹)]
    rw [le_inv_mul_iff₀ hden]
    ring_nf
    have h2u : 2 * fp.u ≤ (m : ℝ) * fp.u := by
      exact mul_le_mul_of_nonneg_right hmreal fp.u_nonneg
    have hu2 : 0 ≤ fp.u ^ 2 := sq_nonneg fp.u
    have hcoef2 : (1 : ℝ) ≤ 2 * (m : ℝ) := by nlinarith
    have hu2le : fp.u ^ 2 ≤ (2 * (m : ℝ)) * fp.u ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hcoef2 hu2
    have hu3 : 0 ≤ fp.u ^ 3 := by
      have hpow : fp.u ^ 3 = fp.u ^ 2 * fp.u := by ring
      rw [hpow]
      exact mul_nonneg hu2 fp.u_nonneg
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hm_u3_nonneg : 0 ≤ (m : ℝ) * fp.u ^ 3 := mul_nonneg hm_nonneg hu3
    nlinarith
  have round_add_step : ∀ (c S p t B T gprev gnext δa : ℝ),
      |δa| ≤ fp.u →
      |c - S| ≤ gprev * B →
      |p - t| ≤ fp.u * T →
      |c| ≤ (1 + gprev) * B →
      |p| ≤ (1 + fp.u) * T →
      gprev + fp.u * (1 + gprev) ≤ gnext →
      fp.u + fp.u * (1 + fp.u) ≤ gnext →
      0 ≤ B → 0 ≤ T →
      |(c + p) * (1 + δa) - (S + t)| ≤ gnext * (B + T) := by
    intro c S p t B T gprev gnext δa hδa he hp hc hpabs hcoeff_old hcoeff_new hB hT
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have hδmul : |δa * (c + p)| ≤ fp.u * (|c| + |p|) := by
      calc
        |δa * (c + p)| = |δa| * |c + p| := by rw [abs_mul]
        _ ≤ fp.u * |c + p| := by
          exact mul_le_mul_of_nonneg_right hδa (abs_nonneg _)
        _ ≤ fp.u * (|c| + |p|) := by
          exact mul_le_mul_of_nonneg_left (abs_add_le c p) hu
    calc
      |(c + p) * (1 + δa) - (S + t)| =
          |(c - S) + (p - t) + δa * (c + p)| := by ring_nf
      _ ≤ |c - S| + |p - t| + |δa * (c + p)| := by
        have h1 : |(c - S) + (p - t) + δa * (c + p)| ≤
            |(c - S) + (p - t)| + |δa * (c + p)| := abs_add_le _ _
        have h2 : |(c - S) + (p - t)| + |δa * (c + p)| ≤
            (|c - S| + |p - t|) + |δa * (c + p)| := by
          exact add_le_add_left (abs_add_le (c - S) (p - t)) _
        linarith
      _ ≤ gprev * B + fp.u * T +
          fp.u * ((1 + gprev) * B + (1 + fp.u) * T) := by
        have hcp : fp.u * (|c| + |p|) ≤
            fp.u * ((1 + gprev) * B + (1 + fp.u) * T) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hc hpabs) hu
        linarith
      _ = (gprev + fp.u * (1 + gprev)) * B +
          (fp.u + fp.u * (1 + fp.u)) * T := by ring
      _ ≤ gnext * B + gnext * T := by
        exact add_le_add (mul_le_mul_of_nonneg_right hcoeff_old hB)
          (mul_le_mul_of_nonneg_right hcoeff_new hT)
      _ = gnext * (B + T) := by ring
  have dot_error_pos :
      ∀ m : ℕ, gammaValid fp (m + 1) → ∀ x y : Fin (m + 1) → ℝ,
        |fl_dotProduct fp (m + 1) x y - ∑ j : Fin (m + 1), x j * y j| ≤
          gamma fp (m + 1) * (∑ j : Fin (m + 1), |x j| * |y j|) := by
    intro m
    induction m with
    | zero =>
        intro h x y
        obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
        have huγ : fp.u ≤ gamma fp 1 := gamma_u_le 1 (by norm_num) h
        have hmain : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            gamma fp 1 * (|x 0| * |y 0|) := by
          rw [hmul]
          calc
            |(x 0 * y 0) * (1 + δ) - x 0 * y 0| =
                |(x 0 * y 0) * δ| := by ring_nf
            _ = |x 0| * |y 0| * |δ| := by rw [abs_mul, abs_mul]
            _ ≤ |x 0| * |y 0| * fp.u := by
              exact mul_le_mul_of_nonneg_left hδ
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ ≤ |x 0| * |y 0| * gamma fp 1 := by
              exact mul_le_mul_of_nonneg_left huγ
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = gamma fp 1 * (|x 0| * |y 0|) := by ring
        simpa [fl_dotProduct] using hmain
    | succ m ih =>
        intro h x y
        let c : ℝ := fl_dotProduct fp (m + 1)
          (fun k : Fin (m + 1) => x k.castSucc) (fun k => y k.castSucc)
        let S : ℝ := ∑ k : Fin (m + 1), x k.castSucc * y k.castSucc
        let B : ℝ := ∑ k : Fin (m + 1), |x k.castSucc| * |y k.castSucc|
        let last : Fin (m + 2) := Fin.last (m + 1)
        let t : ℝ := x last * y last
        let T : ℝ := |x last| * |y last|
        have hprev_valid : gammaValid fp (m + 1) := by
          unfold gammaValid at *
          have hle : ((m + 1 : ℕ) : ℝ) * fp.u ≤ ((m + 2 : ℕ) : ℝ) * fp.u := by
            have hmle : ((m + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_right hmle fp.u_nonneg
          linarith
        have hih : |c - S| ≤ gamma fp (m + 1) * B := by
          simpa [c, S, B] using ih hprev_valid
            (fun k : Fin (m + 1) => x k.castSucc) (fun k => y k.castSucc)
        have hBnonneg : 0 ≤ B := by
          exact Finset.sum_nonneg
            (by intro k hk; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have hTnonneg : 0 ≤ T := by
          exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hSabs : |S| ≤ B := by
          simpa [S, B, abs_mul] using
            (Finset.abs_sum_le_sum_abs
              (fun k : Fin (m + 1) => x k.castSucc * y k.castSucc) Finset.univ)
        have hcabs : |c| ≤ (1 + gamma fp (m + 1)) * B := by
          calc
            |c| = |(c - S) + S| := by ring_nf
            _ ≤ |c - S| + |S| := abs_add_le _ _
            _ ≤ gamma fp (m + 1) * B + B := add_le_add hih hSabs
            _ = (1 + gamma fp (m + 1)) * B := by ring
        obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (x last) (y last)
        have hp : |fp.fl_mul (x last) (y last) - t| ≤ fp.u * T := by
          rw [hmul]
          calc
            |(x last * y last) * (1 + δm) - t| = |t * δm| := by
              congr 1
              calc
                (x last * y last) * (1 + δm) - t =
                    ((x last * y last) + (x last * y last) * δm) - t := by
                  rw [mul_add, mul_one]
                _ = t * δm := by
                  simp [t]
            _ = T * |δm| := by
              simp only [T, t]
              rw [abs_mul, abs_mul]
            _ ≤ T * fp.u := by
              exact mul_le_mul_of_nonneg_left hδm hTnonneg
            _ = fp.u * T := by ring
        have honeδ : |1 + δm| ≤ 1 + fp.u := by
          calc
            |1 + δm| ≤ |(1 : ℝ)| + |δm| := abs_add_le _ _
            _ = 1 + |δm| := by simp
            _ ≤ 1 + fp.u := by exact add_le_add_right hδm 1
        have hpabs : |fp.fl_mul (x last) (y last)| ≤ (1 + fp.u) * T := by
          rw [hmul]
          calc
            |(x last * y last) * (1 + δm)| = T * |1 + δm| := by
              simp only [T]
              rw [abs_mul, abs_mul]
            _ ≤ T * (1 + fp.u) := by
              exact mul_le_mul_of_nonneg_left honeδ hTnonneg
            _ = (1 + fp.u) * T := by ring
        obtain ⟨δa, hδa, hadd⟩ := fp.model_add c (fp.fl_mul (x last) (y last))
        have hcoeff_old :
            gamma fp (m + 1) + fp.u * (1 + gamma fp (m + 1)) ≤ gamma fp (m + 2) := by
          have hs := gamma_step_mul (m + 1) h
          nlinarith
        have hcoeff_new : fp.u + fp.u * (1 + fp.u) ≤ gamma fp (m + 2) := by
          have hs := gamma_square_le (m + 2) (by omega) h
          nlinarith
        have hstep := round_add_step c S (fp.fl_mul (x last) (y last)) t B T
          (gamma fp (m + 1)) (gamma fp (m + 2)) δa hδa hih hp hcabs hpabs
          hcoeff_old hcoeff_new hBnonneg hTnonneg
        calc
          |fl_dotProduct fp (m + 2) x y - ∑ j : Fin (m + 2), x j * y j|
              = |fp.fl_add c (fp.fl_mul (x last) (y last)) - (S + t)| := by
            simp [c, S, t, last, fl_dotProduct, Fin.foldl_succ_last, Fin.sum_univ_castSucc]
          _ = |(c + fp.fl_mul (x last) (y last)) * (1 + δa) - (S + t)| := by
            rw [hadd]
          _ ≤ gamma fp (m + 2) * (B + T) := hstep
          _ = gamma fp (m + 2) * (∑ j : Fin (m + 2), |x j| * |y j|) := by
            simp [B, T, last, Fin.sum_univ_castSucc]
  have dot_error :
      ∀ x y : Fin n → ℝ,
        |fl_dotProduct fp n x y - ∑ j : Fin n, x j * y j| ≤
          gamma fp n * (∑ j : Fin n, |x j| * |y j|) := by
    cases n with
    | zero => cases hnpos
    | succ m =>
        simpa using dot_error_pos m hn
  have residual_point_bound :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * xhat j| ≤
          lapackFerrDenom fp n A xhat b i := by
    intro i
    let C : ℝ := fl_matVec fp n n A xhat i
    let S : ℝ := ∑ j : Fin n, A i j * xhat j
    let B : ℝ := ∑ j : Fin n, |A i j| * |xhat j|
    have hdot : |C - S| ≤ gamma fp n * B := by
      simpa [C, S, B, fl_matVec] using dot_error (A i) xhat
    have hBnonneg : 0 ≤ B := by
      exact Finset.sum_nonneg
        (by intro j hj; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hSabs : |S| ≤ B := by
      simpa [S, B, abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun j : Fin n => A i j * xhat j) Finset.univ)
    have hCabs : |C| ≤ (1 + gamma fp n) * B := by
      calc
        |C| = |(C - S) + S| := by ring_nf
        _ ≤ |C - S| + |S| := abs_add_le _ _
        _ ≤ gamma fp n * B + B := add_le_add hdot hSabs
        _ = (1 + gamma fp n) * B := by ring
    obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (b i) C
    have hcoeff_old :
        gamma fp n + fp.u * (1 + gamma fp n) ≤ gamma fp (n + 1) := by
      have hs := gamma_step_mul n hn1
      nlinarith
    have hcoeff_b : fp.u ≤ gamma fp (n + 1) := gamma_u_le (n + 1) (by omega) hn1
    have hreserr :
        |(b i - S) - fp.fl_sub (b i) C| ≤ gamma fp (n + 1) * (|b i| + B) := by
      have hu : 0 ≤ fp.u := fp.u_nonneg
      have hbC : |δs * (b i - C)| ≤ fp.u * (|b i| + |C|) := by
        calc
          |δs * (b i - C)| = |δs| * |b i - C| := by rw [abs_mul]
          _ ≤ fp.u * |b i - C| := by
            exact mul_le_mul_of_nonneg_right hδs (abs_nonneg _)
          _ ≤ fp.u * (|b i| + |C|) := by
            have hbc : |b i - C| ≤ |b i| + |C| := by
              simpa [sub_eq_add_neg, abs_neg] using abs_add_le (b i) (-C)
            exact mul_le_mul_of_nonneg_left hbc hu
      calc
        |(b i - S) - fp.fl_sub (b i) C| =
            |(C - S) - δs * (b i - C)| := by
          rw [hsub]
          congr 1
          calc
            (b i - S) - (b i - C) * (1 + δs) =
                (b i - S) - ((b i - C) + (b i - C) * δs) := by
              rw [mul_add, mul_one]
            _ = (C - S) - δs * (b i - C) := by ring
        _ ≤ |C - S| + |δs * (b i - C)| := by
          simpa [sub_eq_add_neg, abs_neg] using
            (abs_add_le (C - S) (-(δs * (b i - C))))
        _ ≤ gamma fp n * B + fp.u * (|b i| + |C|) := add_le_add hdot hbC
        _ ≤ gamma fp n * B + fp.u * (|b i| + (1 + gamma fp n) * B) := by
          have harg : |b i| + |C| ≤ |b i| + (1 + gamma fp n) * B := by
            exact add_le_add_right hCabs _
          exact add_le_add_right (mul_le_mul_of_nonneg_left harg hu) _
        _ = fp.u * |b i| + (gamma fp n + fp.u * (1 + gamma fp n)) * B := by ring
        _ ≤ gamma fp (n + 1) * |b i| + gamma fp (n + 1) * B := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoeff_b (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hcoeff_old hBnonneg)
        _ = gamma fp (n + 1) * (|b i| + B) := by ring
    calc
      |b i - S| = |fp.fl_sub (b i) C + ((b i - S) - fp.fl_sub (b i) C)| := by
        ring_nf
      _ ≤ |fp.fl_sub (b i) C| + |(b i - S) - fp.fl_sub (b i) C| := abs_add_le _ _
      _ ≤ |fp.fl_sub (b i) C| + gamma fp (n + 1) * (|b i| + B) := by
        exact add_le_add_right hreserr _
      _ = lapackFerrDenom fp n A xhat b i := by
        simp [lapackFerrDenom, fl_residual, C, B, fl_matVec]
  have denom_nonneg : ∀ i : Fin n, 0 ≤ lapackFerrDenom fp n A xhat b i := by
    intro i
    exact le_trans (abs_nonneg _) (residual_point_bound i)
  have left_mul_eq : ∀ (v : Fin n → ℝ) (i : Fin n),
      ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * v k) = v i := by
    intro v i
    calc
      ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * v k)
          = ∑ k : Fin n, (∑ j : Fin n, A_inv i j * A j k) * v k := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        ring_nf
      _ = ∑ k : Fin n, (if i = k then 1 else 0) * v k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hInv i k]
      _ = v i := by simp
  have pointwise_error :
      ∀ i : Fin n,
        |x i - xhat i| ≤
          infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
    intro i
    have hx_rep : x i = ∑ j : Fin n, A_inv i j * b j := by
      symm
      calc
        ∑ j : Fin n, A_inv i j * b j
            = ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hAx j]
        _ = x i := left_mul_eq x i
    have hxhat_rep :
        xhat i = ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * xhat k) := by
      symm
      exact left_mul_eq xhat i
    have herr :
        x i - xhat i =
          ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k) := by
      calc
        x i - xhat i =
            (∑ j : Fin n, A_inv i j * b j) -
              (∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * xhat k)) := by
          rw [hx_rep, hxhat_rep]
        _ = ∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
    have hsum :
        |∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k)| ≤
          lapackFerrNumerator fp n A A_inv xhat b i := by
      calc
        |∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k)|
            ≤ ∑ j : Fin n, |A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun j : Fin n => A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k))
              Finset.univ)
        _ = ∑ j : Fin n, |A_inv i j| * |b j - ∑ k : Fin n, A j k * xhat k| := by
          simp [abs_mul]
        _ ≤ ∑ j : Fin n, |A_inv i j| * lapackFerrDenom fp n A xhat b j := by
          exact Finset.sum_le_sum (by
            intro j hj
            exact mul_le_mul_of_nonneg_left (residual_point_bound j) (abs_nonneg _))
        _ = lapackFerrNumerator fp n A A_inv xhat b i := by
          simp [lapackFerrNumerator]
    have hnum_nonneg : 0 ≤ lapackFerrNumerator fp n A A_inv xhat b i := by
      simp [lapackFerrNumerator]
      exact Finset.sum_nonneg (by
        intro j hj
        exact mul_nonneg (abs_nonneg _) (denom_nonneg j))
    have hnum_le_norm :
        lapackFerrNumerator fp n A A_inv xhat b i ≤
          infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
      calc
        lapackFerrNumerator fp n A A_inv xhat b i =
            |lapackFerrNumerator fp n A A_inv xhat b i| := by
          rw [abs_of_nonneg hnum_nonneg]
        _ ≤ infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
          unfold infNormVec
          exact Finset.le_sup' (fun i => |lapackFerrNumerator fp n A A_inv xhat b i|)
            (Finset.mem_univ i)
    calc
      |x i - xhat i| =
          |∑ j : Fin n, A_inv i j * (b j - ∑ k : Fin n, A j k * xhat k)| := by
        rw [herr]
      _ ≤ lapackFerrNumerator fp n A A_inv xhat b i := hsum
      _ ≤ infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := hnum_le_norm
  have hnorm :
      infNormVec hnpos (fun i => x i - xhat i) ≤
        infNormVec hnpos (lapackFerrNumerator fp n A A_inv xhat b) := by
    unfold infNormVec
    apply Finset.sup'_le
    intro i hi
    exact pointwise_error i
  unfold lapackFerrBound
  exact div_le_div_of_nonneg_right hnorm hxhat_norm_pos.le

end LeanFpAnalysis.FP
