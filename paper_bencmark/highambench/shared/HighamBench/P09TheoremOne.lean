import HighamBench.P09Base

namespace HighamBench

open scoped BigOperators

private lemma p09_abs_flAdd_sub_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hadd⟩ := model.add_model a b
  rw [hadd]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * (1 + θa * model.epsilon) +
          b * (1 + θb * model.epsilon) - (a + b)| =
        model.epsilon * |a * θa + b * θb| := by
      rw [show a * (1 + θa * model.epsilon) +
          b * (1 + θb * model.epsilon) - (a + b) =
            model.epsilon * (a * θa + b * θb) by ring]
      rw [abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * (|a * θa| + |b * θb|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hε
    _ ≤ model.epsilon * (|a| + |b|) := by
      apply mul_le_mul_of_nonneg_left _ hε
      rw [abs_mul, abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg b]

private lemma p09_abs_flMul_sub_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * |a * b| := by
  obtain ⟨θ, hθ, hmul⟩ := model.mul_model a b
  rw [hmul]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        model.epsilon * |a * b| * |θ| := by
      rw [show a * b * (1 + θ * model.epsilon) - a * b =
          model.epsilon * (a * b) * θ by ring]
      rw [abs_mul, abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * |a * b| := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hθ
          (mul_nonneg hε (abs_nonneg (a * b))))

private lemma p09_abs_flSin_sub_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flSin a - Real.sin a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hsin⟩ := model.sin_model a
  rw [hsin]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.sin a + model.gamma * θ * model.epsilon - Real.sin a =
      model.gamma * model.epsilon * θ by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_nonneg hε]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hθ
      (mul_nonneg model.gamma_nonneg hε))

private lemma p09_abs_flCos_sub_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flCos a - Real.cos a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hcos⟩ := model.cos_model a
  rw [hcos]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.cos a + model.gamma * θ * model.epsilon - Real.cos a =
      model.gamma * model.epsilon * θ by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_nonneg hε]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hθ
      (mul_nonneg model.gamma_nonneg hε))

private lemma p09_complex_norm_le_of_component_bounds
    (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) :
    ‖z‖ ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have hre_sq : z.re ^ 2 ≤ a ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg ha] using hre
  have him_sq : z.im ^ 2 ≤ b ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg hb] using him
  exact add_le_add hre_sq him_sq

private lemma p09_complex_norm_le_mk_of_component_bounds
    (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) :
    ‖z‖ ≤ ‖(⟨a, b⟩ : ℂ)‖ := by
  simpa only [Complex.norm_eq_sqrt_sq_add_sq, Complex.normSq_mk] using
    p09_complex_norm_le_of_component_bounds z ha hb hre him

private noncomputable def p09RoundedComplexAddDev
    (model : P09WilkinsonModel) (x y : ℂ) : ℂ :=
  ⟨model.flAdd x.re y.re, model.flAdd x.im y.im⟩

private lemma p09_norm_abs_components (z : ℂ) :
    ‖(⟨|z.re|, |z.im|⟩ : ℂ)‖ = ‖z‖ := by
  simp only [Complex.norm_eq_sqrt_sq_add_sq]
  congr 2 <;> rw [sq_abs]

private lemma p09_norm_roundedComplexAdd_sub_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAddDev model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let ax : ℂ := ⟨|x.re|, |x.im|⟩
  let ay : ℂ := ⟨|y.re|, |y.im|⟩
  let bound : ℂ := (model.epsilon : ℂ) * (ax + ay)
  have hbre : bound.re = model.epsilon * (|x.re| + |y.re|) := by
    simp [bound, ax, ay]
  have hbim : bound.im = model.epsilon * (|x.im| + |y.im|) := by
    simp [bound, ax, ay]
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexAddDev model x y - (x + y))
    (mul_nonneg hε (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg hε (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (by simpa [p09RoundedComplexAddDev] using
      p09_abs_flAdd_sub_le model x.re y.re)
    (by simpa [p09RoundedComplexAddDev] using
      p09_abs_flAdd_sub_le model x.im y.im)
  rw [← hbre, ← hbim] at hcomponent
  calc
    ‖p09RoundedComplexAddDev model x y - (x + y)‖ ≤ ‖bound‖ := hcomponent
    _ = model.epsilon * ‖ax + ay‖ := by
      change ‖(model.epsilon : ℂ) * (ax + ay)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hε]
    _ ≤ model.epsilon * (‖ax‖ + ‖ay‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le ax ay) hε
    _ = model.epsilon * (‖x‖ + ‖y‖) := by
      rw [show ‖ax‖ = ‖x‖ by exact p09_norm_abs_components x,
        show ‖ay‖ = ‖y‖ by exact p09_norm_abs_components y]

private lemma p09_abs_flMul_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b| ≤ (1 + model.epsilon) * |a * b| := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |model.flMul a b| = |a * b + (model.flMul a b - a * b)| := by ring_nf
    _ ≤ |a * b| + |model.flMul a b - a * b| := abs_add_le _ _
    _ ≤ |a * b| + model.epsilon * |a * b| :=
      add_le_add le_rfl (p09_abs_flMul_sub_le model a b)
    _ = (1 + model.epsilon) * |a * b| := by ring

private lemma p09_complex_product_component_majorant
    (x y : ℂ) :
    ‖(⟨|x.re * y.re| + |x.im * y.im|,
        |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ≤
      Real.sqrt 2 * ‖x‖ * ‖y‖ := by
  let a := |x.re|
  let b := |x.im|
  let c := |y.re|
  let d := |y.im|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have hd : 0 ≤ d := abs_nonneg _
  have hsq_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hmajor_sq :
      (a * c + b * d) ^ 2 + (a * d + b * c) ^ 2 ≤
        2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
    nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c)]
  have hsq :
      ‖(⟨|x.re * y.re| + |x.im * y.im|,
          |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ^ 2 ≤
        (Real.sqrt 2 * ‖x‖ * ‖y‖) ^ 2 := by
    have hx : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [a, b, pow_two]
      nlinarith [sq_abs x.re, sq_abs x.im]
    have hy : ‖y‖ ^ 2 = c ^ 2 + d ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [c, d, pow_two]
      nlinarith [sq_abs y.re, sq_abs y.im]
    calc
      ‖(⟨|x.re * y.re| + |x.im * y.im|,
          |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ^ 2 =
          (a * c + b * d) ^ 2 + (a * d + b * c) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_mk]
        simp only [abs_mul, a, b, c, d]
        ring
      _ ≤ 2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := hmajor_sq
      _ = (Real.sqrt 2 * ‖x‖ * ‖y‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt, hx, hy]
        ring
  rw [sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))
      (norm_nonneg y))] at hsq
  exact hsq

private lemma p09_norm_roundedComplexMul_sub_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let A : ℝ := |x.re * y.re| + |x.im * y.im|
  let B : ℝ := |x.re * y.im| + |x.im * y.re|
  let s : ℝ := 2 * model.epsilon + model.epsilon ^ 2
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs : 0 ≤ s := add_nonneg (mul_nonneg (by norm_num) hε) (sq_nonneg _)
  have hre :
      |(p09RoundedComplexMul model x y - x * y).re| ≤ s * A := by
    let p := model.flMul x.re y.re
    let q := model.flMul x.im y.im
    have hadd := p09_abs_flAdd_sub_le model p (-q)
    have hp := p09_abs_flMul_sub_le model x.re y.re
    have hq := p09_abs_flMul_sub_le model x.im y.im
    have hpabs := p09_abs_flMul_le model x.re y.re
    have hqabs := p09_abs_flMul_le model x.im y.im
    change |model.flAdd p (-q) - (x.re * y.re - x.im * y.im)| ≤ _
    calc
      |model.flAdd p (-q) - (x.re * y.re - x.im * y.im)| =
          |(model.flAdd p (-q) - (p - q)) +
            ((p - q) - (x.re * y.re - x.im * y.im))| := by ring_nf
      _ ≤ |model.flAdd p (-q) - (p - q)| +
          |(p - q) - (x.re * y.re - x.im * y.im)| := abs_add_le _ _
      _ ≤ model.epsilon * (|p| + |-q|) +
          (|p - x.re * y.re| + |q - x.im * y.im|) := by
        apply add_le_add
        · simpa only [sub_eq_add_neg] using hadd
        · rw [show (p - q) - (x.re * y.re - x.im * y.im) =
              (p - x.re * y.re) - (q - x.im * y.im) by ring]
          exact abs_sub (p - x.re * y.re) (q - x.im * y.im)
      _ ≤ model.epsilon *
            ((1 + model.epsilon) * |x.re * y.re| +
              (1 + model.epsilon) * |x.im * y.im|) +
          (model.epsilon * |x.re * y.re| +
            model.epsilon * |x.im * y.im|) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hε
          exact add_le_add hpabs (by simpa only [abs_neg] using hqabs)
        · exact add_le_add hp hq
      _ = s * A := by unfold s A; ring
  have him :
      |(p09RoundedComplexMul model x y - x * y).im| ≤ s * B := by
    let p := model.flMul x.re y.im
    let q := model.flMul x.im y.re
    have hadd := p09_abs_flAdd_sub_le model p q
    have hp := p09_abs_flMul_sub_le model x.re y.im
    have hq := p09_abs_flMul_sub_le model x.im y.re
    have hpabs := p09_abs_flMul_le model x.re y.im
    have hqabs := p09_abs_flMul_le model x.im y.re
    change |model.flAdd p q - (x.re * y.im + x.im * y.re)| ≤ _
    calc
      |model.flAdd p q - (x.re * y.im + x.im * y.re)| =
          |(model.flAdd p q - (p + q)) +
            ((p + q) - (x.re * y.im + x.im * y.re))| := by ring_nf
      _ ≤ |model.flAdd p q - (p + q)| +
          |(p + q) - (x.re * y.im + x.im * y.re)| := abs_add_le _ _
      _ ≤ model.epsilon * (|p| + |q|) +
          (|p - x.re * y.im| + |q - x.im * y.re|) := by
        apply add_le_add
        · exact hadd
        · rw [show (p + q) - (x.re * y.im + x.im * y.re) =
              (p - x.re * y.im) + (q - x.im * y.re) by ring]
          exact abs_add_le _ _
      _ ≤ model.epsilon *
            ((1 + model.epsilon) * |x.re * y.im| +
              (1 + model.epsilon) * |x.im * y.re|) +
          (model.epsilon * |x.re * y.im| +
            model.epsilon * |x.im * y.re|) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hε
          exact add_le_add hpabs hqabs
        · exact add_le_add hp hq
      _ = s * B := by unfold s B; ring
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexMul model x y - x * y)
    (mul_nonneg hs hA) (mul_nonneg hs hB) hre him
  calc
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
        ‖(⟨s * A, s * B⟩ : ℂ)‖ := hcomponent
    _ = s * ‖(⟨A, B⟩ : ℂ)‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
      rw [show (s * A) ^ 2 + (s * B) ^ 2 = s ^ 2 * (A ^ 2 + B ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
    _ ≤ s * (Real.sqrt 2 * ‖x‖ * ‖y‖) := by
      apply mul_le_mul_of_nonneg_left _ hs
      exact p09_complex_product_component_majorant x y
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
      have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hsqrt_two : Real.sqrt 2 ≤ 2 := hsqrt.trans (by norm_num)
      have hcoef : s * Real.sqrt 2 ≤
          3 * model.epsilon + 2 * model.epsilon ^ 2 := by
        unfold s
        nlinarith
      calc
        s * (Real.sqrt 2 * ‖x‖ * ‖y‖) =
            (s * Real.sqrt 2) * ‖x‖ * ‖y‖ := by ring
        _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
          gcongr

private noncomputable def p09ExactRootDev {q : ℕ} [NeZero q]
    (j : ZMod q) : ℂ :=
  ⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩

private lemma p09ExactRootDev_eq_stdAddChar {q : ℕ} [NeZero q]
    (j : ZMod q) :
    p09ExactRootDev j = ZMod.stdAddChar j := by
  rw [p09StdAddChar_positive_exp]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hexponent :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p09RootAngle j : ℂ) * Complex.I := by
    unfold p09RootAngle
    push_cast
    field_simp
  rw [hexponent, Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [p09ExactRootDev, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private lemma p09_norm_exactRootDev (q : ℕ) [NeZero q] (j : ZMod q) :
    ‖p09ExactRootDev j‖ = 1 := by
  rw [p09ExactRootDev_eq_stdAddChar]
  simp

private lemma p09_norm_roundedRoot_sub_exact_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - p09ExactRootDev j‖ ≤
      2 * model.gamma * model.epsilon := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγε : 0 ≤ model.gamma * model.epsilon :=
    mul_nonneg model.gamma_nonneg hε
  have hre :
      |(p09RoundedRoot model j - p09ExactRootDev j).re| ≤
        model.gamma * model.epsilon := by
    simpa [p09RoundedRoot, p09ExactRootDev] using
      p09_abs_flCos_sub_le model (p09RootAngle j)
  have him :
      |(p09RoundedRoot model j - p09ExactRootDev j).im| ≤
        model.gamma * model.epsilon := by
    simpa [p09RoundedRoot, p09ExactRootDev] using
      p09_abs_flSin_sub_le model (p09RootAngle j)
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedRoot model j - p09ExactRootDev j) hγε hγε hre him
  calc
    ‖p09RoundedRoot model j - p09ExactRootDev j‖ ≤
        ‖(⟨model.gamma * model.epsilon,
          model.gamma * model.epsilon⟩ : ℂ)‖ := hcomponent
    _ = Real.sqrt 2 * (model.gamma * model.epsilon) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      rw [show (model.gamma * model.epsilon) ^ 2 +
          (model.gamma * model.epsilon) ^ 2 =
            2 * (model.gamma * model.epsilon) ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hγε]
    _ ≤ 2 * model.gamma * model.epsilon := by
      have hsqrt : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg 2]
      nlinarith

private lemma p09_norm_roundedRoot_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤
      1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ =
        ‖p09ExactRootDev j +
          (p09RoundedRoot model j - p09ExactRootDev j)‖ := by ring_nf
    _ ≤ ‖p09ExactRootDev j‖ +
        ‖p09RoundedRoot model j - p09ExactRootDev j‖ := norm_add_le _ _
    _ ≤ 1 + 2 * model.gamma * model.epsilon := by
      rw [p09_norm_exactRootDev]
      gcongr
      exact p09_norm_roundedRoot_sub_exact_le model j

private lemma p09_norm_roundedRootMul_sub_exact_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        p09ExactRootDev j * x‖ ≤
      model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
        (2 + 10 * model.gamma) * model.epsilon ^ 2 * ‖x‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hmul := p09_norm_roundedComplexMul_sub_le model
    (p09RoundedRoot model j) x
  have hroot := p09_norm_roundedRoot_sub_exact_le model j
  have hrootnorm := p09_norm_roundedRoot_le model j
  calc
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        p09ExactRootDev j * x‖ =
        ‖(p09RoundedComplexMul model (p09RoundedRoot model j) x -
            p09RoundedRoot model j * x) +
          (p09RoundedRoot model j - p09ExactRootDev j) * x‖ := by ring_nf
    _ ≤ ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
            p09RoundedRoot model j * x‖ +
          ‖(p09RoundedRoot model j - p09ExactRootDev j) * x‖ := norm_add_le _ _
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
            ‖p09RoundedRoot model j‖ * ‖x‖ +
          (2 * model.gamma * model.epsilon) * ‖x‖ := by
      rw [norm_mul]
      exact add_le_add hmul
        (mul_le_mul_of_nonneg_right hroot (norm_nonneg x))
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
            (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
          (2 * model.gamma * model.epsilon) * ‖x‖ := by
      gcongr
    _ ≤ model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
          (2 + 10 * model.gamma) * model.epsilon ^ 2 * ‖x‖ := by
      have hnonneg :
          0 ≤ 4 * model.gamma * model.epsilon ^ 2 *
            (1 - model.epsilon) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hγ) (sq_nonneg _))
          (sub_nonneg.mpr hεone)
      have hcoef :
          (3 * model.epsilon + 2 * model.epsilon ^ 2) *
              (1 + 2 * model.gamma * model.epsilon) +
            2 * model.gamma * model.epsilon ≤
          model.epsilon * (3 + 2 * model.gamma) +
            (2 + 10 * model.gamma) * model.epsilon ^ 2 := by
        nlinarith
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hcoef) (norm_nonneg x)]

private def p09RecursiveSumSecondOrder : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n : ℝ) + 2 * p09RecursiveSumSecondOrder n

private lemma p09RecursiveSumSecondOrder_nonneg (n : ℕ) :
    0 ≤ p09RecursiveSumSecondOrder n := by
  induction n with
  | zero => simp [p09RecursiveSumSecondOrder]
  | succ n ih =>
      simp only [p09RecursiveSumSecondOrder]
      positivity

private lemma p09_abs_recursiveSum_sub_sum_le
    (model : P09WilkinsonModel) (hεone : model.epsilon ≤ 1) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum model.flAdd n v - ∑ i : Fin n, v i| ≤
        ((n : ℝ) * model.epsilon +
            p09RecursiveSumSecondOrder n * model.epsilon ^ 2) *
          ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        simpa [recursiveSum, p09RecursiveSumSecondOrder] using
          (mul_nonneg hε (abs_nonneg (v 0)))
      · let prefixValues : Fin n → ℝ := fun i ↦ v i.castSucc
        let lastTerm : ℝ := v (Fin.last n)
        let exactPrefix : ℝ := ∑ i : Fin n, prefixValues i
        let absPrefix : ℝ := ∑ i : Fin n, |prefixValues i|
        let roundedPrefix : ℝ := recursiveSum model.flAdd n prefixValues
        let previousBound : ℝ :=
          ((n : ℝ) * model.epsilon +
              p09RecursiveSumSecondOrder n * model.epsilon ^ 2) * absPrefix
        have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        have habsPrefix : 0 ≤ absPrefix := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        have hpreviousCoeff :
            0 ≤ (n : ℝ) * model.epsilon +
              p09RecursiveSumSecondOrder n * model.epsilon ^ 2 :=
          add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
            (mul_nonneg (p09RecursiveSumSecondOrder_nonneg n) (sq_nonneg _))
        have hpreviousNonneg : 0 ≤ previousBound :=
          mul_nonneg hpreviousCoeff habsPrefix
        have hprevious : |roundedPrefix - exactPrefix| ≤ previousBound := by
          simpa [prefixValues, roundedPrefix, exactPrefix, previousBound, absPrefix]
            using ih prefixValues
        have hexactPrefix : |exactPrefix| ≤ absPrefix := by
          simpa [exactPrefix, absPrefix] using
            (Finset.abs_sum_le_sum_abs (f := prefixValues) Finset.univ)
        have hroundedPrefix : |roundedPrefix| ≤ absPrefix + previousBound := by
          calc
            |roundedPrefix| = |exactPrefix + (roundedPrefix - exactPrefix)| := by ring_nf
            _ ≤ |exactPrefix| + |roundedPrefix - exactPrefix| := abs_add_le _ _
            _ ≤ absPrefix + previousBound := add_le_add hexactPrefix hprevious
        have hadd := p09_abs_flAdd_sub_le model roundedPrefix lastTerm
        rw [recursiveSum, dif_neg hn, Fin.sum_univ_castSucc]
        change |model.flAdd roundedPrefix lastTerm -
            (exactPrefix + lastTerm)| ≤ _
        have hsplit :
            |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| ≤
              model.epsilon * (|roundedPrefix| + |lastTerm|) +
                |roundedPrefix - exactPrefix| := by
          calc
            |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| =
                |(model.flAdd roundedPrefix lastTerm -
                    (roundedPrefix + lastTerm)) +
                  (roundedPrefix - exactPrefix)| := by ring_nf
            _ ≤ |model.flAdd roundedPrefix lastTerm -
                    (roundedPrefix + lastTerm)| +
                  |roundedPrefix - exactPrefix| := abs_add_le _ _
            _ ≤ model.epsilon * (|roundedPrefix| + |lastTerm|) +
                  |roundedPrefix - exactPrefix| := add_le_add hadd le_rfl
        calc
          |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| ≤
              model.epsilon * (|roundedPrefix| + |lastTerm|) +
                |roundedPrefix - exactPrefix| := hsplit
          _ ≤ model.epsilon * (absPrefix + previousBound + |lastTerm|) +
                previousBound := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (add_le_add hroundedPrefix le_rfl) hε) hprevious
          _ ≤ (((n + 1 : ℕ) : ℝ) * model.epsilon +
                p09RecursiveSumSecondOrder (n + 1) * model.epsilon ^ 2) *
              (absPrefix + |lastTerm|) := by
            have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
            have hlast : 0 ≤ |lastTerm| := abs_nonneg _
            have hrem := p09RecursiveSumSecondOrder_nonneg n
            have hremainA :
                0 ≤ p09RecursiveSumSecondOrder n * model.epsilon ^ 2 *
                  (1 - model.epsilon) * absPrefix :=
              mul_nonneg
                (mul_nonneg
                  (mul_nonneg hrem (sq_nonneg _)) (sub_nonneg.mpr hεone))
                habsPrefix
            have hlinearLast :
                0 ≤ (n : ℝ) * model.epsilon * |lastTerm| :=
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) hlast
            have hremainderLast :
                0 ≤ ((n : ℝ) + 2 * p09RecursiveSumSecondOrder n) *
                  model.epsilon ^ 2 * |lastTerm| :=
              mul_nonneg
                (mul_nonneg
                  (add_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg (by norm_num) hrem))
                  (sq_nonneg _)) hlast
            dsimp [previousBound]
            simp only [p09RecursiveSumSecondOrder, Nat.cast_add, Nat.cast_one]
            nlinarith
          _ = (((n + 1 : ℕ) : ℝ) * model.epsilon +
                p09RecursiveSumSecondOrder (n + 1) * model.epsilon ^ 2) *
              ∑ i : Fin (n + 1), |v i| := by
            congr 1
            rw [Fin.sum_univ_castSucc]

private lemma p09_norm_roundedComplexSum_sub_sum_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      ((q : ℝ) * model.epsilon +
          p09RecursiveSumSecondOrder q * model.epsilon ^ 2) *
        ∑ j : ZMod q, ‖term j‖ := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let coefficient : ℝ :=
    (q : ℝ) * model.epsilon +
      p09RecursiveSumSecondOrder q * model.epsilon ^ 2
  let reTotal : ℝ := ∑ i : Fin q, |(term (index i)).re|
  let imTotal : ℝ := ∑ i : Fin q, |(term (index i)).im|
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoefficient : 0 ≤ coefficient :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
      (mul_nonneg (p09RecursiveSumSecondOrder_nonneg q) (sq_nonneg _))
  have hre :
      |(p09RoundedComplexSum model term - ∑ j : ZMod q, term j).re| ≤
        coefficient * reTotal := by
    have hsum : (∑ j : ZMod q, term j).re =
        ∑ i : Fin q, (term (index i)).re := by
      rw [show (∑ j : ZMod q, term j).re =
          ∑ j : ZMod q, (term j).re by simp]
      symm
      exact Fintype.sum_equiv index
        (fun i : Fin q ↦ (term (index i)).re)
        (fun j : ZMod q ↦ (term j).re) (fun _ ↦ rfl)
    change |(p09RoundedComplexSum model term).re -
        (∑ j : ZMod q, term j).re| ≤ _
    rw [hsum]
    simpa [p09RoundedComplexSum, index, coefficient, reTotal] using
      p09_abs_recursiveSum_sub_sum_le model hεone q
        (fun i : Fin q ↦ (term (index i)).re)
  have him :
      |(p09RoundedComplexSum model term - ∑ j : ZMod q, term j).im| ≤
        coefficient * imTotal := by
    have hsum : (∑ j : ZMod q, term j).im =
        ∑ i : Fin q, (term (index i)).im := by
      rw [show (∑ j : ZMod q, term j).im =
          ∑ j : ZMod q, (term j).im by simp]
      symm
      exact Fintype.sum_equiv index
        (fun i : Fin q ↦ (term (index i)).im)
        (fun j : ZMod q ↦ (term j).im) (fun _ ↦ rfl)
    change |(p09RoundedComplexSum model term).im -
        (∑ j : ZMod q, term j).im| ≤ _
    rw [hsum]
    simpa [p09RoundedComplexSum, index, coefficient, imTotal] using
      p09_abs_recursiveSum_sub_sum_le model hεone q
        (fun i : Fin q ↦ (term (index i)).im)
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexSum model term - ∑ j : ZMod q, term j)
    (mul_nonneg hcoefficient (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    (mul_nonneg hcoefficient (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    hre him
  let absTerm : Fin q → ℂ := fun i ↦
    ⟨|(term (index i)).re|, |(term (index i)).im|⟩
  have hmajorant :
      ‖(⟨coefficient * reTotal, coefficient * imTotal⟩ : ℂ)‖ ≤
        coefficient * ∑ j : ZMod q, ‖term j‖ := by
    have hmk :
        (⟨coefficient * reTotal, coefficient * imTotal⟩ : ℂ) =
          (coefficient : ℂ) * ∑ i : Fin q, absTerm i := by
      apply Complex.ext <;>
        simp [absTerm, reTotal, imTotal]
    rw [hmk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcoefficient]
    apply mul_le_mul_of_nonneg_left _ hcoefficient
    calc
      ‖∑ i : Fin q, absTerm i‖ ≤ ∑ i : Fin q, ‖absTerm i‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin q, ‖term (index i)‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact p09_norm_abs_components (term (index i))
      _ = ∑ j : ZMod q, ‖term j‖ := by
        exact Fintype.sum_equiv index
          (fun i : Fin q ↦ ‖term (index i)‖)
          (fun j : ZMod q ↦ ‖term j‖) (fun _ ↦ rfl)
  exact hcomponent.trans hmajorant

private lemma p09_norm_roundedComplexSum_two_sub_sum_le
    (model : P09WilkinsonModel) (term : ZMod 2 → ℂ) :
    ‖p09RoundedComplexSum model term - ∑ j : ZMod 2, term j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖term j‖ := by
  let index : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  have hrounded : p09RoundedComplexSum model term =
      p09RoundedComplexAddDev model (term (index 0)) (term (index 1)) := by
    apply Complex.ext <;>
      simp [p09RoundedComplexSum, p09RoundedComplexAddDev, recursiveSum, index]
  have hexact : (∑ j : ZMod 2, term j) =
      term (index 0) + term (index 1) := by
    calc
      (∑ j : ZMod 2, term j) = ∑ i : Fin 2, term (index i) := by
        symm
        exact Fintype.sum_equiv index
          (fun i : Fin 2 ↦ term (index i)) term (fun _ ↦ rfl)
      _ = term (index 0) + term (index 1) := by
        simp [Fin.sum_univ_two]
  rw [hrounded, hexact]
  calc
    ‖p09RoundedComplexAddDev model (term (index 0)) (term (index 1)) -
        (term (index 0) + term (index 1))‖ ≤
      model.epsilon * (‖term (index 0)‖ + ‖term (index 1)‖) :=
        p09_norm_roundedComplexAdd_sub_le model _ _
    _ = model.epsilon * ∑ j : ZMod 2, ‖term j‖ := by
      congr 1
      calc
        ‖term (index 0)‖ + ‖term (index 1)‖ =
            ∑ i : Fin 2, ‖term (index i)‖ := by simp [Fin.sum_univ_two]
        _ = ∑ j : ZMod 2, ‖term j‖ :=
          Fintype.sum_equiv index
            (fun i : Fin 2 ↦ ‖term (index i)‖)
            (fun j : ZMod 2 ↦ ‖term j‖) (fun _ ↦ rfl)

private lemma p09RadixTwoCoefficientApply_eq (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  by_cases hj : j = 0
  · subst j
    simp [p09RadixTwoCoefficientApply]
  · have hjone : j = 1 := by
      fin_cases j
      · contradiction
      · rfl
    rw [hjone]
    simp only [p09RadixTwoCoefficientApply, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    rw [p09StdAddChar_positive_exp]
    have hexponent :
        2 * Real.pi * Complex.I * ((1 : ZMod 2).val : ℂ) /
            ((2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      simp [ZMod.val_one]
      ring
    rw [hexponent, Complex.exp_pi_mul_I, neg_one_mul]

private lemma p09_norm_roundedRadixTwoBlock_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  let term : ZMod 2 → ℂ := fun j ↦
    p09RadixTwoCoefficientApply (j * k) (x j)
  have hsum := p09_norm_roundedComplexSum_two_sub_sum_le model term
  have hexact : (∑ j : ZMod 2, term j) =
      ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact p09RadixTwoCoefficientApply_eq (j * k) (x j)
  have hnorm : (∑ j : ZMod 2, ‖term j‖) = ∑ j : ZMod 2, ‖x j‖ := by
    apply Finset.sum_congr rfl
    intro j _hj
    unfold term
    rw [p09RadixTwoCoefficientApply_eq]
    simp
  simpa [p09RoundedRadixTwoBlock, term, hexact, hnorm] using hsum

private lemma p09StdAddChar_four_zero :
    ZMod.stdAddChar (0 : ZMod 4) = 1 := by simp

private lemma p09StdAddChar_four_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [p09StdAddChar_positive_exp]
  have hval : (1 : ZMod 4).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 1) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((1 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) = (Real.pi / 2 : ℂ) * Complex.I := by
    rw [hval]
    push_cast
    norm_num
    ring
  rw [hexponent, Complex.exp_pi_div_two_mul_I]

private lemma p09StdAddChar_four_two :
    ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  rw [p09StdAddChar_positive_exp]
  have hval : (2 : ZMod 4).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 2) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((2 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) = Real.pi * Complex.I := by
    rw [hval]
    push_cast
    ring
  rw [hexponent, Complex.exp_pi_mul_I]

private lemma p09StdAddChar_four_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  rw [p09StdAddChar_positive_exp]
  have hval : (3 : ZMod 4).val = 3 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 3) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((3 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) =
        Real.pi * Complex.I + (Real.pi / 2 : ℂ) * Complex.I := by
    rw [hval]
    push_cast
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_pi_div_two_mul_I]
  ring

private lemma p09RadixFourCoefficientApply_eq (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hj with rfl | rfl | rfl | rfl
  · simp [p09RadixFourCoefficientApply, p09StdAddChar_four_zero]
  · rw [p09StdAddChar_four_one]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (1 : ZMod 4) ≠ 0), if_pos rfl]
    apply Complex.ext <;> simp [p09RadixFourCoefficientApply]
  · rw [p09StdAddChar_four_two]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (2 : ZMod 4) ≠ 0),
      if_neg (by decide : (2 : ZMod 4) ≠ 1), if_pos rfl]
    simp
  · rw [p09StdAddChar_four_three]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (3 : ZMod 4) ≠ 0),
      if_neg (by decide : (3 : ZMod 4) ≠ 1),
      if_neg (by decide : (3 : ZMod 4) ≠ 2)]
    apply Complex.ext <;> simp [p09RadixFourCoefficientApply]

private noncomputable def p09RoundedBalancedFourSumDev
    (model : P09WilkinsonModel) (term : Fin 4 → ℂ) : ℂ :=
  p09RoundedComplexAddDev model
    (p09RoundedComplexAddDev model (term 0) (term 1))
    (p09RoundedComplexAddDev model (term 2) (term 3))

private lemma p09_norm_roundedBalancedFourSum_sub_sum_le
    (model : P09WilkinsonModel) (term : Fin 4 → ℂ) :
    ‖p09RoundedBalancedFourSumDev model term - ∑ i : Fin 4, term i‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ i : Fin 4, ‖term i‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let exactLeft : ℂ := term 0 + term 1
  let exactRight : ℂ := term 2 + term 3
  let roundedLeft : ℂ := p09RoundedComplexAddDev model (term 0) (term 1)
  let roundedRight : ℂ := p09RoundedComplexAddDev model (term 2) (term 3)
  let inputL1 : ℝ := ∑ i : Fin 4, ‖term i‖
  have hinputL1 : 0 ≤ inputL1 := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hleft : ‖roundedLeft - exactLeft‖ ≤
      model.epsilon * (‖term 0‖ + ‖term 1‖) := by
    exact p09_norm_roundedComplexAdd_sub_le model _ _
  have hright : ‖roundedRight - exactRight‖ ≤
      model.epsilon * (‖term 2‖ + ‖term 3‖) := by
    exact p09_norm_roundedComplexAdd_sub_le model _ _
  have hpair : ‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖ ≤
      model.epsilon * inputL1 := by
    calc
      ‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖ ≤
          model.epsilon * (‖term 0‖ + ‖term 1‖) +
            model.epsilon * (‖term 2‖ + ‖term 3‖) := add_le_add hleft hright
      _ = model.epsilon * inputL1 := by
        simp [inputL1, Fin.sum_univ_four]
        ring
  have hroundedNorm : ‖roundedLeft‖ + ‖roundedRight‖ ≤
      (1 + model.epsilon) * inputL1 := by
    calc
      ‖roundedLeft‖ + ‖roundedRight‖ =
          ‖exactLeft + (roundedLeft - exactLeft)‖ +
            ‖exactRight + (roundedRight - exactRight)‖ := by ring_nf
      _ ≤ (‖exactLeft‖ + ‖roundedLeft - exactLeft‖) +
            (‖exactRight‖ + ‖roundedRight - exactRight‖) :=
        add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ ((‖term 0‖ + ‖term 1‖) + ‖roundedLeft - exactLeft‖) +
            ((‖term 2‖ + ‖term 3‖) + ‖roundedRight - exactRight‖) := by
        exact add_le_add
          (add_le_add (norm_add_le _ _) le_rfl)
          (add_le_add (norm_add_le _ _) le_rfl)
      _ = inputL1 +
            (‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖) := by
        simp [inputL1, Fin.sum_univ_four]
        ring
      _ ≤ inputL1 + model.epsilon * inputL1 := add_le_add le_rfl hpair
      _ = (1 + model.epsilon) * inputL1 := by ring
  have hfinal := p09_norm_roundedComplexAdd_sub_le model
    roundedLeft roundedRight
  rw [Fin.sum_univ_four]
  have hsum : term 0 + term 1 + term 2 + term 3 =
      exactLeft + exactRight := by
    dsimp [exactLeft, exactRight]
    ring
  rw [hsum]
  unfold p09RoundedBalancedFourSumDev
  change ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
      (exactLeft + exactRight)‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) * inputL1
  calc
    ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
        (exactLeft + exactRight)‖ =
        ‖(p09RoundedComplexAddDev model roundedLeft roundedRight -
            (roundedLeft + roundedRight)) +
          ((roundedLeft - exactLeft) + (roundedRight - exactRight))‖ := by
      ring_nf
    _ ≤ ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
            (roundedLeft + roundedRight)‖ +
          ‖(roundedLeft - exactLeft) + (roundedRight - exactRight)‖ :=
      norm_add_le _ _
    _ ≤ model.epsilon * (‖roundedLeft‖ + ‖roundedRight‖) +
          (‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖) :=
      add_le_add hfinal (norm_add_le _ _)
    _ ≤ model.epsilon * ((1 + model.epsilon) * inputL1) +
          model.epsilon * inputL1 :=
      add_le_add (mul_le_mul_of_nonneg_left hroundedNorm hε) hpair
    _ = (2 * model.epsilon + model.epsilon ^ 2) * inputL1 := by ring

private noncomputable def p09RoundedRadixFourBlockBalancedDev
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) : ℂ :=
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  p09RoundedBalancedFourSumDev model fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))

private lemma p09_norm_roundedRadixFourBlockBalanced_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlockBalancedDev model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  have h := p09_norm_roundedBalancedFourSum_sub_sum_le model term
  have hexact : (∑ i : Fin 4, term i) =
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j := by
    calc
      (∑ i : Fin 4, term i) =
          ∑ i : Fin 4, ZMod.stdAddChar (index i * k) * x (index i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact p09RadixFourCoefficientApply_eq _ _
      _ = ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j :=
        Fintype.sum_equiv index
          (fun i : Fin 4 ↦ ZMod.stdAddChar (index i * k) * x (index i))
          (fun j : ZMod 4 ↦ ZMod.stdAddChar (j * k) * x j) (fun _ ↦ rfl)
  have hnorm : (∑ i : Fin 4, ‖term i‖) = ∑ j : ZMod 4, ‖x j‖ := by
    calc
      (∑ i : Fin 4, ‖term i‖) = ∑ i : Fin 4, ‖x (index i)‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        unfold term
        rw [p09RadixFourCoefficientApply_eq]
        simp
      _ = ∑ j : ZMod 4, ‖x j‖ :=
        Fintype.sum_equiv index
          (fun i : Fin 4 ↦ ‖x (index i)‖)
          (fun j : ZMod 4 ↦ ‖x j‖) (fun _ ↦ rfl)
  change ‖p09RoundedBalancedFourSumDev model term -
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) *
      ∑ j : ZMod 4, ‖x j‖
  rw [← hexact, ← hnorm]
  exact h

private lemma p09_norm_roundedRadixFourBlock_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  simpa [p09RoundedRadixFourBlock,
    p09RoundedRadixFourBlockBalancedDev,
    p09RoundedBalancedFourSumDev, p09RoundedComplexAdd,
    p09RoundedComplexAddDev] using
      p09_norm_roundedRadixFourBlockBalanced_sub_exact_le model x k

private lemma p09ComplexNorm2_block_le_of_coordinate_bound
    {n q blockCount : ℕ} [NeZero n] [NeZero q]
    (reindex : Fin blockCount × ZMod q ≃ ZMod n)
    (x error : ZMod n → ℂ) {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hcoord : ∀ (block : Fin blockCount) (k : ZMod q),
      ‖error (reindex (block, k))‖ ≤
        coefficient * ∑ j : ZMod q, ‖x (reindex (block, j))‖) :
    p09ComplexNorm2 error ≤
      (q : ℝ) * coefficient * p09ComplexNorm2 x := by
  let blockL1 : Fin blockCount → ℝ := fun block ↦
    ∑ j : ZMod q, ‖x (reindex (block, j))‖
  have hblockL1 (block : Fin blockCount) : 0 ≤ blockL1 block :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hblock (block : Fin blockCount) :
      (∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
        ((q : ℝ) * coefficient) ^ 2 *
          ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
    have hcoordSq (k : ZMod q) :
        ‖error (reindex (block, k))‖ ^ 2 ≤
          (coefficient * blockL1 block) ^ 2 := by
      rw [sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hcoefficient (hblockL1 block))]
      exact hcoord block k
    have hL1Sq : (blockL1 block) ^ 2 ≤
        (q : ℝ) * ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
      simpa [blockL1] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (ZMod q)))
          (f := fun j : ZMod q ↦ ‖x (reindex (block, j))‖))
    calc
      (∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
          ∑ _k : ZMod q, (coefficient * blockL1 block) ^ 2 :=
        Finset.sum_le_sum fun k _hk ↦ hcoordSq k
      _ = (q : ℝ) * (coefficient * blockL1 block) ^ 2 := by simp
      _ ≤ (q : ℝ) * (coefficient ^ 2 *
            ((q : ℝ) *
              ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2)) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hL1Sq (sq_nonneg coefficient))
          (Nat.cast_nonneg _)
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by ring
  have herrReindex :
      (∑ i : ZMod n, ‖error i‖ ^ 2) =
        ∑ p : Fin blockCount × ZMod q, ‖error (reindex p)‖ ^ 2 := by
    symm
    exact Fintype.sum_equiv reindex
      (fun p : Fin blockCount × ZMod q ↦ ‖error (reindex p)‖ ^ 2)
      (fun i : ZMod n ↦ ‖error i‖ ^ 2) (fun _ ↦ rfl)
  have hxReindex :
      (∑ p : Fin blockCount × ZMod q, ‖x (reindex p)‖ ^ 2) =
        ∑ i : ZMod n, ‖x i‖ ^ 2 :=
    Fintype.sum_equiv reindex
      (fun p : Fin blockCount × ZMod q ↦ ‖x (reindex p)‖ ^ 2)
      (fun i : ZMod n ↦ ‖x i‖ ^ 2) (fun _ ↦ rfl)
  have hsq : p09ComplexNorm2Sq error ≤
      ((q : ℝ) * coefficient) ^ 2 * p09ComplexNorm2Sq x := by
    unfold p09ComplexNorm2Sq
    rw [herrReindex, Fintype.sum_prod_type]
    calc
      (∑ block : Fin blockCount,
          ∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
          ∑ block : Fin blockCount,
            (((q : ℝ) * coefficient) ^ 2 *
              ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2) :=
        Finset.sum_le_sum fun block _hblock ↦ hblock block
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ block : Fin blockCount,
            ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
        simp only [← Finset.mul_sum]
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ p : Fin blockCount × ZMod q, ‖x (reindex p)‖ ^ 2 := by
        rw [Fintype.sum_prod_type]
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ i : ZMod n, ‖x i‖ ^ 2 := by rw [hxReindex]
  have hqc : 0 ≤ (q : ℝ) * coefficient :=
    mul_nonneg (Nat.cast_nonneg _) hcoefficient
  unfold p09ComplexNorm2
  calc
    Real.sqrt (p09ComplexNorm2Sq error) ≤
        Real.sqrt (((q : ℝ) * coefficient) ^ 2 *
          p09ComplexNorm2Sq x) := Real.sqrt_le_sqrt hsq
    _ = ((q : ℝ) * coefficient) *
        Real.sqrt (p09ComplexNorm2Sq x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hqc]

private noncomputable def p09GenericBlockSecondOrder (q : ℕ) (γ : ℝ) : ℝ :=
  p09RecursiveSumSecondOrder q + (2 + 10 * γ) +
    ((q : ℝ) + p09RecursiveSumSecondOrder q) *
      ((3 + 2 * γ) + (2 + 10 * γ))

private lemma p09GenericBlockSecondOrder_nonneg (q : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09GenericBlockSecondOrder q γ := by
  unfold p09GenericBlockSecondOrder
  have hC := p09RecursiveSumSecondOrder_nonneg q
  have hB : 0 ≤ 2 + 10 * γ := by linarith
  have hqC : 0 ≤ (q : ℝ) + p09RecursiveSumSecondOrder q :=
    add_nonneg (Nat.cast_nonneg _) hC
  have hAB : 0 ≤ (3 + 2 * γ) + (2 + 10 * γ) := by linarith
  exact add_nonneg (add_nonneg hC hB) (mul_nonneg hqC hAB)

private lemma p09_norm_roundedGenericRadixBlock_sub_exact_le
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hq2 : q ≠ 2)
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 * ((q : ℝ) + model.gamma)) *
          (∑ j : ZMod q, ‖x j‖) +
        p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 *
          (∑ j : ZMod q, ‖x j‖) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hq3 : 3 ≤ q := by omega
  let computedTerm : ZMod q → ℂ := fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let exactTerm : ZMod q → ℂ := fun j ↦
    ZMod.stdAddChar (j * k) * x j
  let inputL1 : ℝ := ∑ j : ZMod q, ‖x j‖
  let termFirst : ℝ := 3 + 2 * model.gamma
  let termSecond : ℝ := 2 + 10 * model.gamma
  let termCoefficient : ℝ :=
    model.epsilon * termFirst + termSecond * model.epsilon ^ 2
  let sumCoefficient : ℝ :=
    (q : ℝ) * model.epsilon +
      p09RecursiveSumSecondOrder q * model.epsilon ^ 2
  have hinputL1 : 0 ≤ inputL1 := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have htermFirst : 0 ≤ termFirst := by unfold termFirst; positivity
  have htermSecond : 0 ≤ termSecond := by unfold termSecond; positivity
  have htermCoefficient : 0 ≤ termCoefficient := by
    unfold termCoefficient
    positivity
  have hsumCoefficient : 0 ≤ sumCoefficient := by
    unfold sumCoefficient
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
      (mul_nonneg (p09RecursiveSumSecondOrder_nonneg q) (sq_nonneg _))
  have hterm (j : ZMod q) :
      ‖computedTerm j - exactTerm j‖ ≤ termCoefficient * ‖x j‖ := by
    have h := p09_norm_roundedRootMul_sub_exact_le model (j * k) (x j) hεone
    rw [p09ExactRootDev_eq_stdAddChar] at h
    simpa [computedTerm, exactTerm, termCoefficient, termFirst, termSecond,
      add_mul] using h
  have htermSum :
      ‖(∑ j : ZMod q, computedTerm j) - ∑ j : ZMod q, exactTerm j‖ ≤
        termCoefficient * inputL1 := by
    calc
      ‖(∑ j : ZMod q, computedTerm j) - ∑ j : ZMod q, exactTerm j‖ =
          ‖∑ j : ZMod q, (computedTerm j - exactTerm j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j : ZMod q, ‖computedTerm j - exactTerm j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, termCoefficient * ‖x j‖ :=
        Finset.sum_le_sum fun j _hj ↦ hterm j
      _ = termCoefficient * inputL1 := by
        simp only [← Finset.mul_sum]
        rfl
  have hcomputedL1 :
      (∑ j : ZMod q, ‖computedTerm j‖) ≤
        (1 + termCoefficient) * inputL1 := by
    calc
      (∑ j : ZMod q, ‖computedTerm j‖) ≤
          ∑ j : ZMod q, (‖exactTerm j‖ + ‖computedTerm j - exactTerm j‖) := by
        apply Finset.sum_le_sum
        intro j _hj
        calc
          ‖computedTerm j‖ = ‖exactTerm j + (computedTerm j - exactTerm j)‖ := by
            ring_nf
          _ ≤ ‖exactTerm j‖ + ‖computedTerm j - exactTerm j‖ := norm_add_le _ _
      _ ≤ ∑ j : ZMod q, (‖x j‖ + termCoefficient * ‖x j‖) := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [show ‖exactTerm j‖ = ‖x j‖ by
          simp [exactTerm]]
        exact add_le_add le_rfl (hterm j)
      _ = (1 + termCoefficient) * inputL1 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        unfold inputL1
        ring
  have hsumRound :
      ‖p09RoundedComplexSum model computedTerm -
          ∑ j : ZMod q, computedTerm j‖ ≤
        sumCoefficient * ∑ j : ZMod q, ‖computedTerm j‖ := by
    simpa [sumCoefficient] using
      p09_norm_roundedComplexSum_sub_sum_le model computedTerm hεone
  have hcombined :
      ‖p09RoundedComplexSum model computedTerm - ∑ j : ZMod q, exactTerm j‖ ≤
        (sumCoefficient * (1 + termCoefficient) + termCoefficient) * inputL1 := by
    calc
      ‖p09RoundedComplexSum model computedTerm -
          ∑ j : ZMod q, exactTerm j‖ =
          ‖(p09RoundedComplexSum model computedTerm -
              ∑ j : ZMod q, computedTerm j) +
            ((∑ j : ZMod q, computedTerm j) -
              ∑ j : ZMod q, exactTerm j)‖ := by ring_nf
      _ ≤ ‖p09RoundedComplexSum model computedTerm -
              ∑ j : ZMod q, computedTerm j‖ +
            ‖(∑ j : ZMod q, computedTerm j) -
              ∑ j : ZMod q, exactTerm j‖ := norm_add_le _ _
      _ ≤ sumCoefficient * (∑ j : ZMod q, ‖computedTerm j‖) +
            termCoefficient * inputL1 := add_le_add hsumRound htermSum
      _ ≤ sumCoefficient * ((1 + termCoefficient) * inputL1) +
            termCoefficient * inputL1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcomputedL1 hsumCoefficient) le_rfl
      _ = (sumCoefficient * (1 + termCoefficient) + termCoefficient) *
            inputL1 := by ring
  have hepssq_le : model.epsilon ^ 2 ≤ model.epsilon := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεone)]
  have hsumLinear : sumCoefficient ≤
      model.epsilon * ((q : ℝ) + p09RecursiveSumSecondOrder q) := by
    unfold sumCoefficient
    have hC := p09RecursiveSumSecondOrder_nonneg q
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hepssq_le)]
  have htermLinear : termCoefficient ≤
      model.epsilon * (termFirst + termSecond) := by
    unfold termCoefficient
    nlinarith [mul_nonneg htermSecond (sub_nonneg.mpr hepssq_le)]
  have hproduct : sumCoefficient * termCoefficient ≤
      model.epsilon ^ 2 *
        (((q : ℝ) + p09RecursiveSumSecondOrder q) *
          (termFirst + termSecond)) := by
    calc
      sumCoefficient * termCoefficient ≤
          (model.epsilon * ((q : ℝ) + p09RecursiveSumSecondOrder q)) *
            (model.epsilon * (termFirst + termSecond)) := by
        exact mul_le_mul hsumLinear htermLinear htermCoefficient
          (mul_nonneg hε
            (add_nonneg (Nat.cast_nonneg _)
              (p09RecursiveSumSecondOrder_nonneg q)))
      _ = model.epsilon ^ 2 *
          (((q : ℝ) + p09RecursiveSumSecondOrder q) *
            (termFirst + termSecond)) := by ring
  have hcoefficient :
      sumCoefficient * (1 + termCoefficient) + termCoefficient ≤
        model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
          p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 := by
    have hfirst : (q : ℝ) + termFirst ≤ 2 * ((q : ℝ) + model.gamma) := by
      unfold termFirst
      have hq3r : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      linarith
    unfold sumCoefficient termCoefficient p09GenericBlockSecondOrder at *
    nlinarith
  change ‖p09RoundedComplexSum model computedTerm -
      ∑ j : ZMod q, exactTerm j‖ ≤ _
  calc
    ‖p09RoundedComplexSum model computedTerm -
        ∑ j : ZMod q, exactTerm j‖ ≤
        (sumCoefficient * (1 + termCoefficient) + termCoefficient) *
          inputL1 := hcombined
    _ ≤ (model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
          p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2) *
          inputL1 := mul_le_mul_of_nonneg_right hcoefficient hinputL1
    _ = model.epsilon * (2 * ((q : ℝ) + model.gamma)) * inputL1 +
        p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 *
          inputL1 := by ring

private noncomputable def p09BlockCoordinateSecondOrder
    (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 0
  else if q = 4 then 1
  else p09GenericBlockSecondOrder q γ

private lemma p09StdAddChar_ringEquivCongr {a b : ℕ} [NeZero a] [NeZero b]
    (h : a = b) (j : ZMod a) :
    ZMod.stdAddChar (ZMod.ringEquivCongr h j) = ZMod.stdAddChar j := by
  subst b
  rw [ZMod.ringEquivCongr_refl_apply]

private lemma p09_ringEquivCongr_apply_eq_transport {a b : ℕ}
    (h : a = b) (j : ZMod a) :
    ZMod.ringEquivCongr h j = h ▸ j := by
  subst b
  rw [ZMod.ringEquivCongr_refl_apply]

private lemma p09_ringEquivCongr_symm_apply_eq_transport {a b : ℕ}
    (h : a = b) (j : ZMod b) :
    (ZMod.ringEquivCongr h).symm j = h.symm ▸ j := by
  rw [ZMod.ringEquivCongr_symm]
  exact p09_ringEquivCongr_apply_eq_transport h.symm j

private lemma p09_block_coordinate_error_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (block : Fin stage.blockCount) (k : ZMod stage.radix)
    (hεone : model.epsilon ≤ 1) :
    ‖(p09RoundedMixedRadixBlockApply model stage x
          (stage.reindex (block, k)) -
        p09MixedRadixBlockApply stage x (stage.reindex (block, k)))‖ ≤
      (model.epsilon *
          (if stage.radix = 2 then 1
            else if stage.radix = 4 then 2
            else 2 * ((stage.radix : ℝ) + model.gamma)) +
        p09BlockCoordinateSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2) *
        ∑ j : ZMod stage.radix,
          ‖x (stage.permutation (stage.reindex (block, j)))‖ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  by_cases h2 : stage.radix = 2
  · let e2 : ZMod stage.radix ≃+* ZMod 2 := ZMod.ringEquivCongr h2
    let x2 : ZMod 2 → ℂ := fun j ↦
      permuted (stage.reindex (block, e2.symm j))
    let k2 : ZMod 2 := e2 k
    have h := p09_norm_roundedRadixTwoBlock_sub_exact_le model x2 k2
    have hsumExact :
        (∑ j : ZMod stage.radix,
            ZMod.stdAddChar (j * k) * permuted (stage.reindex (block, j))) =
          ∑ j : ZMod 2, ZMod.stdAddChar (j * k2) * x2 j := by
      apply Fintype.sum_equiv e2.toEquiv
      intro j
      simp [e2, k2, x2, ← map_mul, p09StdAddChar_ringEquivCongr]
    have hsumNorm :
        (∑ j : ZMod stage.radix,
          ‖permuted (stage.reindex (block, j))‖) =
            ∑ j : ZMod 2, ‖x2 j‖ := by
      apply Fintype.sum_equiv e2.toEquiv
      intro j
      simp [e2, x2]
    rw [← hsumExact, ← hsumNorm] at h
    simpa [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
      p09ComplexVecSub, h2, permuted, e2, x2, k2,
      p09BlockCoordinateSecondOrder,
      p09_ringEquivCongr_apply_eq_transport,
      p09_ringEquivCongr_symm_apply_eq_transport] using h
  · by_cases h4 : stage.radix = 4
    · let e4 : ZMod stage.radix ≃+* ZMod 4 := ZMod.ringEquivCongr h4
      let x4 : ZMod 4 → ℂ := fun j ↦
        permuted (stage.reindex (block, e4.symm j))
      let k4 : ZMod 4 := e4 k
      have h := p09_norm_roundedRadixFourBlock_sub_exact_le model x4 k4
      have hsumExact :
          (∑ j : ZMod stage.radix,
              ZMod.stdAddChar (j * k) * permuted (stage.reindex (block, j))) =
            ∑ j : ZMod 4, ZMod.stdAddChar (j * k4) * x4 j := by
        apply Fintype.sum_equiv e4.toEquiv
        intro j
        simp [e4, k4, x4, ← map_mul, p09StdAddChar_ringEquivCongr]
      have hsumNorm :
          (∑ j : ZMod stage.radix,
            ‖permuted (stage.reindex (block, j))‖) =
              ∑ j : ZMod 4, ‖x4 j‖ := by
        apply Fintype.sum_equiv e4.toEquiv
        intro j
        simp [e4, x4]
      rw [← hsumExact, ← hsumNorm] at h
      convert h using 1 <;>
        simp [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
          p09ComplexVecSub, h2, h4, permuted, e4, x4, k4,
          p09BlockCoordinateSecondOrder, add_mul,
          p09_ringEquivCongr_apply_eq_transport,
          p09_ringEquivCongr_symm_apply_eq_transport] <;> ring <;> simp
    · have h := p09_norm_roundedGenericRadixBlock_sub_exact_le
        stage.radix_two_le h2 model
          (fun j ↦ permuted (stage.reindex (block, j))) k hεone
      simpa [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
        p09ComplexVecSub, h2, h4, permuted,
        p09BlockCoordinateSecondOrder, add_mul] using h

private lemma p09ComplexNorm2_comp_equiv {n : ℕ} [NeZero n]
    (equiv : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x (equiv i)) = p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  congr 1
  exact Fintype.sum_equiv equiv
    (fun i : ZMod n ↦ ‖x (equiv i)‖ ^ 2)
    (fun i : ZMod n ↦ ‖x i‖ ^ 2) (fun _ ↦ rfl)

private noncomputable def p09BlockVectorSecondOrder (q : ℕ) (γ : ℝ) : ℝ :=
  (q : ℝ) * p09BlockCoordinateSecondOrder q γ

private lemma p09BlockVectorSecondOrder_nonneg (q : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09BlockVectorSecondOrder q γ := by
  unfold p09BlockVectorSecondOrder p09BlockCoordinateSecondOrder
  split_ifs
  · norm_num
  · norm_num
  · exact mul_nonneg (Nat.cast_nonneg _)
      (p09GenericBlockSecondOrder_nonneg q hγ)

private lemma p09_radix_first_coefficient_le (q : ℕ) (hq : 2 ≤ q)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (q : ℝ) *
        (if q = 2 then 1 else if q = 4 then 2 else 2 * ((q : ℝ) + γ)) ≤
      Real.sqrt (q : ℝ) * p09Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    have hsqrt : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num)
    simp [p09Alpha, hsqrt]
  · by_cases h4 : q = 4
    · subst q
      norm_num [p09Alpha]
    · have hsqrt : Real.sqrt (q : ℝ) * Real.sqrt q = q :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      simp only [p09Alpha, if_neg h2, if_neg h4]
      nlinarith [mul_nonneg (Nat.cast_nonneg q)
        (add_nonneg (Nat.cast_nonneg q) hγ)]

private lemma p09_norm_roundedMixedRadixBlock_sub_exact_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2
        (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
          (p09MixedRadixBlockApply stage x)) ≤
      model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 x +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 x := by
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  let coordinateCoefficient : ℝ :=
    model.epsilon *
        (if stage.radix = 2 then 1
          else if stage.radix = 4 then 2
          else 2 * ((stage.radix : ℝ) + model.gamma)) +
      p09BlockCoordinateSecondOrder stage.radix model.gamma * model.epsilon ^ 2
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoordSecond :
      0 ≤ p09BlockCoordinateSecondOrder stage.radix model.gamma := by
    unfold p09BlockCoordinateSecondOrder
    split_ifs
    · norm_num
    · norm_num
    · exact p09GenericBlockSecondOrder_nonneg _ model.gamma_nonneg
  have hfirstCoord :
      0 ≤ (if stage.radix = 2 then 1
        else if stage.radix = 4 then 2
          else 2 * ((stage.radix : ℝ) + model.gamma)) := by
    split_ifs
    · norm_num
    · norm_num
    · exact mul_nonneg (by norm_num)
        (add_nonneg (Nat.cast_nonneg _) model.gamma_nonneg)
  have hcoordinateCoefficient : 0 ≤ coordinateCoefficient :=
    add_nonneg (mul_nonneg hε hfirstCoord)
      (mul_nonneg hcoordSecond (sq_nonneg _))
  have hlift := p09ComplexNorm2_block_le_of_coordinate_bound
    stage.reindex permuted
    (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
      (p09MixedRadixBlockApply stage x))
    hcoordinateCoefficient (fun block k ↦ by
      simpa [permuted, p09ComplexVecSub, coordinateCoefficient] using
        p09_block_coordinate_error_le model stage x block k hεone)
  rw [p09ComplexNorm2_comp_equiv stage.permutation x] at hlift
  have hfirst := p09_radix_first_coefficient_le stage.radix
    stage.radix_two_le model.gamma model.gamma_nonneg
  have hnorm : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
  calc
    p09ComplexNorm2
        (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
          (p09MixedRadixBlockApply stage x)) ≤
        (stage.radix : ℝ) * coordinateCoefficient * p09ComplexNorm2 x :=
      hlift
    _ = ((stage.radix : ℝ) *
          (if stage.radix = 2 then 1
            else if stage.radix = 4 then 2
            else 2 * ((stage.radix : ℝ) + model.gamma)) * model.epsilon +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2) * p09ComplexNorm2 x := by
      unfold coordinateCoefficient p09BlockVectorSecondOrder
      ring
    _ ≤ (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma *
            model.epsilon +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2) * p09ComplexNorm2 x := by
      apply mul_le_mul_of_nonneg_right _ hnorm
      exact add_le_add (mul_le_mul_of_nonneg_right hfirst hε) le_rfl
    _ = model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 x +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 x := by ring

private lemma p09ComplexNorm2_permute {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09Permute permutation x) = p09ComplexNorm2 x := by
  exact p09ComplexNorm2_comp_equiv permutation x

private lemma p09ComplexNorm2_exactTwiddle {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) =
      p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [p09MixedRadixTwiddleApply]
  split_ifs <;> simp

/-- Norm amplification of the exact FFT factors remaining after stage `k`. -/
private noncomputable def p09ExactCompletionScale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) : ℝ :=
  ((List.ofFn plan.stage).drop k).foldr
    (fun stage scale ↦ Real.sqrt (stage.radix : ℝ) * scale) 1

private lemma p09ExactCompletionScale_final {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09ExactCompletionScale plan plan.stageCount = 1 := by
  unfold p09ExactCompletionScale
  rw [List.drop_eq_nil_of_le]
  · rfl
  · simp

private lemma p09ExactCompletionScale_step {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k < plan.stageCount) :
    p09ExactCompletionScale plan k =
      Real.sqrt ((plan.stage ⟨k, hk⟩).radix : ℝ) *
        p09ExactCompletionScale plan (k + 1) := by
  unfold p09ExactCompletionScale
  have hlength : k < (List.ofFn plan.stage).length := by simpa using hk
  rw [List.drop_eq_getElem_cons hlength]
  simp

private lemma p09ExactCompletionScale_pos {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k ≤ plan.stageCount) :
    0 < p09ExactCompletionScale plan k := by
  induction hk using Nat.decreasingInduction with
  | self => rw [p09ExactCompletionScale_final]; norm_num
  | of_succ k hk ih =>
      rw [p09ExactCompletionScale_step plan k hk]
      exact mul_pos
        (Real.sqrt_pos.2 (Nat.cast_pos.2
          (lt_of_lt_of_le (by norm_num) (plan.stage ⟨k, hk⟩).radix_two_le)))
        ih

private lemma p09ComplexNorm2_exactCompletion {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k ≤ plan.stageCount) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactFftCompletion plan k x) =
      p09ExactCompletionScale plan k * p09ComplexNorm2 x := by
  revert x
  induction hk using Nat.decreasingInduction with
  | self =>
      intro x
      rw [p09ExactFftCompletion_final, p09ExactCompletionScale_final,
        p09ComplexNorm2_permute]
      simp
  | of_succ k hk ih =>
      intro x
      rw [p09ExactFftCompletion_step_input plan k hk, ih,
        plan.stage_norm_scaling, p09ExactCompletionScale_step plan k hk]
      ring

private lemma p09ExactFftCompletion_zero {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ExactFftCompletion plan 0 x = p09FourierTransform x := by
  unfold p09ExactFftCompletion p09ApplyExactStageList
  simp only [List.drop_zero]
  simpa [p09ApplyMixedRadixStages] using plan.exact_factorization x

private lemma p09ComplexNorm2_fourier {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
  have h := plan.fourier_rms_scaling x
  unfold p09ComplexRms at h
  field_simp [hsqrt] at h
  exact h

private lemma p09ComplexNorm2_le_mul_of_coordinate_bound
    {n : ℕ} [NeZero n] (x error : ZMod n → ℂ) {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hcoord : ∀ i, ‖error i‖ ≤ coefficient * ‖x i‖) :
    p09ComplexNorm2 error ≤ coefficient * p09ComplexNorm2 x := by
  have hsq : p09ComplexNorm2Sq error ≤
      coefficient ^ 2 * p09ComplexNorm2Sq x := by
    unfold p09ComplexNorm2Sq
    calc
      (∑ i : ZMod n, ‖error i‖ ^ 2) ≤
          ∑ i : ZMod n, (coefficient * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoefficient (norm_nonneg _))]
        exact hcoord i
      _ = coefficient ^ 2 * ∑ i : ZMod n, ‖x i‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
  unfold p09ComplexNorm2
  calc
    Real.sqrt (p09ComplexNorm2Sq error) ≤
        Real.sqrt (coefficient ^ 2 * p09ComplexNorm2Sq x) :=
      Real.sqrt_le_sqrt hsq
    _ = coefficient * Real.sqrt (p09ComplexNorm2Sq x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hcoefficient]

private noncomputable def p09TwiddleVectorSecondOrder
    {n : ℕ} [NeZero n] (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 2 + 10 * γ else 0

private lemma p09TwiddleVectorSecondOrder_nonneg
    {n : ℕ} [NeZero n] (stage : P09MixedRadixStage n) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09TwiddleVectorSecondOrder stage γ := by
  unfold p09TwiddleVectorSecondOrder
  split_ifs
  · positivity
  · norm_num

private lemma p09_norm_roundedMixedRadixTwiddle_sub_exact_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2
        (p09ComplexVecSub
          (p09RoundedMixedRadixTwiddleApply model stage x)
          (p09MixedRadixTwiddleApply stage x)) ≤
      (model.epsilon *
          (if stage.useTwiddle then 3 + 2 * model.gamma else 0) +
        p09TwiddleVectorSecondOrder stage model.gamma * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  by_cases htwiddle : stage.useTwiddle = true
  · have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    have hfirst : 0 ≤ 3 + 2 * model.gamma := by
      nlinarith [model.gamma_nonneg]
    have hsecond :
        0 ≤ p09TwiddleVectorSecondOrder stage model.gamma :=
      p09TwiddleVectorSecondOrder_nonneg stage model.gamma_nonneg
    simp only [htwiddle, if_true]
    apply p09ComplexNorm2_le_mul_of_coordinate_bound
      (x := x)
      (error := p09ComplexVecSub
        (p09RoundedMixedRadixTwiddleApply model stage x)
        (p09MixedRadixTwiddleApply stage x))
      (coefficient := model.epsilon * (3 + 2 * model.gamma) +
        p09TwiddleVectorSecondOrder stage model.gamma * model.epsilon ^ 2)
      (add_nonneg (mul_nonneg hε hfirst)
        (mul_nonneg hsecond (sq_nonneg model.epsilon)))
    intro i
    convert p09_norm_roundedRootMul_sub_exact_le model
        (stage.twiddleExponent i) (x i) hεone using 1 <;>
      simp [p09RoundedMixedRadixTwiddleApply,
        p09MixedRadixTwiddleApply, p09ComplexVecSub,
        p09TwiddleVectorSecondOrder, htwiddle,
        p09ExactRootDev_eq_stdAddChar] <;> ring
  · have hfalse : stage.useTwiddle = false := Bool.eq_false_of_not_eq_true htwiddle
    simp [p09RoundedMixedRadixTwiddleApply,
      p09MixedRadixTwiddleApply, p09ComplexVecSub,
      p09TwiddleVectorSecondOrder, hfalse,
      p09ComplexNorm2, p09ComplexNorm2Sq]

private lemma p09Alpha_nonneg (q : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09Alpha q γ := by
  unfold p09Alpha
  split_ifs
  · exact Real.sqrt_nonneg _
  · norm_num
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (add_nonneg (Nat.cast_nonneg _) hγ)

private lemma p09TwiddleFirstOrderBudget_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09TwiddleFirstOrderBudget plan γ i := by
  unfold p09TwiddleFirstOrderBudget
  split_ifs
  · nlinarith
  · norm_num

private noncomputable def p09TwiddlePropagatedSecondOrder
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  let first := p09TwiddleFirstOrderBudget plan γ i
  let twiddleSecond := p09TwiddleVectorSecondOrder (plan.stage i) γ
  let alpha := p09Alpha (plan.stage i).radix γ
  let blockSecond := p09BlockVectorSecondOrder (plan.stage i).radix γ
  twiddleSecond + (first + twiddleSecond) * (alpha + blockSecond)

private lemma p09TwiddlePropagatedSecondOrder_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09TwiddlePropagatedSecondOrder plan γ i := by
  unfold p09TwiddlePropagatedSecondOrder
  exact add_nonneg
    (p09TwiddleVectorSecondOrder_nonneg (plan.stage i) hγ)
    (mul_nonneg
      (add_nonneg (p09TwiddleFirstOrderBudget_nonneg plan hγ i)
        (p09TwiddleVectorSecondOrder_nonneg (plan.stage i) hγ))
      (add_nonneg (p09Alpha_nonneg _ hγ)
        (p09BlockVectorSecondOrder_nonneg _ hγ)))

private noncomputable def p09StagePropagatedSecondOrder
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  p09BlockVectorSecondOrder (plan.stage i).radix γ +
    p09TwiddlePropagatedSecondOrder plan γ i

private lemma p09StagePropagatedSecondOrder_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09StagePropagatedSecondOrder plan γ i :=
  add_nonneg (p09BlockVectorSecondOrder_nonneg _ hγ)
    (p09TwiddlePropagatedSecondOrder_nonneg plan hγ i)

private noncomputable def p09CompletedStateNorm
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (k : ℕ) : ℝ :=
  p09ComplexNorm2 (p09ExactFftCompletion plan k (run.stageState k))

private lemma p09_norm_propagatedFftBlockError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftBlockError run i) ≤
      model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
          p09CompletedStateNorm run i.val +
        p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let localError := p09ComplexVecSub
    (p09RoundedMixedRadixBlockApply model stage state)
    (p09MixedRadixBlockApply stage state)
  have hi : i.val ≤ plan.stageCount := Nat.le_of_lt i.isLt
  have hisucc : i.val + 1 ≤ plan.stageCount := Nat.succ_le_of_lt i.isLt
  have hscaleNonneg : 0 ≤ p09ExactCompletionScale plan (i.val + 1) :=
    (p09ExactCompletionScale_pos plan _ hisucc).le
  have hnormState : 0 ≤ p09ComplexNorm2 state := Real.sqrt_nonneg _
  have hsqrtOne : 1 ≤ Real.sqrt ((plan.stage i).radix : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) stage.radix_two_le)
  have hlocal : p09ComplexNorm2 localError ≤
      model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 state := by
    exact p09_norm_roundedMixedRadixBlock_sub_exact_le model stage state hεone
  have hshortScale :
      p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 state ≤
        p09ExactCompletionScale plan i.val * p09ComplexNorm2 state := by
    rw [p09ExactCompletionScale_step plan i.val i.isLt]
    apply mul_le_mul_of_nonneg_right _ hnormState
    calc
      p09ExactCompletionScale plan (i.val + 1) =
          1 * p09ExactCompletionScale plan (i.val + 1) := by ring
      _ ≤ Real.sqrt ((plan.stage ⟨i.val, i.isLt⟩).radix : ℝ) *
          p09ExactCompletionScale plan (i.val + 1) := by
        apply mul_le_mul_of_nonneg_right _ hscaleNonneg
        simpa using hsqrtOne
  calc
    p09ComplexNorm2 (p09PropagatedFftBlockError run i) =
        p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 localError := by
      unfold p09PropagatedFftBlockError p09FftStageBlockLocalError
        p09FftStageRoundedBlock localError stage state
      rw [p09ComplexNorm2_exactCompletion plan _ hisucc,
        p09ComplexNorm2_exactTwiddle]
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2 * p09ComplexNorm2 state) :=
      mul_le_mul_of_nonneg_left hlocal hscaleNonneg
    _ = model.epsilon * p09Alpha stage.radix model.gamma *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) +
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
          (p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 state) := by
      rw [p09ExactCompletionScale_step plan i.val i.isLt]
      ring
    _ ≤ model.epsilon * p09Alpha stage.radix model.gamma *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) +
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hshortScale
          (mul_nonneg
            (p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg)
            (sq_nonneg _)))
    _ = model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
          p09CompletedStateNorm run i.val +
        p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09CompletedStateNorm stage state
      rw [p09ComplexNorm2_exactCompletion plan i.val hi]

private lemma p09_norm_roundedFftStageBlock_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09FftStageRoundedBlock run i) ≤
      Real.sqrt ((plan.stage i).radix : ℝ) *
        (1 + model.epsilon * p09Alpha (plan.stage i).radix model.gamma +
          model.epsilon ^ 2 *
            p09BlockVectorSecondOrder (plan.stage i).radix model.gamma) *
        p09ComplexNorm2 (run.stageState i.val) := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let exactBlock := p09MixedRadixBlockApply stage state
  let localError := p09ComplexVecSub
    (p09RoundedMixedRadixBlockApply model stage state) exactBlock
  have hdecomp : p09FftStageRoundedBlock run i =
      p09ComplexVecAdd exactBlock localError := by
    change p09RoundedMixedRadixBlockApply model stage state =
      p09ComplexVecAdd exactBlock localError
    funext j
    simp [exactBlock, localError, p09ComplexVecAdd, p09ComplexVecSub]
  have hexact : p09ComplexNorm2 exactBlock =
      Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state := by
    have h := plan.stage_norm_scaling i state
    unfold p09MixedRadixStageApply at h
    rw [p09ComplexNorm2_exactTwiddle] at h
    exact h
  have hlocal := p09_norm_roundedMixedRadixBlock_sub_exact_le
    model stage state hεone
  have hsqrtOne : 1 ≤ Real.sqrt (stage.radix : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) stage.radix_two_le)
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hsecond : 0 ≤ p09BlockVectorSecondOrder stage.radix model.gamma :=
    p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg
  rw [hdecomp]
  calc
    p09ComplexNorm2 (p09ComplexVecAdd exactBlock localError) ≤
        p09ComplexNorm2 exactBlock + p09ComplexNorm2 localError :=
      p09ComplexNorm2_add_le _ _
    _ ≤ Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state +
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2 * p09ComplexNorm2 state) := by
      rw [hexact]
      exact add_le_add le_rfl hlocal
    _ ≤ Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state +
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          Real.sqrt (stage.radix : ℝ) *
            (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state)) := by
      apply add_le_add le_rfl
      apply add_le_add le_rfl
      calc
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
            p09ComplexNorm2 state =
            1 * (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state) := by ring
        _ ≤ Real.sqrt (stage.radix : ℝ) *
            (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state) := by
          exact mul_le_mul_of_nonneg_right hsqrtOne
            (mul_nonneg (mul_nonneg hsecond (sq_nonneg _))
              (Real.sqrt_nonneg _))
    _ = Real.sqrt ((plan.stage i).radix : ℝ) *
        (1 + model.epsilon * p09Alpha (plan.stage i).radix model.gamma +
          model.epsilon ^ 2 *
            p09BlockVectorSecondOrder (plan.stage i).radix model.gamma) *
        p09ComplexNorm2 (run.stageState i.val) := by
      unfold stage state
      ring

private lemma p09_norm_propagatedFftTwiddleError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) ≤
      model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09TwiddlePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let roundedBlock := p09FftStageRoundedBlock run i
  let first := p09TwiddleFirstOrderBudget plan model.gamma i
  let twiddleSecond := p09TwiddleVectorSecondOrder stage model.gamma
  let alpha := p09Alpha stage.radix model.gamma
  let blockSecond := p09BlockVectorSecondOrder stage.radix model.gamma
  let propagatedSecond := p09TwiddlePropagatedSecondOrder plan model.gamma i
  have hi : i.val ≤ plan.stageCount := Nat.le_of_lt i.isLt
  have hisucc : i.val + 1 ≤ plan.stageCount := Nat.succ_le_of_lt i.isLt
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hεsqone : model.epsilon ^ 2 ≤ 1 := by nlinarith [sq_nonneg model.epsilon]
  have hscale : 0 ≤ p09ExactCompletionScale plan (i.val + 1) :=
    (p09ExactCompletionScale_pos plan _ hisucc).le
  have hstate : 0 ≤ p09ComplexNorm2 state := Real.sqrt_nonneg _
  have hfirst : 0 ≤ first :=
    p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i
  have htwiddleSecond : 0 ≤ twiddleSecond :=
    p09TwiddleVectorSecondOrder_nonneg stage model.gamma_nonneg
  have halpha : 0 ≤ alpha := p09Alpha_nonneg _ model.gamma_nonneg
  have hblockSecond : 0 ≤ blockSecond :=
    p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg
  have hcoefficient : 0 ≤
      model.epsilon * first + twiddleSecond * model.epsilon ^ 2 :=
    add_nonneg (mul_nonneg hε hfirst)
      (mul_nonneg htwiddleSecond (sq_nonneg _))
  have hlocal :
      p09ComplexNorm2 (p09FftStageTwiddleLocalError run i) ≤
        (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          p09ComplexNorm2 roundedBlock := by
    simpa [p09FftStageTwiddleLocalError, roundedBlock, stage, first,
      twiddleSecond, p09TwiddleFirstOrderBudget] using
      p09_norm_roundedMixedRadixTwiddle_sub_exact_le model stage roundedBlock hεone
  have hrounded : p09ComplexNorm2 roundedBlock ≤
      Real.sqrt (stage.radix : ℝ) *
        (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) *
        p09ComplexNorm2 state := by
    simpa [roundedBlock, stage, state, alpha, blockSecond] using
      p09_norm_roundedFftStageBlock_le run i hεone
  have hpoly :
      (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) ≤
        model.epsilon * first + propagatedSecond * model.epsilon ^ 2 := by
    have h₁ : model.epsilon * first * blockSecond ≤
        first * blockSecond := by
      calc
        model.epsilon * first * blockSecond ≤ 1 * first * blockSecond := by
          gcongr
        _ = first * blockSecond := by ring
    have h₂ : model.epsilon * twiddleSecond * alpha ≤
        twiddleSecond * alpha := by
      calc
        model.epsilon * twiddleSecond * alpha ≤
            1 * twiddleSecond * alpha := by gcongr
        _ = twiddleSecond * alpha := by ring
    have h₃ : model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
        twiddleSecond * blockSecond := by
      calc
        model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
            1 * twiddleSecond * blockSecond := by gcongr
        _ = twiddleSecond * blockSecond := by ring
    rw [show (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) =
        model.epsilon * first + model.epsilon ^ 2 *
          (twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond) by ring]
    apply add_le_add le_rfl
    have hbracket :
        twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
          propagatedSecond := by
      unfold propagatedSecond p09TwiddlePropagatedSecondOrder
      dsimp only
      nlinarith
    calc
      model.epsilon ^ 2 *
          (twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond) ≤
          model.epsilon ^ 2 * propagatedSecond :=
        mul_le_mul_of_nonneg_left hbracket (sq_nonneg _)
      _ = propagatedSecond * model.epsilon ^ 2 := by ring
  calc
    p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) =
        p09ExactCompletionScale plan (i.val + 1) *
          p09ComplexNorm2 (p09FftStageTwiddleLocalError run i) := by
      unfold p09PropagatedFftTwiddleError
      rw [p09ComplexNorm2_exactCompletion plan _ hisucc]
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          p09ComplexNorm2 roundedBlock) :=
      mul_le_mul_of_nonneg_left hlocal hscale
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (Real.sqrt (stage.radix : ℝ) *
            (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) *
            p09ComplexNorm2 state)) := by
      gcongr
    _ = ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond)) *
        (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      rw [p09ExactCompletionScale_step plan i.val i.isLt]
      ring
    _ ≤ (model.epsilon * first + propagatedSecond * model.epsilon ^ 2) *
        (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      exact mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg (p09ExactCompletionScale_pos plan _ hi).le hstate)
    _ = model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09TwiddlePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09CompletedStateNorm first propagatedSecond state
      rw [p09ComplexNorm2_exactCompletion plan i.val hi]
      ring

private lemma p09_norm_propagatedFftStageError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftStageError run i) ≤
      model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09StagePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  rw [p09PropagatedFftStageError_eq_block_add_twiddle]
  calc
    p09ComplexNorm2
        (p09ComplexVecAdd (p09PropagatedFftBlockError run i)
          (p09PropagatedFftTwiddleError run i)) ≤
        p09ComplexNorm2 (p09PropagatedFftBlockError run i) +
          p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) :=
      p09ComplexNorm2_add_le _ _
    _ ≤ (model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
            p09CompletedStateNorm run i.val +
          p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
            model.epsilon ^ 2 * p09CompletedStateNorm run i.val) +
        (model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
            p09CompletedStateNorm run i.val +
          p09TwiddlePropagatedSecondOrder plan model.gamma i *
            model.epsilon ^ 2 * p09CompletedStateNorm run i.val) :=
      add_le_add (p09_norm_propagatedFftBlockError_le run i hεone)
        (p09_norm_propagatedFftTwiddleError_le run i hεone)
    _ = model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09StagePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09StageFirstOrderBudget p09StagePropagatedSecondOrder
      ring

private lemma p09CompletedStateNorm_step_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09CompletedStateNorm run (i.val + 1) ≤
      (1 + model.epsilon * p09StageFirstOrderBudget plan model.gamma i +
        model.epsilon ^ 2 * p09StagePropagatedSecondOrder plan model.gamma i) *
        p09CompletedStateNorm run i.val := by
  have hstep := p09ExactFftCompletion_run_step run i.val i.isLt
  unfold p09CompletedStateNorm
  rw [hstep]
  calc
    p09ComplexNorm2
        (p09ComplexVecAdd
          (p09ExactFftCompletion plan i.val (run.stageState i.val))
          (p09PropagatedFftStageError run i)) ≤
        p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
          p09ComplexNorm2 (p09PropagatedFftStageError run i) :=
      p09ComplexNorm2_add_le _ _
    _ ≤ p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
        (model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
            p09ComplexNorm2
              (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
          p09StagePropagatedSecondOrder plan model.gamma i *
            model.epsilon ^ 2 *
              p09ComplexNorm2
                (p09ExactFftCompletion plan i.val (run.stageState i.val))) := by
      simpa [p09CompletedStateNorm] using
        (add_le_add_right (p09_norm_propagatedFftStageError_le run i hεone)
          (p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val))))
    _ = (1 + model.epsilon * p09StageFirstOrderBudget plan model.gamma i +
          model.epsilon ^ 2 * p09StagePropagatedSecondOrder plan model.gamma i) *
        p09ComplexNorm2
          (p09ExactFftCompletion plan i.val (run.stageState i.val)) := by ring

private noncomputable def p09StageEnvelopeNat
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (k : ℕ) : ℝ :=
  if hk : k < plan.stageCount then
    p09StageFirstOrderBudget plan γ ⟨k, hk⟩ +
      p09StagePropagatedSecondOrder plan γ ⟨k, hk⟩
  else 0

private lemma p09StageEnvelopeNat_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (k : ℕ) :
    0 ≤ p09StageEnvelopeNat plan γ k := by
  unfold p09StageEnvelopeNat
  split_ifs with hk
  · exact add_nonneg
      (add_nonneg (p09Alpha_nonneg _ hγ)
        (p09TwiddleFirstOrderBudget_nonneg plan hγ ⟨k, hk⟩))
      (p09StagePropagatedSecondOrder_nonneg plan hγ ⟨k, hk⟩)
  · norm_num

private noncomputable def p09GrowthEnvelope
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      p09GrowthEnvelope plan γ k + p09StageEnvelopeNat plan γ k +
        p09GrowthEnvelope plan γ k * p09StageEnvelopeNat plan γ k

private lemma p09GrowthEnvelope_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (k : ℕ) :
    0 ≤ p09GrowthEnvelope plan γ k := by
  induction k with
  | zero => simp [p09GrowthEnvelope]
  | succ k ih =>
      rw [p09GrowthEnvelope]
      exact add_nonneg
        (add_nonneg ih (p09StageEnvelopeNat_nonneg plan hγ k))
        (mul_nonneg ih (p09StageEnvelopeNat_nonneg plan hγ k))

private lemma p09CompletedStateNorm_le_growth
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (hεone : model.epsilon ≤ 1) (k : ℕ) (hk : k ≤ plan.stageCount) :
    p09CompletedStateNorm run k ≤
      Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
        (1 + model.epsilon * p09GrowthEnvelope plan model.gamma k) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  induction k with
  | zero =>
      unfold p09CompletedStateNorm
      rw [run.initial_state, p09ExactFftCompletion_zero plan,
        p09ComplexNorm2_fourier plan]
      simp [p09GrowthEnvelope]
  | succ k ih =>
      have hklt : k < plan.stageCount := Nat.lt_of_succ_le hk
      let i : Fin plan.stageCount := ⟨k, hklt⟩
      let budget := p09StageFirstOrderBudget plan model.gamma i
      let second := p09StagePropagatedSecondOrder plan model.gamma i
      let envelope := p09StageEnvelopeNat plan model.gamma k
      let growth := p09GrowthEnvelope plan model.gamma k
      have hbudget : 0 ≤ budget := by
        unfold budget p09StageFirstOrderBudget
        exact add_nonneg (p09Alpha_nonneg _ model.gamma_nonneg)
          (p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i)
      have hsecond : 0 ≤ second :=
        p09StagePropagatedSecondOrder_nonneg plan model.gamma_nonneg i
      have henvelope : envelope = budget + second := by
        simp [envelope, budget, second, p09StageEnvelopeNat, i, hklt]
      have hgrowth : 0 ≤ growth :=
        p09GrowthEnvelope_nonneg plan model.gamma_nonneg k
      have hbase : 0 ≤
          Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hfactor : 0 ≤
          1 + model.epsilon * budget + model.epsilon ^ 2 * second := by
        positivity
      have hεsq_le : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [mul_nonneg hε
          (sub_nonneg.mpr hεone)]
      calc
        p09CompletedStateNorm run (k + 1) ≤
            (1 + model.epsilon * budget + model.epsilon ^ 2 * second) *
              p09CompletedStateNorm run k := by
          simpa [i, budget, second] using
            p09CompletedStateNorm_step_le run i hεone
        _ ≤ (1 + model.epsilon * budget + model.epsilon ^ 2 * second) *
            (Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
              (1 + model.epsilon * growth)) := by
          exact mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hklt)) hfactor
        _ ≤ (1 + model.epsilon * envelope) *
            (Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
              (1 + model.epsilon * growth)) := by
          apply mul_le_mul_of_nonneg_right
          · rw [henvelope]
            nlinarith [mul_le_mul_of_nonneg_right hεsq_le hsecond]
          · exact mul_nonneg hbase
              (add_nonneg (by norm_num) (mul_nonneg hε hgrowth))
        _ = Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            ((1 + model.epsilon * envelope) *
              (1 + model.epsilon * growth)) := by ring
        _ ≤ Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            (1 + model.epsilon *
              (growth + envelope + growth * envelope)) := by
          apply mul_le_mul_of_nonneg_left _ hbase
          have hcross : model.epsilon ^ 2 * (growth * envelope) ≤
              model.epsilon * (growth * envelope) :=
            mul_le_mul_of_nonneg_right hεsq_le
              (mul_nonneg hgrowth
                (p09StageEnvelopeNat_nonneg plan model.gamma_nonneg k))
          nlinarith
        _ = Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            (1 + model.epsilon * p09GrowthEnvelope plan model.gamma (k + 1)) := by
          rw [p09GrowthEnvelope]

private lemma p09ComplexRms_local_of_completed_bound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (k : ℕ) (hk : k ≤ plan.stageCount) (error : ZMod n → ℂ)
    (first second : ℝ) (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hεone : model.epsilon ≤ 1)
    (herror : p09ComplexNorm2 error ≤
      model.epsilon * first * p09CompletedStateNorm run k +
        second * model.epsilon ^ 2 * p09CompletedStateNorm run k) :
    p09ComplexRms error ≤
      model.epsilon * Real.sqrt (n : ℝ) * first *
          p09ComplexRms run.input +
        ((first * p09GrowthEnvelope plan model.gamma k +
            second * (1 + p09GrowthEnvelope plan model.gamma k)) *
          p09ComplexNorm2 run.input) * model.epsilon ^ 2 := by
  let growth := p09GrowthEnvelope plan model.gamma k
  let inputNorm := p09ComplexNorm2 run.input
  let base := Real.sqrt (n : ℝ) * inputNorm
  let remainder :=
    (first * growth + second * (1 + growth)) * inputNorm
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hgrowth : 0 ≤ growth :=
    p09GrowthEnvelope_nonneg plan model.gamma_nonneg k
  have hinput : 0 ≤ inputNorm := Real.sqrt_nonneg _
  have hbase : 0 ≤ base := mul_nonneg hsqrt.le hinput
  have hlocalCoefficient :
      0 ≤ model.epsilon * first + second * model.epsilon ^ 2 :=
    add_nonneg (mul_nonneg hε hfirst)
      (mul_nonneg hsecond (sq_nonneg _))
  have hgrowthFactor : 0 ≤ 1 + model.epsilon * growth :=
    add_nonneg (by norm_num) (mul_nonneg hε hgrowth)
  have hεsecondGrowth : model.epsilon * second * growth ≤
      second * growth := by
    calc
      model.epsilon * second * growth ≤ 1 * second * growth := by gcongr
      _ = second * growth := by ring
  have hpoly :
      (model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth) ≤
        model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second * (1 + growth)) := by
    rw [show (model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth) =
        model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second + model.epsilon * second * growth) by ring]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith
  have hgrowthBound := p09CompletedStateNorm_le_growth run hεone k hk
  have hnorm : p09ComplexNorm2 error ≤
      model.epsilon * Real.sqrt (n : ℝ) * first * inputNorm +
        Real.sqrt (n : ℝ) * remainder * model.epsilon ^ 2 := by
    calc
      p09ComplexNorm2 error ≤
          (model.epsilon * first + second * model.epsilon ^ 2) *
            p09CompletedStateNorm run k := by
        calc
          p09ComplexNorm2 error ≤
              model.epsilon * first * p09CompletedStateNorm run k +
                second * model.epsilon ^ 2 * p09CompletedStateNorm run k := herror
          _ = (model.epsilon * first + second * model.epsilon ^ 2) *
              p09CompletedStateNorm run k := by ring
      _ ≤ (model.epsilon * first + second * model.epsilon ^ 2) *
          (base * (1 + model.epsilon * growth)) := by
        simpa [base, growth, inputNorm] using
          mul_le_mul_of_nonneg_left hgrowthBound hlocalCoefficient
      _ = ((model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth)) * base := by ring
      _ ≤ (model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second * (1 + growth))) * base :=
        mul_le_mul_of_nonneg_right hpoly hbase
      _ = model.epsilon * Real.sqrt (n : ℝ) * first * inputNorm +
          Real.sqrt (n : ℝ) * remainder * model.epsilon ^ 2 := by
        unfold base remainder inputNorm
        ring
  unfold p09ComplexRms
  rw [div_le_iff₀ hsqrt]
  convert hnorm using 1 <;> unfold remainder inputNorm <;>
    field_simp [ne_of_gt hsqrt] <;> ring

private noncomputable def p09PrimitiveBlockSecondOrderCoeff
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (input : ZMod n → ℂ) (i : Fin plan.stageCount) : ℝ :=
  (p09Alpha (plan.stage i).radix γ * p09GrowthEnvelope plan γ i.val +
      p09BlockVectorSecondOrder (plan.stage i).radix γ *
        (1 + p09GrowthEnvelope plan γ i.val)) *
    p09ComplexNorm2 input

private noncomputable def p09PrimitiveTwiddleSecondOrderCoeff
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (input : ZMod n → ℂ) (i : Fin plan.stageCount) : ℝ :=
  (p09TwiddleFirstOrderBudget plan γ i *
        p09GrowthEnvelope plan γ i.val +
      p09TwiddlePropagatedSecondOrder plan γ i *
        (1 + p09GrowthEnvelope plan γ i.val)) *
    p09ComplexNorm2 input

private lemma p09PrimitiveBlockSecondOrderCoeff_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (input : ZMod n → ℂ) (i : Fin plan.stageCount) :
    0 ≤ p09PrimitiveBlockSecondOrderCoeff plan γ input i := by
  unfold p09PrimitiveBlockSecondOrderCoeff
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (p09Alpha_nonneg _ hγ)
        (p09GrowthEnvelope_nonneg plan hγ i.val))
      (mul_nonneg (p09BlockVectorSecondOrder_nonneg _ hγ)
        (add_nonneg (by norm_num)
          (p09GrowthEnvelope_nonneg plan hγ i.val))))
    (Real.sqrt_nonneg _)

private lemma p09PrimitiveTwiddleSecondOrderCoeff_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (input : ZMod n → ℂ) (i : Fin plan.stageCount) :
    0 ≤ p09PrimitiveTwiddleSecondOrderCoeff plan γ input i := by
  unfold p09PrimitiveTwiddleSecondOrderCoeff
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (p09TwiddleFirstOrderBudget_nonneg plan hγ i)
        (p09GrowthEnvelope_nonneg plan hγ i.val))
      (mul_nonneg (p09TwiddlePropagatedSecondOrder_nonneg plan hγ i)
        (add_nonneg (by norm_num)
          (p09GrowthEnvelope_nonneg plan hγ i.val))))
    (Real.sqrt_nonneg _)

private lemma p09PrimitiveBlockRmsBound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexRms (p09PropagatedFftBlockError run i) ≤
      model.epsilon * Real.sqrt (n : ℝ) *
          p09Alpha (plan.stage i).radix model.gamma * p09ComplexRms run.input +
        p09PrimitiveBlockSecondOrderCoeff plan model.gamma run.input i *
          model.epsilon ^ 2 := by
  exact p09ComplexRms_local_of_completed_bound run i.val
    (Nat.le_of_lt i.isLt) _
    (p09Alpha (plan.stage i).radix model.gamma)
    (p09BlockVectorSecondOrder (plan.stage i).radix model.gamma)
    (p09Alpha_nonneg _ model.gamma_nonneg)
    (p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg)
    hεone (p09_norm_propagatedFftBlockError_le run i hεone)

private lemma p09PrimitiveTwiddleRmsBound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexRms (p09PropagatedFftTwiddleError run i) ≤
      model.epsilon * Real.sqrt (n : ℝ) *
          p09TwiddleFirstOrderBudget plan model.gamma i * p09ComplexRms run.input +
        p09PrimitiveTwiddleSecondOrderCoeff plan model.gamma run.input i *
          model.epsilon ^ 2 := by
  exact p09ComplexRms_local_of_completed_bound run i.val
    (Nat.le_of_lt i.isLt) _
    (p09TwiddleFirstOrderBudget plan model.gamma i)
    (p09TwiddlePropagatedSecondOrder plan model.gamma i)
    (p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i)
    (p09TwiddlePropagatedSecondOrder_nonneg plan model.gamma_nonneg i)
    hεone (p09_norm_propagatedFftTwiddleError_le run i hεone)

/-- The paper's local estimates `(3.7)` and `(3.8)`, derived from the scalar
Wilkinson model and the operational mixed-radix kernels. -/
noncomputable def p09PrimitiveTheoremOneLocalAnalysis
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) :
    P09TheoremOneLocalAnalysis family := by
  refine
    { blockSecondOrderCoeff :=
        p09PrimitiveBlockSecondOrderCoeff plan γ family.input
      block_second_order_nonneg := ?_
      twiddleSecondOrderCoeff :=
        p09PrimitiveTwiddleSecondOrderCoeff plan γ family.input
      twiddle_second_order_nonneg := ?_
      radius := 1
      radius_pos := by norm_num
      block_error_bound := ?_
      twiddle_error_bound := ?_ }
  · intro i
    exact p09PrimitiveBlockSecondOrderCoeff_nonneg plan
      family.gamma_nonneg family.input i
  · intro i
    exact p09PrimitiveTwiddleSecondOrderCoeff_nonneg plan
      family.gamma_nonneg family.input i
  · intro ε hε i
    have hmodelEpsilon : (family.model ε).epsilon ≤ 1 := by
      rw [family.model_epsilon ε]
      exact hε
    have h := p09PrimitiveBlockRmsBound (family.run ε) i hmodelEpsilon
    rw [family.model_epsilon ε, family.model_gamma ε,
      family.run_input ε] at h
    exact h
  · intro ε hε i
    have hmodelEpsilon : (family.model ε).epsilon ≤ 1 := by
      rw [family.model_epsilon ε]
      exact hε
    have h := p09PrimitiveTwiddleRmsBound (family.run ε) i hmodelEpsilon
    rw [family.model_epsilon ε, family.model_gamma ε,
      family.run_input ε] at h
    exact h

/-- Theorem 1(a), proved from the operation-level FFT execution family. The
caller supplies no local or global error-bound certificate. -/
theorem p09TheoremOneRmsAsymptotic_exists
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) :
    Nonempty (P09TheoremOneRmsAsymptotic family) :=
  p09TheoremOneRmsAsymptotic_exists_of_local_analysis
    { family := family
      localAnalysis := p09PrimitiveTheoremOneLocalAnalysis family }

end HighamBench
