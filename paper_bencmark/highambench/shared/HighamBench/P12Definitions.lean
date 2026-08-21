import HighamBench.Core

namespace HighamBench

/-- A condition-neutral nearest-rounding relation into a representable set. -/
def p12Nearest (representable : ℝ → Prop) (exact rounded : ℝ) : Prop :=
  representable rounded ∧
    ∀ candidate, representable candidate →
      |exact - rounded| ≤ |exact - candidate|

/-- The radix, precision, and inclusive exponent interval in equation (1) of
Lange and Oishi. -/
structure P12RadixFormat where
  beta : ℕ
  precision : ℕ
  emin : ℤ
  emax : ℤ
  beta_ge_two : 2 ≤ beta
  precision_pos : 0 < precision
  emin_le_emax : emin ≤ emax

namespace P12RadixFormat

/-- The paper's integer radix viewed in the reals. -/
def betaR (fmt : P12RadixFormat) : ℝ :=
  fmt.beta

/-- The strict mantissa bound `beta^p` from equation (1). -/
def mantissaBound (fmt : P12RadixFormat) : ℝ :=
  fmt.betaR ^ fmt.precision

/-- The integer part `floor(beta / 2)` appearing in the proof of Theorem 2. -/
def halfRadixFloor (fmt : P12RadixFormat) : ℝ :=
  (fmt.beta / 2 : ℕ)

/-- The exact coefficient `ceil(beta^p - beta / 2)` in equation (7), evaluated
as the equal natural number `beta^p - floor(beta / 2)`. -/
def condition7Ceiling (fmt : P12RadixFormat) : ℝ :=
  (fmt.beta ^ fmt.precision - fmt.beta / 2 : ℕ)

/-- The largest nonnegative mantissa admitted by the strict equation-(1)
mantissa interval. -/
def maxMantissa (fmt : P12RadixFormat) : ℝ :=
  (fmt.beta ^ fmt.precision - 1 : ℕ)

/-- The exponent scale `beta^e` used by a particular representation. -/
noncomputable def scale (fmt : P12RadixFormat) (e : ℤ) : ℝ :=
  fmt.betaR ^ e

/-- The largest positive element of the finite equation-(1) set. -/
noncomputable def maxValue (fmt : P12RadixFormat) : ℝ :=
  fmt.maxMantissa * fmt.scale fmt.emax

/-- An exact real operation result lies in the finite range of equation (1).
This is the Section 4 meaning of "absence of overflow": the exact result does
not lie beyond either finite endpoint. -/
def noOverflow (fmt : P12RadixFormat) (z : ℝ) : Prop :=
  |z| ≤ fmt.maxValue

theorem betaR_pos (fmt : P12RadixFormat) : 0 < fmt.betaR := by
  change (0 : ℝ) < (fmt.beta : ℝ)
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) fmt.beta_ge_two)

theorem betaR_one_le (fmt : P12RadixFormat) : 1 ≤ fmt.betaR := by
  have htwo : (2 : ℝ) ≤ fmt.betaR := by
    change (2 : ℝ) ≤ (fmt.beta : ℝ)
    exact_mod_cast fmt.beta_ge_two
  linarith

theorem mantissaBound_pos (fmt : P12RadixFormat) :
    0 < fmt.mantissaBound := by
  exact pow_pos fmt.betaR_pos _

theorem scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  exact zpow_pos fmt.betaR_pos _

theorem scale_mono (fmt : P12RadixFormat) {e f : ℤ} (hef : e ≤ f) :
    fmt.scale e ≤ fmt.scale f := by
  exact zpow_le_zpow_right₀ fmt.betaR_one_le hef

theorem scale_succ (fmt : P12RadixFormat) (e : ℤ) :
    fmt.scale (e + 1) = fmt.scale e * fmt.betaR := by
  rw [scale, scale, zpow_add₀ (ne_of_gt fmt.betaR_pos)]
  simp

theorem scale_add (fmt : P12RadixFormat) (e f : ℤ) :
    fmt.scale (e + f) = fmt.scale e * fmt.scale f := by
  exact zpow_add₀ (ne_of_gt fmt.betaR_pos) e f

theorem scale_add_precision (fmt : P12RadixFormat) (e : ℤ) :
    fmt.scale (e + (fmt.precision : ℤ)) =
      fmt.scale e * fmt.mantissaBound := by
  rw [fmt.scale_add]
  congr 1

theorem betaR_le_mantissaBound (fmt : P12RadixFormat) :
    fmt.betaR ≤ fmt.mantissaBound := by
  have hp : fmt.precision - 1 + 1 = fmt.precision := by
    have := fmt.precision_pos
    omega
  have hpow : 1 ≤ fmt.betaR ^ (fmt.precision - 1) :=
    one_le_pow₀ fmt.betaR_one_le
  rw [mantissaBound, ← hp, pow_succ]
  nlinarith [fmt.betaR_pos]

theorem halfRadixFloor_add_condition7Ceiling (fmt : P12RadixFormat) :
    fmt.halfRadixFloor + fmt.condition7Ceiling = fmt.mantissaBound := by
  have hhalf_le_beta : fmt.beta / 2 ≤ fmt.beta := Nat.div_le_self _ _
  have hbeta_le_bound_nat : fmt.beta ≤ fmt.beta ^ fmt.precision := by
    have hreal : (fmt.beta : ℝ) ≤ (fmt.beta ^ fmt.precision : ℕ) := by
      simpa [betaR, mantissaBound] using fmt.betaR_le_mantissaBound
    exact_mod_cast hreal
  have hhalf_le_bound : fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans hhalf_le_beta hbeta_le_bound_nat
  norm_num [halfRadixFloor, condition7Ceiling, mantissaBound, betaR]
  exact_mod_cast (by
    simpa [Nat.add_comm] using Nat.sub_add_cancel hhalf_le_bound)

theorem halfRadixFloor_le_half (fmt : P12RadixFormat) :
    fmt.halfRadixFloor ≤ fmt.betaR / 2 := by
  have hdiv : (fmt.beta / 2) * 2 ≤ fmt.beta := Nat.div_mul_le_self _ _
  have hdiv_real : ((fmt.beta / 2 : ℕ) : ℝ) * 2 ≤ (fmt.beta : ℝ) := by
    exact_mod_cast hdiv
  norm_num [halfRadixFloor, betaR]
  nlinarith

theorem half_lt_halfRadixFloor_add_one (fmt : P12RadixFormat) :
    fmt.betaR / 2 < fmt.halfRadixFloor + 1 := by
  have hdiv : fmt.beta < (fmt.beta / 2 + 1) * 2 := by omega
  have hdiv_real :
      (fmt.beta : ℝ) < ((fmt.beta / 2 + 1 : ℕ) : ℝ) * 2 := by
    exact_mod_cast hdiv
  norm_num at hdiv_real
  norm_num [halfRadixFloor, betaR]
  nlinarith

theorem one_le_halfRadixFloor (fmt : P12RadixFormat) :
    (1 : ℝ) ≤ fmt.halfRadixFloor := by
  have htwo := fmt.beta_ge_two
  have hone : 1 ≤ fmt.beta / 2 := by omega
  simpa [halfRadixFloor] using (show (1 : ℝ) ≤ (fmt.beta / 2 : ℕ) by
    exact_mod_cast hone)

theorem condition7Ceiling_eq_intCeil (fmt : P12RadixFormat) :
    fmt.condition7Ceiling =
      ((⌈fmt.mantissaBound - fmt.betaR / 2⌉ : ℤ) : ℝ) := by
  have hlower :
      fmt.condition7Ceiling - 1 < fmt.mantissaBound - fmt.betaR / 2 := by
    nlinarith [fmt.halfRadixFloor_add_condition7Ceiling,
      fmt.half_lt_halfRadixFloor_add_one]
  have hupper :
      fmt.mantissaBound - fmt.betaR / 2 ≤ fmt.condition7Ceiling := by
    nlinarith [fmt.halfRadixFloor_add_condition7Ceiling,
      fmt.halfRadixFloor_le_half]
  have hceil :
      ⌈fmt.mantissaBound - fmt.betaR / 2⌉ =
        (fmt.beta ^ fmt.precision - fmt.beta / 2 : ℕ) := by
    rw [Int.ceil_eq_iff]
    simpa [condition7Ceiling] using And.intro hlower hupper
  rw [hceil]
  simp [condition7Ceiling]

theorem condition7Ceiling_lt_mantissaBound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  nlinarith [fmt.halfRadixFloor_add_condition7Ceiling,
    fmt.one_le_halfRadixFloor]

theorem maxMantissa_nonneg (fmt : P12RadixFormat) :
    0 ≤ fmt.maxMantissa := by
  simp [maxMantissa]

theorem maxMantissa_add_one (fmt : P12RadixFormat) :
    fmt.maxMantissa + 1 = fmt.mantissaBound := by
  have hbeta_pos : 0 < fmt.beta :=
    lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two
  have hpow_pos : 0 < fmt.beta ^ fmt.precision := pow_pos hbeta_pos _
  have hnat :
      fmt.beta ^ fmt.precision - 1 + 1 = fmt.beta ^ fmt.precision :=
    Nat.sub_add_cancel hpow_pos
  norm_num [maxMantissa, mantissaBound, betaR]
  exact_mod_cast hnat

theorem maxMantissa_lt_mantissaBound (fmt : P12RadixFormat) :
    fmt.maxMantissa < fmt.mantissaBound := by
  have hbeta_pos : 0 < fmt.beta :=
    lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two
  have hpow_pos : 0 < fmt.beta ^ fmt.precision := pow_pos hbeta_pos _
  have hnat : fmt.beta ^ fmt.precision - 1 < fmt.beta ^ fmt.precision := by
    omega
  have hreal :
      ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) <
        ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
    exact_mod_cast hnat
  simpa [maxMantissa, mantissaBound, betaR] using hreal

end P12RadixFormat

/-- A particular, not necessarily normalized, representation
`x = m * beta^e` admitted by equation (1).  Keeping the exponent in the
witness preserves the paper's intentional nonuniqueness of `e(x)`. -/
structure P12Representation (fmt : P12RadixFormat) (x : ℝ) where
  mantissa : ℤ
  exponent : ℤ
  mantissa_lower : -fmt.mantissaBound < (mantissa : ℝ)
  mantissa_upper : (mantissa : ℝ) < fmt.mantissaBound
  exponent_lower : fmt.emin ≤ exponent
  exponent_upper : exponent ≤ fmt.emax
  value_eq : x = (mantissa : ℝ) * fmt.scale exponent

/-- Membership in the paper's floating-point set `F`, retaining no preferred
representation. -/
def p12Representable (fmt : P12RadixFormat) (x : ℝ) : Prop :=
  Nonempty (P12Representation fmt x)

/-- Zero belongs to every equation-(1) format, at the lower endpoint exponent. -/
noncomputable def p12ZeroRepresentation
    (fmt : P12RadixFormat) : P12Representation fmt 0 where
  mantissa := 0
  exponent := fmt.emin
  mantissa_lower := by
    have := fmt.mantissaBound_pos
    simpa using (neg_neg_of_pos this)
  mantissa_upper := by simpa using fmt.mantissaBound_pos
  exponent_lower := le_rfl
  exponent_upper := fmt.emin_le_emax
  value_eq := by simp

theorem p12Representable_zero (fmt : P12RadixFormat) :
    p12Representable fmt 0 :=
  ⟨p12ZeroRepresentation fmt⟩

/-- A representation whose exponent is least among all equation-(1)
representations of the same value.  Its scale is the paper's local ULP for a
representable finite value. -/
structure P12LeastRepresentation (fmt : P12RadixFormat) (x : ℝ)
    extends P12Representation fmt x where
  least : ∀ r : P12Representation fmt x, exponent ≤ r.exponent

/-- Exact membership in the radix grid with spacing `beta^e`, without a
mantissa-size claim. -/
def p12IntegerMultiple (fmt : P12RadixFormat) (x : ℝ) (e : ℤ) : Prop :=
  ∃ k : ℤ, x = (k : ℝ) * fmt.scale e

theorem p12IntegerMultiple_add
    {fmt : P12RadixFormat} {x y : ℝ} {e : ℤ}
    (hx : p12IntegerMultiple fmt x e)
    (hy : p12IntegerMultiple fmt y e) :
    p12IntegerMultiple fmt (x + y) e := by
  rcases hx with ⟨kx, hkx⟩
  rcases hy with ⟨ky, hky⟩
  refine ⟨kx + ky, ?_⟩
  rw [hkx, hky, Int.cast_add]
  ring

theorem p12IntegerMultiple_sub
    {fmt : P12RadixFormat} {x y : ℝ} {e : ℤ}
    (hx : p12IntegerMultiple fmt x e)
    (hy : p12IntegerMultiple fmt y e) :
    p12IntegerMultiple fmt (x - y) e := by
  rcases hx with ⟨kx, hkx⟩
  rcases hy with ⟨ky, hky⟩
  refine ⟨kx - ky, ?_⟩
  rw [hkx, hky, Int.cast_sub]
  ring

/-- Products multiply their radix scales. -/
theorem p12IntegerMultiple_mul
    {fmt : P12RadixFormat} {x y : ℝ} {e f : ℤ}
    (hx : p12IntegerMultiple fmt x e)
    (hy : p12IntegerMultiple fmt y f) :
    p12IntegerMultiple fmt (x * y) (e + f) := by
  rcases hx with ⟨kx, hkx⟩
  rcases hy with ⟨ky, hky⟩
  refine ⟨kx * ky, ?_⟩
  rw [hkx, hky, Int.cast_mul, fmt.scale_add]
  ring

/-- A multiple of a coarser radix scale is also a multiple of every finer
radix scale. -/
theorem p12IntegerMultiple_of_le
    {fmt : P12RadixFormat} {x : ℝ} {e f : ℤ}
    (hef : e ≤ f) (hx : p12IntegerMultiple fmt x f) :
    p12IntegerMultiple fmt x e := by
  rcases hx with ⟨k, hk⟩
  let d : ℕ := (f - e).toNat
  have hdiff_nonneg : 0 ≤ f - e := sub_nonneg.mpr hef
  have hd : (d : ℤ) = f - e := Int.toNat_of_nonneg hdiff_nonneg
  refine ⟨k * (fmt.beta : ℤ) ^ d, ?_⟩
  calc
    x = (k : ℝ) * fmt.scale f := hk
    _ = (k : ℝ) * (fmt.scale e * fmt.betaR ^ d) := by
      rw [P12RadixFormat.scale, P12RadixFormat.scale]
      have hexp : f = e + (d : ℤ) := by omega
      rw [hexp, zpow_add₀ (ne_of_gt fmt.betaR_pos), zpow_natCast]
    _ = ((k * (fmt.beta : ℤ) ^ d : ℤ) : ℝ) * fmt.scale e := by
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      change (k : ℝ) * (fmt.scale e * ((fmt.beta : ℝ) ^ d)) =
        (k : ℝ) * ((fmt.beta : ℝ) ^ d) * fmt.scale e
      ring

namespace P12Representation

theorem abs_lt_mantissaBound_mul_scale
    {fmt : P12RadixFormat} {x : ℝ} (r : P12Representation fmt x) :
    |x| < fmt.mantissaBound * fmt.scale r.exponent := by
  have hm : |(r.mantissa : ℝ)| < fmt.mantissaBound :=
    (abs_lt).2 ⟨by linarith [r.mantissa_lower], r.mantissa_upper⟩
  calc
    |x| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
      congrArg abs r.value_eq
    _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
      rw [abs_mul, abs_of_pos (fmt.scale_pos r.exponent)]
    _ < fmt.mantissaBound * fmt.scale r.exponent :=
      mul_lt_mul_of_pos_right hm (fmt.scale_pos r.exponent)

theorem abs_le_maxValue
    {fmt : P12RadixFormat} {x : ℝ} (r : P12Representation fmt x) :
    |x| ≤ fmt.maxValue := by
  have hbeta_pos : 0 < fmt.beta :=
    lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two
  have hbound_nat_pos : 0 < fmt.beta ^ fmt.precision := pow_pos hbeta_pos _
  have hupper_int : r.mantissa < (fmt.beta ^ fmt.precision : ℕ) := by
    have hupper_real :
        (r.mantissa : ℝ) < (fmt.beta ^ fmt.precision : ℕ) := by
      simpa [P12RadixFormat.mantissaBound,
        P12RadixFormat.betaR] using r.mantissa_upper
    exact_mod_cast hupper_real
  have hlower_int : -((fmt.beta ^ fmt.precision : ℕ) : ℤ) < r.mantissa := by
    have hlower_real :
        -((fmt.beta ^ fmt.precision : ℕ) : ℝ) < (r.mantissa : ℝ) := by
      simpa [P12RadixFormat.mantissaBound,
        P12RadixFormat.betaR] using r.mantissa_lower
    exact_mod_cast hlower_real
  have habs_int : |r.mantissa| ≤
      ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have habs_mantissa : |(r.mantissa : ℝ)| ≤ fmt.maxMantissa := by
    have habs_cast :
        (|r.mantissa| : ℝ) ≤
          (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast habs_int
    simpa [P12RadixFormat.maxMantissa] using habs_cast
  have hscale : fmt.scale r.exponent ≤ fmt.scale fmt.emax :=
    fmt.scale_mono r.exponent_upper
  calc
    |x| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
      congrArg abs r.value_eq
    _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
      rw [abs_mul, abs_of_pos (fmt.scale_pos r.exponent)]
    _ ≤ fmt.maxMantissa * fmt.scale r.exponent :=
      mul_le_mul_of_nonneg_right habs_mantissa (fmt.scale_pos _).le
    _ ≤ fmt.maxMantissa * fmt.scale fmt.emax :=
      mul_le_mul_of_nonneg_left hscale fmt.maxMantissa_nonneg
    _ = fmt.maxValue := rfl

end P12Representation

/-- The positive finite endpoint of equation (1). -/
noncomputable def p12PositiveMaxRepresentation (fmt : P12RadixFormat) :
    P12Representation fmt fmt.maxValue where
  mantissa := (fmt.beta ^ fmt.precision - 1 : ℕ)
  exponent := fmt.emax
  mantissa_lower := by
    have hnonneg : (0 : ℝ) ≤ fmt.maxMantissa := fmt.maxMantissa_nonneg
    have hbound := fmt.mantissaBound_pos
    simpa [P12RadixFormat.maxMantissa] using (show
      -fmt.mantissaBound < fmt.maxMantissa by linarith)
  mantissa_upper := by
    simpa [P12RadixFormat.maxMantissa] using fmt.maxMantissa_lt_mantissaBound
  exponent_lower := fmt.emin_le_emax
  exponent_upper := le_rfl
  value_eq := by
    simp [P12RadixFormat.maxValue, P12RadixFormat.maxMantissa]

/-- The negative finite endpoint of equation (1). -/
noncomputable def p12NegativeMaxRepresentation (fmt : P12RadixFormat) :
    P12Representation fmt (-fmt.maxValue) where
  mantissa := -((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ)
  exponent := fmt.emax
  mantissa_lower := by
    simpa [P12RadixFormat.maxMantissa] using
      neg_lt_neg fmt.maxMantissa_lt_mantissaBound
  mantissa_upper := by
    have hnonneg : (0 : ℝ) ≤ fmt.maxMantissa := fmt.maxMantissa_nonneg
    have hbound := fmt.mantissaBound_pos
    simpa [P12RadixFormat.maxMantissa] using (show
      -fmt.maxMantissa < fmt.mantissaBound by linarith)
  exponent_lower := fmt.emin_le_emax
  exponent_upper := le_rfl
  value_eq := by
    simp [P12RadixFormat.maxValue, P12RadixFormat.maxMantissa]

/-- Nearest rounding into the concrete radix set from equation (1). -/
def p12NearestInFormat (fmt : P12RadixFormat) (exact rounded : ℝ) : Prop :=
  p12Nearest (p12Representable fmt) exact rounded

/-- Faithful rounding into `F`: apart from the returned endpoint, no
representable value lies in the closed interval up to the exact result.  This
allows either adjacent endpoint and fixes no tie-breaking policy. -/
def p12FaithfulInFormat (fmt : P12RadixFormat) (exact rounded : ℝ) : Prop :=
  p12Representable fmt rounded ∧
    ∀ candidate, p12Representable fmt candidate →
      ¬ ((rounded < candidate ∧ candidate ≤ exact) ∨
        (exact ≤ candidate ∧ candidate < rounded))

theorem p12NearestInFormat_mem
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (h : p12NearestInFormat fmt exact rounded) :
    p12Representable fmt rounded :=
  h.1

theorem p12NearestInFormat_error_le
    {fmt : P12RadixFormat} {exact rounded candidate : ℝ}
    (h : p12NearestInFormat fmt exact rounded)
    (hcandidate : p12Representable fmt candidate) :
    |exact - rounded| ≤ |exact - candidate| :=
  h.2 candidate hcandidate

theorem p12NearestInFormat_eq_of_representable
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (hexact : p12Representable fmt exact)
    (h : p12NearestInFormat fmt exact rounded) :
    rounded = exact := by
  have hz : |exact - rounded| ≤ 0 := by
    simpa using h.2 exact hexact
  have hzero : exact - rounded = 0 :=
    abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  linarith

theorem p12NearestInFormat_abs_le_of_symmetric_candidates
    {fmt : P12RadixFormat} {exact rounded bound : ℝ}
    (hexact : |exact| ≤ bound)
    (hpositive : p12Representable fmt bound)
    (hnegative : p12Representable fmt (-bound))
    (hnearest : p12NearestInFormat fmt exact rounded) :
    |rounded| ≤ bound := by
  have hexactBounds : -bound ≤ exact ∧ exact ≤ bound :=
    (abs_le).mp hexact
  have hroundUpper : rounded ≤ bound := by
    by_contra hnot
    have hgt : bound < rounded := lt_of_not_ge hnot
    have hnear := hnearest.2 bound hpositive
    rw [abs_of_nonpos (by linarith : exact - rounded ≤ 0),
      abs_of_nonpos (by linarith : exact - bound ≤ 0)] at hnear
    linarith
  have hroundLower : -bound ≤ rounded := by
    by_contra hnot
    have hlt : rounded < -bound := lt_of_not_ge hnot
    have hnear := hnearest.2 (-bound) hnegative
    rw [abs_of_nonneg (by linarith : 0 ≤ exact - rounded),
      abs_of_nonneg (by linarith : 0 ≤ exact - -bound)] at hnear
    linarith
  exact (abs_le).2 ⟨hroundLower, hroundUpper⟩

/-- Nearest rounding is faithful, independently of tie breaking. -/
theorem p12NearestInFormat_faithful
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (h : p12NearestInFormat fmt exact rounded) :
    p12FaithfulInFormat fmt exact rounded := by
  refine ⟨h.1, ?_⟩
  intro candidate hcandidate hbetween
  have hminimal := h.2 candidate hcandidate
  rcases hbetween with hbetween | hbetween
  · rw [abs_of_nonneg (by linarith : 0 ≤ exact - rounded),
      abs_of_nonneg (by linarith : 0 ≤ exact - candidate)] at hminimal
    linarith
  · rw [abs_of_nonpos (by linarith : exact - rounded ≤ 0),
      abs_of_nonpos (by linarith : exact - candidate ≤ 0)] at hminimal
    linarith

theorem p12FaithfulInFormat_mem
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (h : p12FaithfulInFormat fmt exact rounded) :
    p12Representable fmt rounded :=
  h.1

theorem p12FaithfulInFormat_eq_of_representable
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (hexact : p12Representable fmt exact)
    (h : p12FaithfulInFormat fmt exact rounded) :
    rounded = exact := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.2 exact hexact (Or.inl ⟨hlt, le_rfl⟩)
  · exact h.2 exact hexact (Or.inr ⟨le_rfl, hgt⟩)

/-- The elementary radix-grid facts used in Theorem 2's three-case proof.
Each field is a general consequence of equation (1), independent of a
particular FastTwoSum execution.  The bounded addition/subtraction fields are
the representability content of equation (8) and its addition analogue; their
range obligations are derived from an available larger exponent or a strict
magnitude bound rather than attached to an execution. -/
structure P12RadixGeometry (fmt : P12RadixFormat) : Prop where
  representation_at_or_below_of_abs_lt :
    ∀ {x y : ℝ} (rx : P12Representation fmt x),
      p12Representable fmt y →
      |y| < fmt.mantissaBound * fmt.scale rx.exponent →
      ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent
  add_representation_of_bound :
    ∀ {a b : ℝ} (ra : P12Representation fmt a)
      (rb : P12Representation fmt b),
      min ra.exponent rb.exponent < fmt.emax →
      |a + b| ≤
        fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent) →
      ∃ rsum : P12Representation fmt (a + b),
        min ra.exponent rb.exponent ≤ rsum.exponent
  sub_representation_of_bound :
    ∀ {a b : ℝ} (ra : P12Representation fmt a)
      (rb : P12Representation fmt b),
      min ra.exponent rb.exponent < fmt.emax →
      |a - b| ≤
        fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent) →
      ∃ rdiff : P12Representation fmt (a - b),
        min ra.exponent rb.exponent ≤ rdiff.exponent
  sub_representation_of_strict_bound :
    ∀ {a b : ℝ} (ra : P12Representation fmt a)
      (rb : P12Representation fmt b),
      |a - b| <
        fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent) →
      ∃ rdiff : P12Representation fmt (a - b),
        rdiff.exponent = min ra.exponent rb.exponent
  same_exponent_nearest_add :
    ∀ {x y s : ℝ} (rx : P12Representation fmt x)
      (ry : P12Representation fmt y),
      rx.exponent = ry.exponent →
      |y| ≤
        fmt.condition7Ceiling * fmt.scale rx.exponent →
      rx.exponent < fmt.emax →
      p12NearestInFormat fmt (x + y) s →
      ∃ rs : P12Representation fmt s,
        rx.exponent ≤ rs.exponent ∧
          |s - (x + y)| ≤
            fmt.halfRadixFloor * fmt.scale rx.exponent
  large_sum_nearest_exponent :
    ∀ {x y s : ℝ} (rx : P12Representation fmt x)
      (ry : P12Representation fmt y),
      ry.exponent < rx.exponent →
      fmt.mantissaBound * fmt.scale ry.exponent < |x + y| →
      p12NearestInFormat fmt (x + y) s →
      ∃ rs : P12Representation fmt s, ry.exponent < rs.exponent

open P12RadixFormat

private theorem representation_integer_multiple_at
    {fmt : P12RadixFormat} {x : ℝ} (r : P12Representation fmt x)
    {e : ℤ} (he : e ≤ r.exponent) :
    ∃ k : ℤ, x = (k : ℝ) * fmt.scale e := by
  let d : ℕ := (r.exponent - e).toNat
  have hdiff_nonneg : 0 ≤ r.exponent - e := sub_nonneg.mpr he
  have hd : (d : ℤ) = r.exponent - e := Int.toNat_of_nonneg hdiff_nonneg
  refine ⟨r.mantissa * (fmt.beta : ℤ) ^ d, ?_⟩
  calc
    x = (r.mantissa : ℝ) * fmt.scale r.exponent := r.value_eq
    _ = (r.mantissa : ℝ) *
        (fmt.scale e * (fmt.betaR ^ d)) := by
      rw [P12RadixFormat.scale, P12RadixFormat.scale]
      have hexp : r.exponent = e + (d : ℤ) := by omega
      rw [hexp, zpow_add₀ (ne_of_gt fmt.betaR_pos), zpow_natCast]
    _ = ((r.mantissa * (fmt.beta : ℤ) ^ d : ℤ) : ℝ) *
        fmt.scale e := by
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      change (r.mantissa : ℝ) *
          (fmt.scale e * ((fmt.beta : ℝ) ^ d)) =
        (r.mantissa : ℝ) * ((fmt.beta : ℝ) ^ d) * fmt.scale e
      ring

private noncomputable def representation_of_integer_multiple_of_abs_lt
    {fmt : P12RadixFormat} {z : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (heemax : e ≤ fmt.emax)
    (k : ℤ) (hz : z = (k : ℝ) * fmt.scale e)
    (hbound : |z| < fmt.mantissaBound * fmt.scale e) :
    P12Representation fmt z := by
  have hscale : 0 < fmt.scale e := fmt.scale_pos e
  have hkabs : |(k : ℝ)| < fmt.mantissaBound := by
    rw [hz, abs_mul, abs_of_pos hscale] at hbound
    nlinarith
  exact
    { mantissa := k
      exponent := e
      mantissa_lower := (abs_lt.mp hkabs).1
      mantissa_upper := (abs_lt.mp hkabs).2
      exponent_lower := hemin
      exponent_upper := heemax
      value_eq := hz }

private theorem representation_at_or_below_of_abs_lt
    {fmt : P12RadixFormat} {x y : ℝ}
    (rx : P12Representation fmt x) (hy : p12Representable fmt y)
    (hbound : |y| < fmt.mantissaBound * fmt.scale rx.exponent) :
    ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent := by
  rcases hy with ⟨ry⟩
  by_cases he : ry.exponent ≤ rx.exponent
  · exact ⟨ry, he⟩
  · have hxe : rx.exponent ≤ ry.exponent := le_of_not_ge he
    rcases representation_integer_multiple_at ry hxe with ⟨k, hk⟩
    let ry' := representation_of_integer_multiple_of_abs_lt
      rx.exponent_lower rx.exponent_upper k hk hbound
    exact ⟨ry', le_rfl⟩

private theorem precision_sub_one_add_one (fmt : P12RadixFormat) :
    fmt.precision - 1 + 1 = fmt.precision := by
  have hp := fmt.precision_pos
  omega

private theorem mantissaUnit_cast (fmt : P12RadixFormat) :
    (((fmt.beta : ℤ) ^ (fmt.precision - 1) : ℤ) : ℝ) =
      fmt.betaR ^ (fmt.precision - 1) := by
  simp [P12RadixFormat.betaR]

private theorem mantissaUnit_lt_bound (fmt : P12RadixFormat) :
    fmt.betaR ^ (fmt.precision - 1) < fmt.mantissaBound := by
  have hpow : 0 < fmt.betaR ^ (fmt.precision - 1) :=
    pow_pos fmt.betaR_pos _
  have htwo : (2 : ℝ) ≤ fmt.betaR := by
    change (2 : ℝ) ≤ (fmt.beta : ℝ)
    exact_mod_cast fmt.beta_ge_two
  have hbeta : 1 < fmt.betaR := by linarith
  have hbound_eq :
      fmt.mantissaBound =
        fmt.betaR ^ (fmt.precision - 1) * fmt.betaR := by
    calc
      fmt.mantissaBound = fmt.betaR ^ fmt.precision := rfl
      _ = fmt.betaR ^ (fmt.precision - 1 + 1) := by
        rw [precision_sub_one_add_one fmt]
      _ = fmt.betaR ^ (fmt.precision - 1) * fmt.betaR := pow_succ _ _
  rw [hbound_eq]
  nlinarith

private theorem mantissaBound_eq_unit_mul_beta (fmt : P12RadixFormat) :
    fmt.mantissaBound =
      fmt.betaR ^ (fmt.precision - 1) * fmt.betaR := by
  calc
    fmt.mantissaBound = fmt.betaR ^ fmt.precision := rfl
    _ = fmt.betaR ^ (fmt.precision - 1 + 1) := by
      rw [precision_sub_one_add_one fmt]
    _ = fmt.betaR ^ (fmt.precision - 1) * fmt.betaR := pow_succ _ _

private theorem mantissaUnit_le_bound_sub_half (fmt : P12RadixFormat) :
    fmt.betaR ^ (fmt.precision - 1) ≤
      fmt.mantissaBound - fmt.betaR / 2 := by
  have hunit : 1 ≤ fmt.betaR ^ (fmt.precision - 1) := by
    exact one_le_pow₀ fmt.betaR_one_le
  have htwo : (2 : ℝ) ≤ fmt.betaR := by
    change (2 : ℝ) ≤ (fmt.beta : ℝ)
    exact_mod_cast fmt.beta_ge_two
  rw [mantissaBound_eq_unit_mul_beta]
  nlinarith [mul_nonneg
    (sub_nonneg.mpr hunit)
    (sub_nonneg.mpr (by linarith : 1 ≤ fmt.betaR - 1))]

private noncomputable def positive_boundary_representation
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (heemax : e + 1 ≤ fmt.emax) :
    P12Representation fmt (fmt.mantissaBound * fmt.scale e) where
  mantissa := (fmt.beta : ℤ) ^ (fmt.precision - 1)
  exponent := e + 1
  mantissa_lower := by
    rw [mantissaUnit_cast]
    have hpow : 0 ≤ fmt.betaR ^ (fmt.precision - 1) :=
      (pow_pos fmt.betaR_pos _).le
    have hbound := fmt.mantissaBound_pos
    linarith
  mantissa_upper := by
    rw [mantissaUnit_cast]
    exact mantissaUnit_lt_bound fmt
  exponent_lower := le_trans hemin (by omega)
  exponent_upper := heemax
  value_eq := by
    rw [mantissaUnit_cast, fmt.scale_succ,
      mantissaBound_eq_unit_mul_beta]
    ring

private noncomputable def negative_boundary_representation
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (heemax : e + 1 ≤ fmt.emax) :
    P12Representation fmt (-(fmt.mantissaBound * fmt.scale e)) where
  mantissa := -((fmt.beta : ℤ) ^ (fmt.precision - 1))
  exponent := e + 1
  mantissa_lower := by
    rw [Int.cast_neg, mantissaUnit_cast]
    exact neg_lt_neg (mantissaUnit_lt_bound fmt)
  mantissa_upper := by
    rw [Int.cast_neg, mantissaUnit_cast]
    have hpow : 0 ≤ fmt.betaR ^ (fmt.precision - 1) :=
      (pow_pos fmt.betaR_pos _).le
    have hbound := fmt.mantissaBound_pos
    linarith
  exponent_lower := le_trans hemin (by omega)
  exponent_upper := heemax
  value_eq := by
    rw [Int.cast_neg, mantissaUnit_cast, fmt.scale_succ,
      mantissaBound_eq_unit_mul_beta]
    ring

private theorem representation_of_integer_multiple_of_bound
    {fmt : P12RadixFormat} {z : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (heemax : e ≤ fmt.emax)
    (k : ℤ) (hz : z = (k : ℝ) * fmt.scale e)
    (hno : fmt.noOverflow z)
    (hbound : |z| ≤ fmt.mantissaBound * fmt.scale e) :
    ∃ rz : P12Representation fmt z, e ≤ rz.exponent := by
  by_cases hstrict : |z| < fmt.mantissaBound * fmt.scale e
  · exact ⟨representation_of_integer_multiple_of_abs_lt
      hemin heemax k hz hstrict, le_rfl⟩
  · have habs : |z| = fmt.mantissaBound * fmt.scale e :=
      le_antisymm hbound (le_of_not_gt hstrict)
    have heplus : e + 1 ≤ fmt.emax := by
      by_contra hnot
      have heeq : e = fmt.emax := by omega
      rw [P12RadixFormat.noOverflow, habs, heeq,
        P12RadixFormat.maxValue] at hno
      nlinarith [fmt.maxMantissa_add_one, fmt.scale_pos fmt.emax]
    have hendpoint_nonneg :
        0 ≤ fmt.mantissaBound * fmt.scale e :=
      (mul_pos fmt.mantissaBound_pos (fmt.scale_pos e)).le
    rcases (abs_eq hendpoint_nonneg).mp habs with hzpos | hzneg
    · rw [hzpos]
      refine ⟨positive_boundary_representation fmt e hemin heplus, ?_⟩
      change e ≤ e + 1
      omega
    · rw [hzneg]
      refine ⟨negative_boundary_representation fmt e hemin heplus, ?_⟩
      change e ≤ e + 1
      omega

private theorem representation_of_integer_multiple_of_bound_of_exponent_lt
    {fmt : P12RadixFormat} {z : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (helt : e < fmt.emax)
    (k : ℤ) (hz : z = (k : ℝ) * fmt.scale e)
    (hbound : |z| ≤ fmt.mantissaBound * fmt.scale e) :
    ∃ rz : P12Representation fmt z, e ≤ rz.exponent := by
  by_cases hstrict : |z| < fmt.mantissaBound * fmt.scale e
  · exact ⟨representation_of_integer_multiple_of_abs_lt
      hemin helt.le k hz hstrict, le_rfl⟩
  · have habs : |z| = fmt.mantissaBound * fmt.scale e :=
      le_antisymm hbound (le_of_not_gt hstrict)
    have heplus : e + 1 ≤ fmt.emax := by omega
    have hendpoint_nonneg :
        0 ≤ fmt.mantissaBound * fmt.scale e :=
      (mul_pos fmt.mantissaBound_pos (fmt.scale_pos e)).le
    rcases (abs_eq hendpoint_nonneg).mp habs with hzpos | hzneg
    · rw [hzpos]
      refine ⟨positive_boundary_representation fmt e hemin heplus, ?_⟩
      change e ≤ e + 1
      omega
    · rw [hzneg]
      refine ⟨negative_boundary_representation fmt e hemin heplus, ?_⟩
      change e ≤ e + 1
      omega

theorem p12Representation_exists_of_integerMultiple_of_abs_lt
    {fmt : P12RadixFormat} {z : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (heemax : e ≤ fmt.emax)
    (hgrid : p12IntegerMultiple fmt z e)
    (hbound : |z| < fmt.mantissaBound * fmt.scale e) :
    ∃ rz : P12Representation fmt z, rz.exponent = e := by
  rcases hgrid with ⟨k, hk⟩
  let rz := representation_of_integer_multiple_of_abs_lt
    hemin heemax k hk hbound
  exact ⟨rz, rfl⟩

theorem p12Representation_of_integerMultiple_of_bound
    {fmt : P12RadixFormat} {z : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (heemax : e ≤ fmt.emax)
    (hgrid : p12IntegerMultiple fmt z e)
    (hno : fmt.noOverflow z)
    (hbound : |z| ≤ fmt.mantissaBound * fmt.scale e) :
    ∃ rz : P12Representation fmt z, e ≤ rz.exponent := by
  rcases hgrid with ⟨k, hk⟩
  exact representation_of_integer_multiple_of_bound
    hemin heemax k hk hno hbound

theorem p12IntegerMultiple_of_representation_at
    {fmt : P12RadixFormat} {x : ℝ} (r : P12Representation fmt x)
    {e : ℤ} (he : e ≤ r.exponent) :
    p12IntegerMultiple fmt x e := by
  exact representation_integer_multiple_at r he

/-- Nearest rounding of an in-range value preserves every radix grid on which
the exact value lies.  This is the reusable no-range-clipping fact needed by
the Section 4 applications. -/
theorem p12NearestInFormat_integerMultiple
    {fmt : P12RadixFormat} {exact rounded : ℝ} {e : ℤ}
    (hgrid : p12IntegerMultiple fmt exact e)
    (hno : fmt.noOverflow exact)
    (hround : p12NearestInFormat fmt exact rounded) :
    p12IntegerMultiple fmt rounded e := by
  rcases hround.1 with ⟨rr⟩
  by_cases helow : e < fmt.emin
  · exact p12IntegerMultiple_of_le
      (le_trans helow.le rr.exponent_lower)
      (p12IntegerMultiple_of_representation_at rr le_rfl)
  · have hemin : fmt.emin ≤ e := le_of_not_gt helow
    by_cases hehigh : e ≤ fmt.emax
    · by_cases hsmall :
          |exact| < fmt.mantissaBound * fmt.scale e
      · rcases p12Representation_exists_of_integerMultiple_of_abs_lt
            hemin hehigh hgrid hsmall with ⟨rexact, _⟩
        have hrounded : rounded = exact :=
          p12NearestInFormat_eq_of_representable ⟨rexact⟩ hround
        rw [hrounded]
        exact hgrid
      · have hlarge :
            fmt.mantissaBound * fmt.scale e ≤ |exact| :=
          le_of_not_gt hsmall
        have helt : e < fmt.emax := by
          by_contra hnot
          have heq : e = fmt.emax := le_antisymm hehigh (le_of_not_gt hnot)
          rw [P12RadixFormat.noOverflow,
            P12RadixFormat.maxValue] at hno
          rw [heq] at hlarge
          nlinarith [fmt.maxMantissa_add_one,
            fmt.scale_pos fmt.emax]
        have hre : e ≤ rr.exponent := by
          by_contra hnot
          have hrlt : rr.exponent < e := lt_of_not_ge hnot
          have hsucc : rr.exponent + 1 ≤ e := by omega
          have hscaleStep :
              fmt.scale (rr.exponent + 1) ≤ fmt.scale e :=
            fmt.scale_mono hsucc
          have hbetaTwo : (2 : ℝ) ≤ fmt.betaR := by
            change (2 : ℝ) ≤ (fmt.beta : ℝ)
            exact_mod_cast fmt.beta_ge_two
          have hscaleTwo :
              2 * fmt.scale rr.exponent ≤ fmt.scale e := by
            rw [fmt.scale_succ] at hscaleStep
            nlinarith [fmt.scale_pos rr.exponent]
          have hroundedSmall :
              |rounded| <
                fmt.mantissaBound / 2 * fmt.scale e := by
            have hrr := rr.abs_lt_mantissaBound_mul_scale
            have hboundPos := fmt.mantissaBound_pos
            nlinarith
          let endpoint := fmt.mantissaBound * fmt.scale e
          have hendpointPos : 0 < endpoint :=
            mul_pos fmt.mantissaBound_pos (fmt.scale_pos e)
          have hhalfEndpoint :
              fmt.mantissaBound / 2 * fmt.scale e = endpoint / 2 := by
            dsimp [endpoint]
            ring
          have hroundedUpper : rounded < endpoint := by
            have := le_abs_self rounded
            rw [hhalfEndpoint] at hroundedSmall
            nlinarith
          have hroundedLower : -endpoint < rounded := by
            have := neg_abs_le rounded
            rw [hhalfEndpoint] at hroundedSmall
            nlinarith
          by_cases hexactNonneg : 0 ≤ exact
          · have hpositive : endpoint ≤ exact := by
              simpa [endpoint, abs_of_nonneg hexactNonneg] using hlarge
            have hcandidate : p12Representable fmt endpoint :=
              ⟨positive_boundary_representation fmt e hemin (by omega)⟩
            have hminimal := hround.2 endpoint hcandidate
            rw [abs_of_nonneg (by linarith : 0 ≤ exact - rounded),
              abs_of_nonneg (by linarith : 0 ≤ exact - endpoint)] at hminimal
            linarith
          · have hexactNeg : exact < 0 := lt_of_not_ge hexactNonneg
            have hnegative : exact ≤ -endpoint := by
              rw [abs_of_neg hexactNeg] at hlarge
              dsimp [endpoint]
              linarith
            have hcandidate : p12Representable fmt (-endpoint) :=
              ⟨negative_boundary_representation fmt e hemin (by omega)⟩
            have hminimal := hround.2 (-endpoint) hcandidate
            rw [abs_of_nonpos (by linarith : exact - rounded ≤ 0),
              abs_of_nonpos (by linarith : exact - -endpoint ≤ 0)] at hminimal
            linarith
        exact p12IntegerMultiple_of_representation_at rr hre
    · have hemax : fmt.emax ≤ e := by omega
      have hgridMax : p12IntegerMultiple fmt exact fmt.emax :=
        p12IntegerMultiple_of_le hemax hgrid
      have hstrict :
          |exact| < fmt.mantissaBound * fmt.scale fmt.emax := by
        rw [P12RadixFormat.noOverflow,
          P12RadixFormat.maxValue] at hno
        nlinarith [fmt.maxMantissa_add_one,
          fmt.scale_pos fmt.emax]
      rcases p12Representation_exists_of_integerMultiple_of_abs_lt
          fmt.emin_le_emax le_rfl hgridMax hstrict with ⟨rexact, _⟩
      have hrounded : rounded = exact :=
        p12NearestInFormat_eq_of_representable ⟨rexact⟩ hround
      rw [hrounded]
      exact hgrid

private theorem add_representation_of_bound
    {fmt : P12RadixFormat} {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (helt : min ra.exponent rb.exponent < fmt.emax)
    (hbound : |a + b| ≤
      fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent)) :
    ∃ rsum : P12Representation fmt (a + b),
      min ra.exponent rb.exponent ≤ rsum.exponent := by
  let e := min ra.exponent rb.exponent
  rcases representation_integer_multiple_at ra (min_le_left _ _) with
    ⟨ka, hka⟩
  rcases representation_integer_multiple_at rb (min_le_right _ _) with
    ⟨kb, hkb⟩
  have hz : a + b = ((ka + kb : ℤ) : ℝ) * fmt.scale e := by
    rw [hka, hkb]
    simp only [Int.cast_add]
    ring
  apply representation_of_integer_multiple_of_bound_of_exponent_lt
    (le_min ra.exponent_lower rb.exponent_lower)
    helt (ka + kb) hz
  simpa [e] using hbound

private theorem sub_representation_of_bound
    {fmt : P12RadixFormat} {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (helt : min ra.exponent rb.exponent < fmt.emax)
    (hbound : |a - b| ≤
      fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent)) :
    ∃ rdiff : P12Representation fmt (a - b),
      min ra.exponent rb.exponent ≤ rdiff.exponent := by
  let e := min ra.exponent rb.exponent
  rcases representation_integer_multiple_at ra (min_le_left _ _) with
    ⟨ka, hka⟩
  rcases representation_integer_multiple_at rb (min_le_right _ _) with
    ⟨kb, hkb⟩
  have hz : a - b = ((ka - kb : ℤ) : ℝ) * fmt.scale e := by
    rw [hka, hkb]
    simp only [Int.cast_sub]
    ring
  apply representation_of_integer_multiple_of_bound_of_exponent_lt
    (le_min ra.exponent_lower rb.exponent_lower)
    helt (ka - kb) hz
  simpa [e] using hbound

private theorem sub_representation_of_strict_bound
    {fmt : P12RadixFormat} {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (hbound : |a - b| <
      fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent)) :
    ∃ rdiff : P12Representation fmt (a - b),
      rdiff.exponent = min ra.exponent rb.exponent := by
  let e := min ra.exponent rb.exponent
  rcases representation_integer_multiple_at ra (min_le_left _ _) with
    ⟨ka, hka⟩
  rcases representation_integer_multiple_at rb (min_le_right _ _) with
    ⟨kb, hkb⟩
  have hz : a - b = ((ka - kb : ℤ) : ℝ) * fmt.scale e := by
    rw [hka, hkb]
    simp only [Int.cast_sub]
    ring
  let rdiff := representation_of_integer_multiple_of_abs_lt
    (le_min ra.exponent_lower rb.exponent_lower)
    (le_trans (min_le_left _ _) ra.exponent_upper)
    (ka - kb) hz (by simpa [e] using hbound)
  exact ⟨rdiff, rfl⟩

private theorem large_sum_nearest_exponent
    {fmt : P12RadixFormat} {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (hryx : ry.exponent < rx.exponent)
    (hlarge : fmt.mantissaBound * fmt.scale ry.exponent < |x + y|)
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    ∃ rs : P12Representation fmt s, ry.exponent < rs.exponent := by
  let endpoint := fmt.mantissaBound * fmt.scale ry.exponent
  have hendpoint_pos : 0 < endpoint :=
    mul_pos fmt.mantissaBound_pos (fmt.scale_pos ry.exponent)
  have heplus : ry.exponent + 1 ≤ fmt.emax := by
    exact le_trans (by omega) rx.exponent_upper
  have hs_endpoint : endpoint ≤ |s| := by
    have htriangle : |x + y| ≤ |(x + y) - s| + |s| := by
      calc
        |x + y| = |((x + y) - s) + s| := by congr 1 <;> ring
        _ ≤ |(x + y) - s| + |s| := abs_add_le _ _
    by_cases hsign : 0 ≤ x + y
    · have hvalue : endpoint < x + y := by
        simpa [abs_of_nonneg hsign] using hlarge
      have hcand : p12Representable fmt endpoint :=
        ⟨positive_boundary_representation fmt ry.exponent
          ry.exponent_lower heplus⟩
      have hnear := hnearest.2 endpoint hcand
      have hdist : |(x + y) - endpoint| = (x + y) - endpoint :=
        abs_of_nonneg (sub_nonneg.mpr hvalue.le)
      rw [hdist] at hnear
      rw [abs_of_nonneg hsign] at htriangle
      linarith
    · have hsign' : x + y < 0 := lt_of_not_ge hsign
      have hvalue : x + y < -endpoint := by
        rw [abs_of_neg hsign'] at hlarge
        linarith
      have hcand : p12Representable fmt (-endpoint) :=
        ⟨negative_boundary_representation fmt ry.exponent
          ry.exponent_lower heplus⟩
      have hnear := hnearest.2 (-endpoint) hcand
      have hdist : |(x + y) - (-endpoint)| = -(x + y) - endpoint := by
        rw [abs_of_neg]
        · ring
        · linarith
      rw [hdist] at hnear
      rw [abs_of_neg hsign'] at htriangle
      linarith
  rcases hnearest.1 with ⟨rs⟩
  refine ⟨rs, ?_⟩
  by_contra hnot
  have hrs_le : rs.exponent ≤ ry.exponent := le_of_not_gt hnot
  have hscale : fmt.scale rs.exponent ≤ fmt.scale ry.exponent :=
    fmt.scale_mono hrs_le
  have hrs_abs := rs.abs_lt_mantissaBound_mul_scale
  have hrs_lt_endpoint : |s| < endpoint :=
    lt_of_lt_of_le hrs_abs
      (mul_le_mul_of_nonneg_left hscale fmt.mantissaBound_pos.le)
  exact (not_lt_of_ge hs_endpoint hrs_lt_endpoint)

private theorem same_exponent_nearest_add
    {fmt : P12RadixFormat} {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (hsame : rx.exponent = ry.exponent)
    (hcondition : |y| ≤
      fmt.condition7Ceiling * fmt.scale rx.exponent)
    (hexponent_lt : rx.exponent < fmt.emax)
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    ∃ rs : P12Representation fmt s,
      rx.exponent ≤ rs.exponent ∧
        |s - (x + y)| ≤
          fmt.halfRadixFloor * fmt.scale rx.exponent := by
  let z := x + y
  let e := rx.exponent
  have hscale_pos : 0 < fmt.scale e := fmt.scale_pos e
  have hx_abs := rx.abs_lt_mantissaBound_mul_scale
  have hz_upper :
      |z| < (fmt.mantissaBound + fmt.condition7Ceiling) *
        fmt.scale e := by
    calc
      |z| ≤ |x| + |y| := by
        simpa [z] using abs_add_le x y
      _ < fmt.mantissaBound * fmt.scale e + |y| := by
        nlinarith
      _ ≤ fmt.mantissaBound * fmt.scale e +
          fmt.condition7Ceiling * fmt.scale e := by
        nlinarith
      _ = (fmt.mantissaBound + fmt.condition7Ceiling) *
          fmt.scale e := by
        ring
  by_cases hsmall : |z| ≤ fmt.mantissaBound * fmt.scale e
  · have hmin : min rx.exponent ry.exponent = e := by
      simp [e, hsame]
    have hbound : |x + y| ≤
        fmt.mantissaBound *
          fmt.scale (min rx.exponent ry.exponent) := by
      simpa [z, hmin] using hsmall
    have hmin_lt : min rx.exponent ry.exponent < fmt.emax := by
      simpa [hmin, e] using hexponent_lt
    rcases add_representation_of_bound rx ry hmin_lt hbound with
      ⟨rsum, hrsum⟩
    have hs : s = x + y :=
      p12NearestInFormat_eq_of_representable ⟨rsum⟩ hnearest
    rw [hs]
    refine ⟨rsum, ?_, ?_⟩
    · simpa [e, hmin] using hrsum
    · simp
      exact mul_nonneg (by
        simp [P12RadixFormat.halfRadixFloor])
        (fmt.scale_pos rx.exponent).le
  · have hlarge : fmt.mantissaBound * fmt.scale e < |z| :=
      lt_of_not_ge hsmall
    have heplus : e + 1 ≤ fmt.emax := by
      simpa [e] using hexponent_lt
    rcases representation_integer_multiple_at rx (by
      change rx.exponent ≤ rx.exponent
      exact le_rfl) with
      ⟨kx, hkx⟩
    rcases representation_integer_multiple_at ry (by
      change rx.exponent ≤ ry.exponent
      exact hsame.le) with
      ⟨ky, hky⟩
    let k : ℤ := kx + ky
    have hz_mul : z = (k : ℝ) * fmt.scale e := by
      rw [show z = x + y by rfl, hkx, hky]
      simp only [k, Int.cast_add]
      ring
    have hk_upper : |(k : ℝ)| <
        fmt.mantissaBound + fmt.condition7Ceiling := by
      rw [hz_mul, abs_mul, abs_of_pos hscale_pos] at hz_upper
      nlinarith
    let n : ℤ := round ((k : ℝ) / fmt.betaR)
    have hround :
        |(k : ℝ) / fmt.betaR - (n : ℝ)| ≤ 1 / 2 := by
      exact abs_sub_round ((k : ℝ) / fmt.betaR)
    have hn_triangle : |(n : ℝ)| ≤
        |(k : ℝ) / fmt.betaR - (n : ℝ)| +
          |(k : ℝ)| / fmt.betaR := by
      calc
        |(n : ℝ)| =
            |-((k : ℝ) / fmt.betaR - (n : ℝ)) +
              (k : ℝ) / fmt.betaR| := by congr 1 <;> ring
        _ ≤ |-((k : ℝ) / fmt.betaR - (n : ℝ))| +
            |(k : ℝ) / fmt.betaR| := abs_add_le _ _
        _ = |(k : ℝ) / fmt.betaR - (n : ℝ)| +
            |(k : ℝ)| / fmt.betaR := by
          rw [abs_neg, abs_div, abs_of_pos fmt.betaR_pos]
    have hk_div : |(k : ℝ)| / fmt.betaR <
        (fmt.mantissaBound + fmt.condition7Ceiling) / fmt.betaR :=
      div_lt_div_of_pos_right hk_upper fmt.betaR_pos
    have hcoefficient_le :
        fmt.condition7Ceiling ≤ fmt.mantissaBound - 1 := by
      nlinarith [fmt.halfRadixFloor_add_condition7Ceiling,
        fmt.one_le_halfRadixFloor]
    have hn_pre : |(n : ℝ)| <
        1 / 2 + (2 * fmt.mantissaBound - 1) / fmt.betaR := by
      calc
        |(n : ℝ)| ≤
            |(k : ℝ) / fmt.betaR - (n : ℝ)| +
              |(k : ℝ)| / fmt.betaR := hn_triangle
        _ ≤ 1 / 2 + |(k : ℝ)| / fmt.betaR := by linarith
        _ < 1 / 2 +
            (fmt.mantissaBound + fmt.condition7Ceiling) /
              fmt.betaR := by
          linarith
        _ ≤ 1 / 2 + (2 * fmt.mantissaBound - 1) / fmt.betaR := by
          have hquot :
              (fmt.mantissaBound + fmt.condition7Ceiling) / fmt.betaR ≤
                (2 * fmt.mantissaBound - 1) / fmt.betaR :=
            (div_le_div_iff_of_pos_right fmt.betaR_pos).2 (by linarith)
          linarith
    have htwo : (2 : ℝ) ≤ fmt.betaR := by
      change (2 : ℝ) ≤ (fmt.beta : ℝ)
      exact_mod_cast fmt.beta_ge_two
    have hshift_nonneg :
        0 ≤ (fmt.betaR - 2) * (fmt.mantissaBound - 1 / 2) := by
      exact mul_nonneg (sub_nonneg.mpr htwo) (by
        have hbound_one : (1 : ℝ) ≤ fmt.mantissaBound :=
          le_trans fmt.betaR_one_le fmt.betaR_le_mantissaBound
        linarith)
    have htwo_bound :
        1 / 2 + (2 * fmt.mantissaBound - 1) / fmt.betaR ≤
          fmt.mantissaBound := by
      rw [show 1 / 2 + (2 * fmt.mantissaBound - 1) / fmt.betaR =
          (fmt.betaR / 2 + 2 * fmt.mantissaBound - 1) / fmt.betaR by
        field_simp [ne_of_gt fmt.betaR_pos]
        ring]
      rw [div_le_iff₀ fmt.betaR_pos]
      nlinarith
    have hn_bound : |(n : ℝ)| < fmt.mantissaBound :=
      lt_of_lt_of_le hn_pre htwo_bound
    let candidate := (n : ℝ) * fmt.scale (e + 1)
    have hcand_bound :
        |candidate| < fmt.mantissaBound * fmt.scale (e + 1) := by
      rw [show candidate = (n : ℝ) * fmt.scale (e + 1) by rfl,
        abs_mul, abs_of_pos (fmt.scale_pos (e + 1))]
      exact mul_lt_mul_of_pos_right hn_bound (fmt.scale_pos (e + 1))
    let rcandidate : P12Representation fmt candidate :=
      representation_of_integer_multiple_of_abs_lt
        (le_trans rx.exponent_lower (by omega)) heplus n rfl hcand_bound
    have hscaled_round :
        |(k : ℝ) - (n : ℝ) * fmt.betaR| ≤
          fmt.halfRadixFloor := by
      have hmul := mul_le_mul_of_nonneg_left hround fmt.betaR_pos.le
      have hrewrite :
          fmt.betaR *
              |(k : ℝ) / fmt.betaR - (n : ℝ)| =
            |(k : ℝ) - (n : ℝ) * fmt.betaR| := by
        calc
          fmt.betaR * |(k : ℝ) / fmt.betaR - (n : ℝ)| =
              |fmt.betaR| *
                |(k : ℝ) / fmt.betaR - (n : ℝ)| := by
            rw [abs_of_pos fmt.betaR_pos]
          _ = |fmt.betaR *
                ((k : ℝ) / fmt.betaR - (n : ℝ))| := by
            rw [abs_mul]
          _ = |(k : ℝ) - (n : ℝ) * fmt.betaR| := by
            congr 1
            field_simp [ne_of_gt fmt.betaR_pos]
      rw [hrewrite] at hmul
      have hraw :
          |(k : ℝ) - (n : ℝ) * fmt.betaR| ≤ fmt.betaR / 2 := by
        nlinarith
      let d : ℤ := k - n * (fmt.beta : ℤ)
      have hd_cast :
          (d : ℝ) = (k : ℝ) - (n : ℝ) * fmt.betaR := by
        simp [d, P12RadixFormat.betaR]
      have hd_upper_real : (d : ℝ) < fmt.halfRadixFloor + 1 := by
        calc
          (d : ℝ) ≤ |(d : ℝ)| := le_abs_self _
          _ = |(k : ℝ) - (n : ℝ) * fmt.betaR| := by rw [hd_cast]
          _ ≤ fmt.betaR / 2 := hraw
          _ < fmt.halfRadixFloor + 1 := fmt.half_lt_halfRadixFloor_add_one
      have hd_lower_real : -(fmt.halfRadixFloor + 1) < (d : ℝ) := by
        calc
          -(fmt.halfRadixFloor + 1) < -(fmt.betaR / 2) := by
            linarith [fmt.half_lt_halfRadixFloor_add_one]
          _ ≤ -|(d : ℝ)| := by
            rw [hd_cast]
            exact neg_le_neg hraw
          _ ≤ (d : ℝ) := neg_abs_le _
      have hd_upper_int : d ≤ (fmt.beta / 2 : ℕ) := by
        have hd_upper_real' :
            (d : ℝ) < (((fmt.beta / 2 : ℕ) : ℤ) : ℝ) + 1 := by
          simpa [P12RadixFormat.halfRadixFloor] using hd_upper_real
        have : d < ((fmt.beta / 2 : ℕ) : ℤ) + 1 := by
          exact_mod_cast hd_upper_real'
        omega
      have hd_lower_int : -((fmt.beta / 2 : ℕ) : ℤ) ≤ d := by
        have hd_lower_real' :
            -((((fmt.beta / 2 : ℕ) : ℤ) : ℝ) + 1) < (d : ℝ) := by
          simpa [P12RadixFormat.halfRadixFloor] using hd_lower_real
        have : -(((fmt.beta / 2 : ℕ) : ℤ) + 1) < d := by
          exact_mod_cast hd_lower_real'
        omega
      rw [← hd_cast]
      have hd_lower_real' :
          -((((fmt.beta / 2 : ℕ) : ℤ) : ℝ)) ≤ (d : ℝ) := by
        exact_mod_cast hd_lower_int
      have hd_upper_real' :
          (d : ℝ) ≤ (((fmt.beta / 2 : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast hd_upper_int
      have habs := abs_le.2 ⟨hd_lower_real', hd_upper_real'⟩
      simpa [P12RadixFormat.halfRadixFloor] using habs
    have hcandidate_error :
        |z - candidate| ≤ fmt.halfRadixFloor * fmt.scale e := by
      rw [hz_mul, show candidate = (n : ℝ) * fmt.scale (e + 1) by rfl,
        fmt.scale_succ]
      have heq :
          (k : ℝ) * fmt.scale e -
              (n : ℝ) * (fmt.scale e * fmt.betaR) =
            ((k : ℝ) - (n : ℝ) * fmt.betaR) * fmt.scale e := by
        ring
      rw [heq, abs_mul, abs_of_pos hscale_pos]
      exact mul_le_mul_of_nonneg_right hscaled_round hscale_pos.le
    have hnearest_error :
        |z - s| ≤ fmt.halfRadixFloor * fmt.scale e :=
      le_trans (hnearest.2 candidate ⟨rcandidate⟩) hcandidate_error
    have hs_lower :
        fmt.condition7Ceiling * fmt.scale e < |s| := by
      have htriangle : |z| ≤ |z - s| + |s| := by
        calc
          |z| = |(z - s) + s| := by congr 1 <;> ring
          _ ≤ |z - s| + |s| := abs_add_le _ _
      rw [← fmt.halfRadixFloor_add_condition7Ceiling] at hlarge
      nlinarith
    rcases hnearest.1 with ⟨rs⟩
    have hrs_ge : e ≤ rs.exponent := by
      by_contra hnot
      have hrs_succ : rs.exponent + 1 ≤ e := by omega
      have hscale_step :
          fmt.scale (rs.exponent + 1) ≤ fmt.scale e :=
        fmt.scale_mono hrs_succ
      have hrs_upper := rs.abs_lt_mantissaBound_mul_scale
      have hunit_nonneg :
          0 ≤ fmt.betaR ^ (fmt.precision - 1) :=
        (pow_pos fmt.betaR_pos _).le
      have hcoarse :
          fmt.mantissaBound * fmt.scale rs.exponent ≤
            fmt.betaR ^ (fmt.precision - 1) * fmt.scale e := by
        calc
          fmt.mantissaBound * fmt.scale rs.exponent =
              fmt.betaR ^ (fmt.precision - 1) *
                fmt.scale (rs.exponent + 1) := by
            rw [mantissaBound_eq_unit_mul_beta, fmt.scale_succ]
            ring
          _ ≤ fmt.betaR ^ (fmt.precision - 1) * fmt.scale e :=
            mul_le_mul_of_nonneg_left hscale_step hunit_nonneg
      have hthreshold :
          fmt.betaR ^ (fmt.precision - 1) * fmt.scale e ≤
            fmt.condition7Ceiling * fmt.scale e :=
        mul_le_mul_of_nonneg_right
          (by
            calc
              fmt.betaR ^ (fmt.precision - 1) ≤
                  fmt.mantissaBound - fmt.betaR / 2 :=
                mantissaUnit_le_bound_sub_half fmt
              _ ≤ fmt.condition7Ceiling := by
                nlinarith [fmt.halfRadixFloor_add_condition7Ceiling,
                  fmt.halfRadixFloor_le_half])
          hscale_pos.le
      have : |s| <
          fmt.condition7Ceiling * fmt.scale e :=
        lt_of_lt_of_le hrs_upper (le_trans hcoarse hthreshold)
      exact (not_lt_of_ge hs_lower.le this)
    refine ⟨rs, ?_, ?_⟩
    · simpa [e] using hrs_ge
    · rw [abs_sub_comm]
      simpa [z, e] using hnearest_error

theorem p12RadixGeometry (fmt : P12RadixFormat) :
    P12RadixGeometry fmt where
  representation_at_or_below_of_abs_lt :=
    representation_at_or_below_of_abs_lt
  add_representation_of_bound := add_representation_of_bound
  sub_representation_of_bound := sub_representation_of_bound
  sub_representation_of_strict_bound :=
    sub_representation_of_strict_bound
  same_exponent_nearest_add := same_exponent_nearest_add
  large_sum_nearest_exponent := large_sum_nearest_exponent

/-- The three returned/intermediate values of Dekker's FastTwoSum algorithm. -/
structure P12FastTwoSumTrace where
  s : ℝ
  t : ℝ
  e : ℝ

/-- One execution of the original three-operation FastTwoSum algorithm from
the paper: nearest addition followed by two uses of the same faithful
subtraction model.  Theorem 2 states no separate range premise; exactness and
representability of both differences are consequences of condition (7). -/
structure P12FastTwoSumExecution (fmt : P12RadixFormat)
    (x y : ℝ) (tr : P12FastTwoSumTrace) : Prop where
  add : p12NearestInFormat fmt (x + y) tr.s
  first_sub : p12FaithfulInFormat fmt (tr.s - x) tr.t
  second_sub : p12FaithfulInFormat fmt (y - tr.t) tr.e

/-- The values needed to state the exact ThreeProduct composition in Lemma 4. -/
structure P12ThreeProductTrace where
  th : ℝ
  tl : ℝ
  s1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  s2 : ℝ
  t : ℝ
  r : ℝ
  s3 : ℝ

/-- The observable meaning of "no underflow errors" for a delegated
`TwoProduct` call in Lemma 4.  The transformation remains exact, a nonzero
product is not rounded to zero, and the returned residual retains the product
scale propagated by `FourSumThreeProduct`. -/
def P12TwoProductNoUnderflowError
    (fmt : P12RadixFormat) (left right high low : ℝ)
    (productGrid : ℤ) : Prop :=
  high + low = left * right ∧
    (left * right ≠ 0 → high ≠ 0) ∧
    |low| ≤ fmt.mantissaBound / 2 * fmt.scale productGrid

/-- The concrete equation-(17) contract of one `TwoProduct` call.  `leftGrid`
and `rightGrid` identify the residual scale propagated by the corresponding
`FourSumThreeProduct` call; unlike the old contract, no operand or output grid
is stored as an execution certificate. -/
structure P12TwoProductExecution
    (fmt : P12RadixFormat) {left right : ℝ}
    (leftRep : P12LeastRepresentation fmt left)
    (rightRep : P12LeastRepresentation fmt right)
    (leftGrid rightGrid : ℤ)
    (high low : ℝ) where
  highRep : P12LeastRepresentation fmt high
  lowRep : P12LeastRepresentation fmt low
  high_round : p12NearestInFormat fmt (left * right) high
  no_underflow_error : P12TwoProductNoUnderflowError fmt
    left right high low (leftGrid + rightGrid)
  product_no_overflow : fmt.noOverflow (left * right)
  low_error : |low| ≤ (1 / 2) * fmt.scale highRep.exponent

/-- The Section 4 instance of FastTwoSum: all three operations use nearest
rounding.  The more general Theorem 2 execution remains available for the
paper's faithful-subtraction result. -/
structure P12NearestFastTwoSumExecution (fmt : P12RadixFormat)
    (x y : ℝ) (tr : P12FastTwoSumTrace) : Prop where
  add : p12NearestInFormat fmt (x + y) tr.s
  first_sub : p12NearestInFormat fmt (tr.s - x) tr.t
  second_sub : p12NearestInFormat fmt (y - tr.t) tr.e

/-- The FastTwoSum trace formed by lines 1--2 of `ThreeProduct` after the three
`TwoProduct` calls have produced the four-term expansion. -/
def P12ThreeProductTrace.mergeTrace
    (tr : P12ThreeProductTrace) : P12FastTwoSumTrace where
  s := tr.s2
  t := tr.t
  e := tr.r

/-- One execution of the paper's `ThreeProduct` procedure.  The propagated
scales are exactly those in the proof of Lemma 4: the first product uses the
input scales, and both following products use their sum.  Every arithmetic
operation is nearest-rounded, and the explicit range fields are precisely
Section 4's standing absence-of-overflow convention.  No exact merge, final
representability, or target equality is stored in the execution. -/
structure P12ThreeProductExecution
    (fmt : P12RadixFormat) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace) where
  x1Rep : P12LeastRepresentation fmt x1
  x2Rep : P12LeastRepresentation fmt x2
  x3Rep : P12LeastRepresentation fmt x3
  first : P12TwoProductExecution fmt x2Rep x3Rep
    x2Rep.exponent x3Rep.exponent tr.th tr.tl
  second : P12TwoProductExecution fmt x1Rep first.highRep
    x1Rep.exponent (x2Rep.exponent + x3Rep.exponent) tr.s1 tr.a2
  third : P12TwoProductExecution fmt x1Rep first.lowRep
    x1Rep.exponent (x2Rep.exponent + x3Rep.exponent) tr.a3 tr.a4
  merge : P12NearestFastTwoSumExecution fmt tr.a2 tr.a3 tr.mergeTrace
  merge_add_no_overflow : fmt.noOverflow (tr.a2 + tr.a3)
  merge_first_sub_no_overflow : fmt.noOverflow (tr.s2 - tr.a2)
  merge_second_sub_no_overflow : fmt.noOverflow (tr.a3 - tr.t)
  final_add : p12NearestInFormat fmt (tr.r + tr.a4) tr.s3
  final_no_overflow : fmt.noOverflow (tr.r + tr.a4)

end HighamBench
