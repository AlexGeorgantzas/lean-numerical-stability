# Declaration dossier for P12-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p12_t2_fast_two_sum_exact
    (fmt : P12RadixFormat) (x y : ℝ) (tr : P12FastTwoSumTrace)
    (hx : p12Representable fmt x) (hy : p12Representable fmt y)
    (hcondition7 : ∃ rx : P12Representation fmt x,
      |y| ≤
        (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale rx.exponent)
    (run : P12FastTwoSumExecution fmt x y tr) :
    tr.t = tr.s - x ∧
      tr.e = y - tr.t ∧
      tr.s + tr.e = x + y ∧
      |tr.s - (x + y)| ≤ |y|
```

## Elaborated target type

```lean
∀ (fmt : HighamBench.P12RadixFormat) (x y : Real) (tr : HighamBench.P12FastTwoSumTrace),
  HighamBench.p12Representable fmt x →
    HighamBench.p12Representable fmt y →
      (Exists fun rx =>
          Real.instLE.le (abs y)
            (instHMul.hMul (instHSub.hSub fmt.mantissaBound (instHDiv.hDiv fmt.betaR 2)) (fmt.scale rx.exponent))) →
        HighamBench.P12FastTwoSumExecution fmt x y tr →
          And (Eq tr.t (instHSub.hSub tr.s x))
            (And (Eq tr.e (instHSub.hSub y tr.t))
              (And (Eq (instHAdd.hAdd tr.s tr.e) (instHAdd.hAdd x y))
                (Real.instLE.le (abs (instHSub.hSub tr.s (instHAdd.hAdd x y))) (abs y))))
```

## Fully explicit elaborated target type

```lean
∀ (fmt : HighamBench.P12RadixFormat) (x y : Real) (tr : HighamBench.P12FastTwoSumTrace)
  (hx : HighamBench.p12Representable fmt x) (hy : HighamBench.p12Representable fmt y)
  (hcondition7 :
    @Exists.{1} (HighamBench.P12Representation fmt x) fun (rx : HighamBench.P12Representation fmt x) =>
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup y)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (HighamBench.P12RadixFormat.mantissaBound fmt)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (HighamBench.P12RadixFormat.betaR fmt)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (HighamBench.P12RadixFormat.scale fmt (@HighamBench.P12Representation.exponent fmt x rx))))
  (run : HighamBench.P12FastTwoSumExecution fmt x y tr),
  And
    (@Eq.{1} Real (HighamBench.P12FastTwoSumTrace.t tr)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12FastTwoSumTrace.s tr) x))
    (And
      (@Eq.{1} Real (HighamBench.P12FastTwoSumTrace.e tr)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) y (HighamBench.P12FastTwoSumTrace.t tr)))
      (And
        (@Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12FastTwoSumTrace.s tr)
            (HighamBench.P12FastTwoSumTrace.e tr))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y))
        (@LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12FastTwoSumTrace.s tr)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)))
          (@abs.{0} Real Real.lattice Real.instAddGroup y))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P12Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P12Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P12FastTwoSumExecution`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `833a4fd2aa477fce008995b87689683174e9251093458eba4d27eef75bfe2820`

Type:

```lean
HighamBench.P12RadixFormat → Real → Real → HighamBench.P12FastTwoSumTrace → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x y : Real) → (tr : HighamBench.P12FastTwoSumTrace) → Prop
```

### D002: `HighamBench.P12FastTwoSumTrace`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a1b5217c0378ce1b740434d1eb47365d42c1c872f1c39dd028fc0b4d3e3dca6f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D003: `HighamBench.P12FastTwoSumTrace.e`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cc3317bbdb2eaa69bc8b7b247535d66ce5c0fef13fe12280bd5801a4ac0f84f9`

Type:

```lean
HighamBench.P12FastTwoSumTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12FastTwoSumTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D004: `HighamBench.P12FastTwoSumTrace.s`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `af611c8df0f69d3f007cfb3f3885d093f4cd4afff8387aa7d47e41db0a02b21a`

Type:

```lean
HighamBench.P12FastTwoSumTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12FastTwoSumTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D005: `HighamBench.P12FastTwoSumTrace.t`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5a7088d876ae1f159467fb8754df1325283911651abbdf07ea0fba96b9b7bec7`

Type:

```lean
HighamBench.P12FastTwoSumTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12FastTwoSumTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D006: `HighamBench.P12RadixFormat`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `e9e9215e6d3537ea32d9fb10bf6f9455804915beb41514d3586ea1e906889695`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D007: `HighamBench.P12RadixFormat.betaR`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `03c195fec72dece4f9a192ae9817181f3999f6355b885b3a3c002b687b4637d6`

Type:

```lean
HighamBench.P12RadixFormat → Real
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt => fmt.beta.cast
```

### D008: `HighamBench.P12RadixFormat.mantissaBound`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fecbead56154f0b704b8757c954ec63c18b3fcf73f8166f18ab5855d63fd9339`

Type:

```lean
HighamBench.P12RadixFormat → Real
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt => instHPow.hPow fmt.betaR fmt.precision
```

### D009: `HighamBench.P12RadixFormat.scale`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6a88e828c763eb1c5a8f34bdb18576a40d5f6f61cb8e6e52e944c05064802131`

Type:

```lean
HighamBench.P12RadixFormat → Int → Real
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (e : Int) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt e => instHPow.hPow fmt.betaR e
```

### D010: `HighamBench.P12Representation`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `66552fb13211cd9864e1fb0a61a15a50a907336ecc0666099b7c2d9ac5030705`

Type:

```lean
HighamBench.P12RadixFormat → Real → Type
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x : Real) → Type
```

### D011: `HighamBench.P12Representation.exponent`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `94b3c2e3f0ba0a5b00b9fb6e78bfb17ca72edcdd738f82976779dc5ceff211f9`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} → {x : Real} → HighamBench.P12Representation fmt x → Int
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} → {x : Real} → (self : HighamBench.P12Representation fmt x) → Int
```

Definition body (one-level semantic boundary):

```lean
fun fmt x self => self.2
```

### D012: `HighamBench.p12Representable`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8691a63b80faf30a782d588bd11e059d3bb19d347a9be2e73125e9a29646ce32`

Type:

```lean
HighamBench.P12RadixFormat → Real → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt x => Nonempty (HighamBench.P12Representation fmt x)
```

### D013: `HighamBench.P12FastTwoSumExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `f28dba02810eb00e666096914d817e2c6478b73ee41104a83cfe7d11e3a10c5a`

Type:

```lean
∀ {fmt : HighamBench.P12RadixFormat} {x y : Real} {tr : HighamBench.P12FastTwoSumTrace},
  HighamBench.p12NearestInFormat fmt (instHAdd.hAdd x y) tr.s →
    HighamBench.p12FaithfulInFormat fmt (instHSub.hSub tr.s x) tr.t →
      HighamBench.p12FaithfulInFormat fmt (instHSub.hSub y tr.t) tr.e →
        fmt.noOverflow (instHAdd.hAdd x y) →
          fmt.noOverflow (instHSub.hSub tr.s x) →
            fmt.noOverflow (instHSub.hSub y tr.t) → HighamBench.P12FastTwoSumExecution fmt x y tr
```

Fully explicit type:

```lean
∀ {fmt : HighamBench.P12RadixFormat} {x y : Real} {tr : HighamBench.P12FastTwoSumTrace}
  (add :
    HighamBench.p12NearestInFormat fmt (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)
      (HighamBench.P12FastTwoSumTrace.s tr))
  (first_sub :
    HighamBench.p12FaithfulInFormat fmt
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12FastTwoSumTrace.s tr) x)
      (HighamBench.P12FastTwoSumTrace.t tr))
  (second_sub :
    HighamBench.p12FaithfulInFormat fmt
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) y (HighamBench.P12FastTwoSumTrace.t tr))
      (HighamBench.P12FastTwoSumTrace.e tr))
  (add_no_overflow :
    HighamBench.P12RadixFormat.noOverflow fmt
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y))
  (first_sub_no_overflow :
    HighamBench.P12RadixFormat.noOverflow fmt
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12FastTwoSumTrace.s tr) x))
  (second_sub_no_overflow :
    HighamBench.P12RadixFormat.noOverflow fmt
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) y (HighamBench.P12FastTwoSumTrace.t tr))),
  HighamBench.P12FastTwoSumExecution fmt x y tr
```

### D014: `HighamBench.P12FastTwoSumTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `7e1967bc82b8a98cf783796616d87692459541a6d6ba28f5e6b38df8117d6622`

Type:

```lean
Real → Real → Real → HighamBench.P12FastTwoSumTrace
```

Fully explicit type:

```lean
(s t e : Real) → HighamBench.P12FastTwoSumTrace
```

### D015: `HighamBench.P12RadixFormat.beta`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0741ffffe19dd11f26d5487b516e0ca383c70e8c6024589a4dccac058822efba`

Type:

```lean
HighamBench.P12RadixFormat → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P12RadixFormat) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D016: `HighamBench.P12RadixFormat.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1317d4bd617285889f6ec55f3e604baf1f7ea6366d78720d29bb86bb343868cd`

Type:

```lean
(beta precision : Nat) →
  (emin emax : Int) →
    instLENat.le 2 beta → instLTNat.lt 0 precision → Int.instLEInt.le emin emax → HighamBench.P12RadixFormat
```

Fully explicit type:

```lean
(beta precision : Nat) →
  (emin emax : Int) →
    (beta_ge_two : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) beta) →
      (precision_pos :
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) precision) →
        (emin_le_emax : @LE.le.{0} Int Int.instLEInt emin emax) → HighamBench.P12RadixFormat
```

### D017: `HighamBench.P12RadixFormat.precision`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6b2ee34c11be50e7aa7403e47134cccad80b1411183d7f7501e6e66da9fd5696`

Type:

```lean
HighamBench.P12RadixFormat → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P12RadixFormat) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D018: `HighamBench.P12Representation.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `4ff833977434de2ee11c5a4657a5c152f48f5464ba0decc2a02d74036246c588`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} →
    (mantissa exponent : Int) →
      Real.instLT.lt (Real.instNeg.neg fmt.mantissaBound) mantissa.cast →
        Real.instLT.lt mantissa.cast fmt.mantissaBound →
          Int.instLEInt.le fmt.emin exponent →
            Int.instLEInt.le exponent fmt.emax →
              Eq x (instHMul.hMul mantissa.cast (fmt.scale exponent)) → HighamBench.P12Representation fmt x
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} →
    (mantissa exponent : Int) →
      (mantissa_lower :
          @LT.lt.{0} Real Real.instLT (@Neg.neg.{0} Real Real.instNeg (HighamBench.P12RadixFormat.mantissaBound fmt))
            (@Int.cast.{0} Real Real.instIntCast mantissa)) →
        (mantissa_upper :
            @LT.lt.{0} Real Real.instLT (@Int.cast.{0} Real Real.instIntCast mantissa)
              (HighamBench.P12RadixFormat.mantissaBound fmt)) →
          (exponent_lower : @LE.le.{0} Int Int.instLEInt (HighamBench.P12RadixFormat.emin fmt) exponent) →
            (exponent_upper : @LE.le.{0} Int Int.instLEInt exponent (HighamBench.P12RadixFormat.emax fmt)) →
              (value_eq :
                  @Eq.{1} Real x
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Int.cast.{0} Real Real.instIntCast mantissa) (HighamBench.P12RadixFormat.scale fmt exponent))) →
                HighamBench.P12Representation fmt x
```

### D019: `HighamBench.P12RadixFormat.emax`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f38fa848bb32249d357ee953ef7afa5993a158f87d0a6892a13670309d624d28`

Type:

```lean
HighamBench.P12RadixFormat → Int
```

Fully explicit type:

```lean
(self : HighamBench.P12RadixFormat) → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D020: `HighamBench.P12RadixFormat.emin`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cdabd96613e43077d416fac6544c4096da7469b80e621790c4f79f730b4d6e21`

Type:

```lean
HighamBench.P12RadixFormat → Int
```

Fully explicit type:

```lean
(self : HighamBench.P12RadixFormat) → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D021: `HighamBench.P12RadixFormat.noOverflow`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c54879e1cbb5fa40d0432c2b576d60e8fedf1ee2683683c2845c178e79223cea`

Type:

```lean
HighamBench.P12RadixFormat → Real → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (z : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt z => Real.instLT.lt (abs z) (instHMul.hMul fmt.mantissaBound (fmt.scale fmt.emax))
```

### D022: `HighamBench.p12FaithfulInFormat`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b0e8b06f8a120f69d4b19442b95b8de7d5ff64757d0748f35a70b0b2c55eb037`

Type:

```lean
HighamBench.P12RadixFormat → Real → Real → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (exact rounded : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt exact rounded =>
  And (HighamBench.p12Representable fmt rounded)
    (∀ (candidate : Real),
      HighamBench.p12Representable fmt candidate →
        Not
          (Or (And (Real.instLT.lt rounded candidate) (Real.instLE.le candidate exact))
            (And (Real.instLE.le exact candidate) (Real.instLT.lt candidate rounded))))
```

### D023: `HighamBench.p12NearestInFormat`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ad6b455941b1f92027ae2a8113d1913f7e0815af688407353d477ba1f82bd29`

Type:

```lean
HighamBench.P12RadixFormat → Real → Real → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (exact rounded : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt exact rounded => HighamBench.p12Nearest (HighamBench.p12Representable fmt) exact rounded
```

### D024: `HighamBench.p12Nearest`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `edcdf2d37cd85e670605f9af536f80bcc7591a77ea9445f0c81565e1f99760d0`

Type:

```lean
(Real → Prop) → Real → Real → Prop
```

Fully explicit type:

```lean
(representable : Real → Prop) → (exact rounded : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun representable exact rounded =>
  And (representable rounded)
    (∀ (candidate : Real),
      representable candidate →
        Real.instLE.le (abs (instHSub.hSub exact rounded)) (abs (instHSub.hSub exact candidate)))
```

### D025: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D026: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Fully explicit type:

```lean
{G : Type u} → [self : DivInvMonoid.{u} G] → Div.{u} G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D027: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D028: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D029: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HAdd.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D030: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HDiv.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D031: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HMul.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D032: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSub.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D033: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D034: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D035: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

Fully explicit type:

```lean
∀ (n : Nat) [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n],
  Nat.AtLeastTwo
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D036: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ {n : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D037: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Fully explicit type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat.{u} α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D038: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D039: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`

Type:

```lean
Add Real
```

Fully explicit type:

```lean
Add.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ add := Real.add✝ }
```

### D040: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Fully explicit type:

```lean
AddGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D041: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`

Type:

```lean
DivInvMonoid Real
```

Fully explicit type:

```lean
DivInvMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toMonoid := Real.instMonoid, toInv := Real.instInv, div := DivInvMonoid.div',
  div_eq_mul_inv := Real.instDivInvMonoid._proof_1, zpow := zpowRec, zpow_zero' := Real.instDivInvMonoid._proof_2,
  zpow_succ' := Real.instDivInvMonoid._proof_3, zpow_neg' := Real.instDivInvMonoid._proof_4 }
```

### D042: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Fully explicit type:

```lean
LE.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D043: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Fully explicit type:

```lean
Mul.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D044: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Fully explicit type:

```lean
NatCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D045: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Fully explicit type:

```lean
Sub.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D046: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Fully explicit type:

```lean
Lattice.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D047: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`

Type:

```lean
{α : Type u_1} → [Lattice α] → [AddGroup α] → α → α
```

Fully explicit type:

```lean
{α : Type u_1} → [Lattice.{u_1} α] → [AddGroup.{u_1} α] → (a : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D048: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`

Type:

```lean
{α : Type u_1} → [Add α] → HAdd α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
```

### D049: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Div.{u_1} α] → HDiv.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D050: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Mul.{u_1} α] → HMul.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D051: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Sub.{u_1} α] → HSub.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D052: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Fully explicit type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast.{u_1} R] → [Nat.AtLeastTwo n] → OfNat.{u_1} R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D053: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Fully explicit type:

```lean
(n : Nat) → OfNat.{0} Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D054: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1e8b6758b3a3bf88b78eeff1bb4effb1dce39e6b9e38153dab79b664d58d89b5`

Type:

```lean
{M : Type u_2} → [DivInvMonoid M] → Pow M Int
```

Fully explicit type:

```lean
{M : Type u_2} → [DivInvMonoid.{u_2} M] → Pow.{u_2, 0} M Int
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : DivInvMonoid M] => { pow := fun x n => inst.zpow n x }
```

### D055: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HPow.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D056: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D057: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Fully explicit type:

```lean
{M : Type u_2} → [Monoid.{u_2} M] → Pow.{u_2, 0} M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D058: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D059: `Nonempty`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `37c79de378d44cb9dc334502b161bb140da0544579086aded2cf83ff99c462c7`

Type:

```lean
Sort u → Prop
```

Fully explicit type:

```lean
(α : Sort u) → Prop
```

### D060: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Fully explicit type:

```lean
Monoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D061: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow.{u_1, u_2} α β] → HPow.{u_1, u_2, u_1} α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D062: `Int.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3347681a56db726f3d5ec40fea35e331466578d6194deeb554a0c70ba5189971`

Type:

```lean
{R : Type u} → [IntCast R] → Int → R
```

Fully explicit type:

```lean
{R : Type u} → [IntCast.{u} R] → Int → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : IntCast R] => inst.intCast
```

### D063: `Int.instLEInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f51330a4994f7ae8126646c50493b06244696bcf7ecd84ee76d837ba05820e15`

Type:

```lean
LE Int
```

Fully explicit type:

```lean
LE.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ le := Int.le }
```

### D064: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Fully explicit type:

```lean
{α : Type u} → [self : LT.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D065: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Neg.{u} α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D066: `Real.instIntCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7ad2826677bdd498c1fca7a01f5af78c74e38b65a4f1e767cdf3670649eac222`

Type:

```lean
IntCast Real
```

Fully explicit type:

```lean
IntCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ intCast := fun z => { cauchy := z.cast } }
```

### D067: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Fully explicit type:

```lean
LT.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D068: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Fully explicit type:

```lean
Neg.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D069: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Fully explicit type:

```lean
LE.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D070: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Fully explicit type:

```lean
LT.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D071: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Fully explicit type:

```lean
(a : Prop) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D072: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

## Complete local imported sources

### `HighamBench.Core`

Path: `paper_bencmark/highambench/shared/HighamBench/Core.lean`
SHA-256: `8c84e05c04f4245e067d3a971dafa45bcfe92f55bbc24f2305964a8e2b9bd55a`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench common core

This file is deliberately independent of the evaluated library. It contains
only the floating-point model and notation used by more than one benchmark
paper.
-/

namespace HighamBench

open scoped BigOperators

/-- The part of the usual floating-point model needed for ordinary summation. -/
structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- Higham's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- The denominator in `gamma u n` is positive. -/
def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Left-to-right recursive summation, with a one-element sum kept exact. -/
noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

end HighamBench
```

### `HighamBench.P12Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P12Definitions.lean`
SHA-256: `3e58eed419082337e49fab333f872c016fd6c0bec01cc02a9dad52a6033771bb`

```lean
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

/-- The exponent scale `beta^e` used by a particular representation. -/
noncomputable def scale (fmt : P12RadixFormat) (e : ℤ) : ℝ :=
  fmt.betaR ^ e

/-- Explicit range-validity for an exact real operation result.  The strict
upper endpoint matches equation (1) and makes the paper's "absence of
overflow" qualification in equation (8) visible. -/
def noOverflow (fmt : P12RadixFormat) (z : ℝ) : Prop :=
  |z| < fmt.mantissaBound * fmt.scale fmt.emax

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

end P12Representation

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
the representability content of equation (8) and its addition analogue. -/
structure P12RadixGeometry (fmt : P12RadixFormat) : Prop where
  representation_at_or_below_of_abs_lt :
    ∀ {x y : ℝ} (rx : P12Representation fmt x),
      p12Representable fmt y →
      |y| < fmt.mantissaBound * fmt.scale rx.exponent →
      ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent
  add_representation_of_bound :
    ∀ {a b : ℝ} (ra : P12Representation fmt a)
      (rb : P12Representation fmt b),
      fmt.noOverflow (a + b) →
      |a + b| ≤
        fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent) →
      ∃ rsum : P12Representation fmt (a + b),
        min ra.exponent rb.exponent ≤ rsum.exponent
  sub_representation_of_bound :
    ∀ {a b : ℝ} (ra : P12Representation fmt a)
      (rb : P12Representation fmt b),
      fmt.noOverflow (a - b) →
      |a - b| ≤
        fmt.mantissaBound * fmt.scale (min ra.exponent rb.exponent) →
      ∃ rdiff : P12Representation fmt (a - b),
        min ra.exponent rb.exponent ≤ rdiff.exponent
  same_exponent_nearest_add :
    ∀ {x y s : ℝ} (rx : P12Representation fmt x)
      (ry : P12Representation fmt y),
      rx.exponent = ry.exponent →
      |y| ≤
        (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale rx.exponent →
      fmt.noOverflow (x + y) →
      p12NearestInFormat fmt (x + y) s →
      ∃ rs : P12Representation fmt s,
        rx.exponent ≤ rs.exponent ∧
          |s - (x + y)| ≤ fmt.betaR / 2 * fmt.scale rx.exponent
  large_sum_nearest_exponent :
    ∀ {x y s : ℝ} (rx : P12Representation fmt x)
      (ry : P12Representation fmt y),
      ry.exponent < rx.exponent →
      fmt.mantissaBound * fmt.scale ry.exponent < |x + y| →
      fmt.noOverflow (x + y) →
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
      rw [P12RadixFormat.noOverflow, ← heeq, habs] at hno
      exact (lt_irrefl _ hno)
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

private theorem add_representation_of_bound
    {fmt : P12RadixFormat} {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (hno : fmt.noOverflow (a + b))
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
  apply representation_of_integer_multiple_of_bound
    (le_min ra.exponent_lower rb.exponent_lower)
    (le_trans (min_le_left _ _) ra.exponent_upper)
    (ka + kb) hz hno
  simpa [e] using hbound

private theorem sub_representation_of_bound
    {fmt : P12RadixFormat} {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (hno : fmt.noOverflow (a - b))
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
  apply representation_of_integer_multiple_of_bound
    (le_min ra.exponent_lower rb.exponent_lower)
    (le_trans (min_le_left _ _) ra.exponent_upper)
    (ka - kb) hz hno
  simpa [e] using hbound

private theorem large_sum_nearest_exponent
    {fmt : P12RadixFormat} {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (_hryx : ry.exponent < rx.exponent)
    (hlarge : fmt.mantissaBound * fmt.scale ry.exponent < |x + y|)
    (hno : fmt.noOverflow (x + y))
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    ∃ rs : P12Representation fmt s, ry.exponent < rs.exponent := by
  let endpoint := fmt.mantissaBound * fmt.scale ry.exponent
  have hendpoint_pos : 0 < endpoint :=
    mul_pos fmt.mantissaBound_pos (fmt.scale_pos ry.exponent)
  have heplus : ry.exponent + 1 ≤ fmt.emax := by
    by_contra hnot
    have hry_upper := ry.exponent_upper
    have heeq : ry.exponent = fmt.emax := by omega
    rw [P12RadixFormat.noOverflow, ← heeq] at hno
    exact (not_lt_of_ge hlarge.le hno)
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
      (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale rx.exponent)
    (hno : fmt.noOverflow (x + y))
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    ∃ rs : P12Representation fmt s,
      rx.exponent ≤ rs.exponent ∧
        |s - (x + y)| ≤ fmt.betaR / 2 * fmt.scale rx.exponent := by
  let z := x + y
  let e := rx.exponent
  have hscale_pos : 0 < fmt.scale e := fmt.scale_pos e
  have hx_abs := rx.abs_lt_mantissaBound_mul_scale
  have hz_upper :
      |z| < (2 * fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e := by
    calc
      |z| ≤ |x| + |y| := by
        simpa [z] using abs_add_le x y
      _ < fmt.mantissaBound * fmt.scale e + |y| := by
        nlinarith
      _ ≤ fmt.mantissaBound * fmt.scale e +
          (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e := by
        nlinarith
      _ = (2 * fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e := by
        ring
  by_cases hsmall : |z| ≤ fmt.mantissaBound * fmt.scale e
  · have hmin : min rx.exponent ry.exponent = e := by
      simp [e, hsame]
    have hbound : |x + y| ≤
        fmt.mantissaBound *
          fmt.scale (min rx.exponent ry.exponent) := by
      simpa [z, hmin] using hsmall
    rcases add_representation_of_bound rx ry hno hbound with
      ⟨rsum, hrsum⟩
    have hs : s = x + y :=
      p12NearestInFormat_eq_of_representable ⟨rsum⟩ hnearest
    rw [hs]
    refine ⟨rsum, ?_, ?_⟩
    · simpa [e, hmin] using hrsum
    · simp
      exact mul_nonneg (div_nonneg fmt.betaR_pos.le (by norm_num))
        (fmt.scale_pos rx.exponent).le
  · have hlarge : fmt.mantissaBound * fmt.scale e < |z| :=
      lt_of_not_ge hsmall
    have heplus : e + 1 ≤ fmt.emax := by
      by_contra hnot
      have he_upper := rx.exponent_upper
      have heeq : e = fmt.emax := by omega
      rw [P12RadixFormat.noOverflow, ← heeq] at hno
      exact (not_lt_of_ge hlarge.le hno)
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
        2 * fmt.mantissaBound - fmt.betaR / 2 := by
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
        (2 * fmt.mantissaBound - fmt.betaR / 2) / fmt.betaR :=
      div_lt_div_of_pos_right hk_upper fmt.betaR_pos
    have hn_pre : |(n : ℝ)| < 2 * fmt.mantissaBound / fmt.betaR := by
      calc
        |(n : ℝ)| ≤
            |(k : ℝ) / fmt.betaR - (n : ℝ)| +
              |(k : ℝ)| / fmt.betaR := hn_triangle
        _ ≤ 1 / 2 + |(k : ℝ)| / fmt.betaR := by linarith
        _ < 1 / 2 +
            (2 * fmt.mantissaBound - fmt.betaR / 2) / fmt.betaR := by
          linarith
        _ = 2 * fmt.mantissaBound / fmt.betaR := by
          field_simp [ne_of_gt fmt.betaR_pos]
          ring
    have htwo : (2 : ℝ) ≤ fmt.betaR := by
      change (2 : ℝ) ≤ (fmt.beta : ℝ)
      exact_mod_cast fmt.beta_ge_two
    have htwo_bound :
        2 * fmt.mantissaBound / fmt.betaR ≤ fmt.mantissaBound := by
      rw [div_le_iff₀ fmt.betaR_pos]
      nlinarith [fmt.mantissaBound_pos]
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
        |(k : ℝ) - (n : ℝ) * fmt.betaR| ≤ fmt.betaR / 2 := by
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
      nlinarith
    have hcandidate_error :
        |z - candidate| ≤ fmt.betaR / 2 * fmt.scale e := by
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
        |z - s| ≤ fmt.betaR / 2 * fmt.scale e :=
      le_trans (hnearest.2 candidate ⟨rcandidate⟩) hcandidate_error
    have hs_lower :
        (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e < |s| := by
      have htriangle : |z| ≤ |z - s| + |s| := by
        calc
          |z| = |(z - s) + s| := by congr 1 <;> ring
          _ ≤ |z - s| + |s| := abs_add_le _ _
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
            (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e :=
        mul_le_mul_of_nonneg_right
          (mantissaUnit_le_bound_sub_half fmt) hscale_pos.le
      have : |s| <
          (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale e :=
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
  same_exponent_nearest_add := same_exponent_nearest_add
  large_sum_nearest_exponent := large_sum_nearest_exponent

/-- The three returned/intermediate values of Dekker's FastTwoSum algorithm. -/
structure P12FastTwoSumTrace where
  s : ℝ
  t : ℝ
  e : ℝ

/-- One execution of the original three-operation FastTwoSum algorithm from
the paper: nearest addition followed by two uses of the same faithful
subtraction model.  Range validity makes equation (8)'s overflow qualification
explicit without assuming either exact difference is representable. -/
structure P12FastTwoSumExecution (fmt : P12RadixFormat)
    (x y : ℝ) (tr : P12FastTwoSumTrace) : Prop where
  add : p12NearestInFormat fmt (x + y) tr.s
  first_sub : p12FaithfulInFormat fmt (tr.s - x) tr.t
  second_sub : p12FaithfulInFormat fmt (y - tr.t) tr.e
  add_no_overflow : fmt.noOverflow (x + y)
  first_sub_no_overflow : fmt.noOverflow (tr.s - x)
  second_sub_no_overflow : fmt.noOverflow (y - tr.t)

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

/-- The semantic contract of the `TwoProduct` subroutine used in equation (17).
The exact decomposition is delegated background in Lemma 4.  The remaining
fields expose its nearest product, local half-ULP error, radix-grid, and range
properties so that the ThreeProduct proof cannot replace an execution with an
arbitrary decomposition.  Product-grid range obligations are conditional on a
nonzero exact product, preserving Lemma 4's trivial zero case. -/
structure P12TwoProductExecution
    (fmt : P12RadixFormat) {left right : ℝ}
    (leftRep : P12LeastRepresentation fmt left)
    (rightRep : P12LeastRepresentation fmt right)
    (high low : ℝ) where
  highRep : P12LeastRepresentation fmt high
  lowRep : P12LeastRepresentation fmt low
  high_round : p12NearestInFormat fmt (left * right) high
  exact : high + low = left * right
  product_no_overflow : fmt.noOverflow (left * right)
  product_grid_in_range : left * right ≠ 0 →
    fmt.emin ≤ leftRep.exponent + rightRep.exponent ∧
      leftRep.exponent + rightRep.exponent ≤ fmt.emax
  high_nonzero : left * right ≠ 0 → high ≠ 0
  low_error : |low| ≤ (1 / 2) * fmt.scale highRep.exponent
  high_envelope_candidates :
    let bound :=
      fmt.mantissaBound * fmt.scale leftRep.exponent * |right|
    p12Representable fmt bound ∧ p12Representable fmt (-bound)
  grid_preserving :
    ∀ {leftExponent rightExponent : ℤ},
      p12IntegerMultiple fmt left leftExponent →
      p12IntegerMultiple fmt right rightExponent →
      p12IntegerMultiple fmt high (leftExponent + rightExponent) ∧
        p12IntegerMultiple fmt low (leftExponent + rightExponent)

/-- The FastTwoSum trace formed by lines 1--2 of `ThreeProduct` after the three
`TwoProduct` calls have produced the four-term expansion. -/
def P12ThreeProductTrace.mergeTrace
    (tr : P12ThreeProductTrace) : P12FastTwoSumTrace where
  s := tr.s2
  t := tr.t
  e := tr.r

/-- One execution of the paper's `ThreeProduct` procedure.  The range witness
for the middle addition states that nearest rounding is not clipped by an
underflow or overflow boundary at the product grid.  Neither the exact merge
nor representability of the final exact sum is assumed. -/
structure P12ThreeProductExecution
    (fmt : P12RadixFormat) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace) where
  x1Rep : P12LeastRepresentation fmt x1
  x2Rep : P12LeastRepresentation fmt x2
  x3Rep : P12LeastRepresentation fmt x3
  first : P12TwoProductExecution fmt x2Rep x3Rep tr.th tr.tl
  second : P12TwoProductExecution fmt x1Rep first.highRep tr.s1 tr.a2
  third : P12TwoProductExecution fmt x1Rep first.lowRep tr.a3 tr.a4
  merge : P12FastTwoSumExecution fmt tr.a2 tr.a3 tr.mergeTrace
  merge_high_grid :
    p12IntegerMultiple fmt tr.s2
      (x1Rep.exponent + x2Rep.exponent + x3Rep.exponent)
  merge_no_range_error :
    ∃ candidate : ℝ, p12Representable fmt candidate ∧
      |(tr.a2 + tr.a3) - candidate| ≤
        fmt.mantissaBound / 2 *
          fmt.scale (x1Rep.exponent + x2Rep.exponent + x3Rep.exponent)
  final_add : p12NearestInFormat fmt (tr.r + tr.a4) tr.s3
  final_no_overflow : fmt.noOverflow (tr.r + tr.a4)
  triple_grid_in_range : x1 * x2 * x3 ≠ 0 →
    fmt.emin ≤ x1Rep.exponent + x2Rep.exponent + x3Rep.exponent ∧
      x1Rep.exponent + x2Rep.exponent + x3Rep.exponent ≤ fmt.emax

end HighamBench
```
