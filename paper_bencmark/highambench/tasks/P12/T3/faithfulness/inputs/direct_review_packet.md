# Declaration dossier for P12-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p12_t3_three_product_exact
    (fmt : P12RadixFormat) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace)
    (run : P12ThreeProductExecution fmt x1 x2 x3 tr) :
    (∃ ra2 : P12Representation fmt tr.a2,
        |tr.a3| ≤
          (fmt.mantissaBound - fmt.betaR / 2) * fmt.scale ra2.exponent) ∧
      tr.t = tr.s2 - tr.a2 ∧
      tr.r = tr.a3 - tr.t ∧
      tr.s2 + tr.r = tr.a2 + tr.a3 ∧
      tr.s3 = tr.r + tr.a4 ∧
      tr.s1 + tr.s2 + tr.s3 = x1 * x2 * x3
```

## Elaborated target type

```lean
∀ (fmt : HighamBench.P12RadixFormat) (x1 x2 x3 : Real) (tr : HighamBench.P12ThreeProductTrace)
  (run : HighamBench.P12ThreeProductExecution fmt x1 x2 x3 tr),
  And
    (Exists fun ra2 =>
      Real.instLE.le (abs tr.a3)
        (instHMul.hMul (instHSub.hSub fmt.mantissaBound (instHDiv.hDiv fmt.betaR 2)) (fmt.scale ra2.exponent)))
    (And (Eq tr.t (instHSub.hSub tr.s2 tr.a2))
      (And (Eq tr.r (instHSub.hSub tr.a3 tr.t))
        (And (Eq (instHAdd.hAdd tr.s2 tr.r) (instHAdd.hAdd tr.a2 tr.a3))
          (And (Eq tr.s3 (instHAdd.hAdd tr.r tr.a4))
            (Eq (instHAdd.hAdd (instHAdd.hAdd tr.s1 tr.s2) tr.s3) (instHMul.hMul (instHMul.hMul x1 x2) x3))))))
```

## Fully explicit elaborated target type

```lean
∀ (fmt : HighamBench.P12RadixFormat) (x1 x2 x3 : Real) (tr : HighamBench.P12ThreeProductTrace)
  (run : HighamBench.P12ThreeProductExecution fmt x1 x2 x3 tr),
  And
    (@Exists.{1} (HighamBench.P12Representation fmt (HighamBench.P12ThreeProductTrace.a2 tr))
      fun (ra2 : HighamBench.P12Representation fmt (HighamBench.P12ThreeProductTrace.a2 tr)) =>
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup (HighamBench.P12ThreeProductTrace.a3 tr))
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
          (HighamBench.P12RadixFormat.scale fmt
            (@HighamBench.P12Representation.exponent fmt (HighamBench.P12ThreeProductTrace.a2 tr) ra2))))
    (And
      (@Eq.{1} Real (HighamBench.P12ThreeProductTrace.t tr)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12ThreeProductTrace.s2 tr)
          (HighamBench.P12ThreeProductTrace.a2 tr)))
      (And
        (@Eq.{1} Real (HighamBench.P12ThreeProductTrace.r tr)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (HighamBench.P12ThreeProductTrace.a3 tr) (HighamBench.P12ThreeProductTrace.t tr)))
        (And
          (@Eq.{1} Real
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (HighamBench.P12ThreeProductTrace.s2 tr) (HighamBench.P12ThreeProductTrace.r tr))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (HighamBench.P12ThreeProductTrace.a2 tr) (HighamBench.P12ThreeProductTrace.a3 tr)))
          (And
            (@Eq.{1} Real (HighamBench.P12ThreeProductTrace.s3 tr)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (HighamBench.P12ThreeProductTrace.r tr) (HighamBench.P12ThreeProductTrace.a4 tr)))
            (@Eq.{1} Real
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (HighamBench.P12ThreeProductTrace.s1 tr) (HighamBench.P12ThreeProductTrace.s2 tr))
                (HighamBench.P12ThreeProductTrace.s3 tr))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2) x3))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P12Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P12Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P12RadixFormat`

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

### D002: `HighamBench.P12RadixFormat.betaR`

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

### D003: `HighamBench.P12RadixFormat.mantissaBound`

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

### D004: `HighamBench.P12RadixFormat.scale`

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

### D005: `HighamBench.P12Representation`

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

### D006: `HighamBench.P12Representation.exponent`

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

### D007: `HighamBench.P12ThreeProductExecution`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `7b439fd661eb19c11bc1890c7e0bed27f01e6a70063446c40fa46dbdb133b35d`

Type:

```lean
HighamBench.P12RadixFormat → Real → Real → Real → HighamBench.P12ThreeProductTrace → Type
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x1 x2 x3 : Real) → (tr : HighamBench.P12ThreeProductTrace) → Type
```

### D008: `HighamBench.P12ThreeProductTrace`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9fed7af38298cc99b2584602f8dc6a0ecae65b0e3524385d306f1f4945963b4e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D009: `HighamBench.P12ThreeProductTrace.a2`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `289f898f5679c2a96ca1c8d17f6934f7742d6ec4c68888ed4aafe5f38402d989`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D010: `HighamBench.P12ThreeProductTrace.a3`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `77edbaea043595efa13eca92f6e3b1c04d5161e54a7d4235f73f14741172470c`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D011: `HighamBench.P12ThreeProductTrace.a4`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `828d7a6b53ceead32456365013d4a8160538bc8ff2ec3ff6410283d994bb6af7`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D012: `HighamBench.P12ThreeProductTrace.r`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c7b8dc2fffc1ea267c5802c01cb0380b0063444355e3660b4c7d38051a15dea6`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D013: `HighamBench.P12ThreeProductTrace.s1`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5b515b8e9df01ce69fb87b7a40875da2512619a5bce988b0b7ab88fe47d01ae`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D014: `HighamBench.P12ThreeProductTrace.s2`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `453c5b295feb863be4420245e6f5804bd3e6dcb5965719930d27d1e921c25fca`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.7
```

### D015: `HighamBench.P12ThreeProductTrace.s3`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0b3865cb5292f8d930c4cce3f1f10e9b96457792babcc341b8baa898c5d8a9de`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.10
```

### D016: `HighamBench.P12ThreeProductTrace.t`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2354459f682bf1297409ae0d53df6f74d3a641652e499bd3a7a237ac3b28f0f4`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D017: `HighamBench.P12RadixFormat.beta`

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

### D018: `HighamBench.P12RadixFormat.mk`

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

### D019: `HighamBench.P12RadixFormat.precision`

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

### D020: `HighamBench.P12Representation.mk`

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

### D021: `HighamBench.P12ThreeProductExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1595ce6e9b510bbc65ccdd5f2389aca796a44cc6a21f5bd1f3de45937f1236c3`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x1 x2 x3 : Real} →
    {tr : HighamBench.P12ThreeProductTrace} →
      (x1Rep : HighamBench.P12LeastRepresentation fmt x1) →
        (x2Rep : HighamBench.P12LeastRepresentation fmt x2) →
          (x3Rep : HighamBench.P12LeastRepresentation fmt x3) →
            (first : HighamBench.P12TwoProductExecution fmt x2Rep x3Rep tr.th tr.tl) →
              HighamBench.P12TwoProductExecution fmt x1Rep first.highRep tr.s1 tr.a2 →
                HighamBench.P12TwoProductExecution fmt x1Rep first.lowRep tr.a3 tr.a4 →
                  HighamBench.P12FastTwoSumExecution fmt tr.a2 tr.a3 tr.mergeTrace →
                    HighamBench.p12IntegerMultiple fmt tr.s2
                        (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent) →
                      (Exists fun candidate =>
                          And (HighamBench.p12Representable fmt candidate)
                            (Real.instLE.le (abs (instHSub.hSub (instHAdd.hAdd tr.a2 tr.a3) candidate))
                              (instHMul.hMul (instHDiv.hDiv fmt.mantissaBound 2)
                                (fmt.scale
                                  (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent))))) →
                        HighamBench.p12NearestInFormat fmt (instHAdd.hAdd tr.r tr.a4) tr.s3 →
                          fmt.noOverflow (instHAdd.hAdd tr.r tr.a4) →
                            (Ne (instHMul.hMul (instHMul.hMul x1 x2) x3) 0 →
                                And
                                  (Int.instLEInt.le fmt.emin
                                    (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent))
                                  (Int.instLEInt.le
                                    (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent)
                                    fmt.emax)) →
                              HighamBench.P12ThreeProductExecution fmt x1 x2 x3 tr
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x1 x2 x3 : Real} →
    {tr : HighamBench.P12ThreeProductTrace} →
      (x1Rep : HighamBench.P12LeastRepresentation fmt x1) →
        (x2Rep : HighamBench.P12LeastRepresentation fmt x2) →
          (x3Rep : HighamBench.P12LeastRepresentation fmt x3) →
            (first :
                @HighamBench.P12TwoProductExecution fmt x2 x3 x2Rep x3Rep (HighamBench.P12ThreeProductTrace.th tr)
                  (HighamBench.P12ThreeProductTrace.tl tr)) →
              (second :
                  @HighamBench.P12TwoProductExecution fmt x1 (HighamBench.P12ThreeProductTrace.th tr) x1Rep
                    (@HighamBench.P12TwoProductExecution.highRep fmt x2 x3 x2Rep x3Rep
                      (HighamBench.P12ThreeProductTrace.th tr) (HighamBench.P12ThreeProductTrace.tl tr) first)
                    (HighamBench.P12ThreeProductTrace.s1 tr) (HighamBench.P12ThreeProductTrace.a2 tr)) →
                (third :
                    @HighamBench.P12TwoProductExecution fmt x1 (HighamBench.P12ThreeProductTrace.tl tr) x1Rep
                      (@HighamBench.P12TwoProductExecution.lowRep fmt x2 x3 x2Rep x3Rep
                        (HighamBench.P12ThreeProductTrace.th tr) (HighamBench.P12ThreeProductTrace.tl tr) first)
                      (HighamBench.P12ThreeProductTrace.a3 tr) (HighamBench.P12ThreeProductTrace.a4 tr)) →
                  (merge :
                      HighamBench.P12FastTwoSumExecution fmt (HighamBench.P12ThreeProductTrace.a2 tr)
                        (HighamBench.P12ThreeProductTrace.a3 tr) (HighamBench.P12ThreeProductTrace.mergeTrace tr)) →
                    (merge_high_grid :
                        HighamBench.p12IntegerMultiple fmt (HighamBench.P12ThreeProductTrace.s2 tr)
                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                              (@HighamBench.P12Representation.exponent fmt x1
                                (@HighamBench.P12LeastRepresentation.toP12Representation fmt x1 x1Rep))
                              (@HighamBench.P12Representation.exponent fmt x2
                                (@HighamBench.P12LeastRepresentation.toP12Representation fmt x2 x2Rep)))
                            (@HighamBench.P12Representation.exponent fmt x3
                              (@HighamBench.P12LeastRepresentation.toP12Representation fmt x3 x3Rep)))) →
                      (merge_no_range_error :
                          @Exists.{1} Real fun (candidate : Real) =>
                            And (HighamBench.p12Representable fmt candidate)
                              (@LE.le.{0} Real Real.instLE
                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (HighamBench.P12ThreeProductTrace.a2 tr) (HighamBench.P12ThreeProductTrace.a3 tr))
                                    candidate))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (HighamBench.P12RadixFormat.mantissaBound fmt)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                                  (HighamBench.P12RadixFormat.scale fmt
                                    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                        (@HighamBench.P12Representation.exponent fmt x1
                                          (@HighamBench.P12LeastRepresentation.toP12Representation fmt x1 x1Rep))
                                        (@HighamBench.P12Representation.exponent fmt x2
                                          (@HighamBench.P12LeastRepresentation.toP12Representation fmt x2 x2Rep)))
                                      (@HighamBench.P12Representation.exponent fmt x3
                                        (@HighamBench.P12LeastRepresentation.toP12Representation fmt x3 x3Rep))))))) →
                        (final_add :
                            HighamBench.p12NearestInFormat fmt
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (HighamBench.P12ThreeProductTrace.r tr) (HighamBench.P12ThreeProductTrace.a4 tr))
                              (HighamBench.P12ThreeProductTrace.s3 tr)) →
                          (final_no_overflow :
                              HighamBench.P12RadixFormat.noOverflow fmt
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (HighamBench.P12ThreeProductTrace.r tr) (HighamBench.P12ThreeProductTrace.a4 tr))) →
                            (triple_grid_in_range :
                                @Ne.{1} Real
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2) x3)
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                  And
                                    (@LE.le.{0} Int Int.instLEInt (HighamBench.P12RadixFormat.emin fmt)
                                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                          (@HighamBench.P12Representation.exponent fmt x1
                                            (@HighamBench.P12LeastRepresentation.toP12Representation fmt x1 x1Rep))
                                          (@HighamBench.P12Representation.exponent fmt x2
                                            (@HighamBench.P12LeastRepresentation.toP12Representation fmt x2 x2Rep)))
                                        (@HighamBench.P12Representation.exponent fmt x3
                                          (@HighamBench.P12LeastRepresentation.toP12Representation fmt x3 x3Rep))))
                                    (@LE.le.{0} Int Int.instLEInt
                                      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                          (@HighamBench.P12Representation.exponent fmt x1
                                            (@HighamBench.P12LeastRepresentation.toP12Representation fmt x1 x1Rep))
                                          (@HighamBench.P12Representation.exponent fmt x2
                                            (@HighamBench.P12LeastRepresentation.toP12Representation fmt x2 x2Rep)))
                                        (@HighamBench.P12Representation.exponent fmt x3
                                          (@HighamBench.P12LeastRepresentation.toP12Representation fmt x3 x3Rep)))
                                      (HighamBench.P12RadixFormat.emax fmt))) →
                              HighamBench.P12ThreeProductExecution fmt x1 x2 x3 tr
```

### D022: `HighamBench.P12ThreeProductTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d172449bbd7ae28c9391ca6b6804c36b26a5182c00e2723d2f44aa99b2391565`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real → Real → Real → HighamBench.P12ThreeProductTrace
```

Fully explicit type:

```lean
(th tl s1 a2 a3 a4 s2 t r s3 : Real) → HighamBench.P12ThreeProductTrace
```

### D023: `HighamBench.P12FastTwoSumExecution`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `833a4fd2aa477fce008995b87689683174e9251093458eba4d27eef75bfe2820`

Type:

```lean
HighamBench.P12RadixFormat → Real → Real → HighamBench.P12FastTwoSumTrace → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x y : Real) → (tr : HighamBench.P12FastTwoSumTrace) → Prop
```

### D024: `HighamBench.P12LeastRepresentation`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `302962d04521acd1d09ac7a7f82f59fa6724e0e3d0b7b37ebfbfb6efc9840f91`

Type:

```lean
HighamBench.P12RadixFormat → Real → Type
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x : Real) → Type
```

### D025: `HighamBench.P12LeastRepresentation.toP12Representation`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `dcc2955b45e7466038df0e40cfa413b78faa2c4df1103875b7514f107686f0de`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} → HighamBench.P12LeastRepresentation fmt x → HighamBench.P12Representation fmt x
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} → (self : HighamBench.P12LeastRepresentation fmt x) → HighamBench.P12Representation fmt x
```

Definition body (one-level semantic boundary):

```lean
fun fmt x self => self.1
```

### D026: `HighamBench.P12RadixFormat.emax`

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

### D027: `HighamBench.P12RadixFormat.emin`

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

### D028: `HighamBench.P12RadixFormat.noOverflow`

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

### D029: `HighamBench.P12ThreeProductTrace.mergeTrace`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a0ed7257ee0ae731ef1594f3cc0961dc6ecf0e0918cd1dc80fc4ec35c1801fa0`

Type:

```lean
HighamBench.P12ThreeProductTrace → HighamBench.P12FastTwoSumTrace
```

Fully explicit type:

```lean
(tr : HighamBench.P12ThreeProductTrace) → HighamBench.P12FastTwoSumTrace
```

Definition body (one-level semantic boundary):

```lean
fun tr => { s := tr.s2, t := tr.t, e := tr.r }
```

### D030: `HighamBench.P12ThreeProductTrace.th`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef4f8744872c06aa335e817ea788e934c6412092d84ba88ad5d050a85bc11fb2`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D031: `HighamBench.P12ThreeProductTrace.tl`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fb797a747ceba50411d7c9a8a0944efd03596db1f0470f5236b78c217cccc483`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D032: `HighamBench.P12TwoProductExecution`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `ba53740690be40d4fcfd3ce2a46a53fc2276be2a721809a4479a122dabb9c88e`

Type:

```lean
(fmt : HighamBench.P12RadixFormat) →
  {left right : Real} →
    HighamBench.P12LeastRepresentation fmt left → HighamBench.P12LeastRepresentation fmt right → Real → Real → Type
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) →
  {left right : Real} →
    (leftRep : HighamBench.P12LeastRepresentation fmt left) →
      (rightRep : HighamBench.P12LeastRepresentation fmt right) → (high low : Real) → Type
```

### D033: `HighamBench.P12TwoProductExecution.highRep`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `95634763d2777483c0e8c72f6bacd7dd4294a6a42b83fb23730a691a16e4483e`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          HighamBench.P12TwoProductExecution fmt leftRep rightRep high low → HighamBench.P12LeastRepresentation fmt high
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          (self : @HighamBench.P12TwoProductExecution fmt left right leftRep rightRep high low) →
            HighamBench.P12LeastRepresentation fmt high
```

Definition body (one-level semantic boundary):

```lean
fun fmt left right leftRep rightRep high low self => self.1
```

### D034: `HighamBench.P12TwoProductExecution.lowRep`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4721fdd3cb9232bf995c154eeb61e621d98878e609abaf80688f2664bdd2fc56`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          HighamBench.P12TwoProductExecution fmt leftRep rightRep high low → HighamBench.P12LeastRepresentation fmt low
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          (self : @HighamBench.P12TwoProductExecution fmt left right leftRep rightRep high low) →
            HighamBench.P12LeastRepresentation fmt low
```

Definition body (one-level semantic boundary):

```lean
fun fmt left right leftRep rightRep high low self => self.2
```

### D035: `HighamBench.p12IntegerMultiple`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `99f7d23392d52ed66b8159af4264f7a4e8f8b84d4db3523975d32d43c7342e35`

Type:

```lean
HighamBench.P12RadixFormat → Real → Int → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P12RadixFormat) → (x : Real) → (e : Int) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt x e => Exists fun k => Eq x (instHMul.hMul k.cast (fmt.scale e))
```

### D036: `HighamBench.p12NearestInFormat`

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

### D037: `HighamBench.p12Representable`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D038: `HighamBench.P12FastTwoSumExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
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

### D039: `HighamBench.P12FastTwoSumTrace`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `a1b5217c0378ce1b740434d1eb47365d42c1c872f1c39dd028fc0b4d3e3dca6f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D040: `HighamBench.P12FastTwoSumTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `7e1967bc82b8a98cf783796616d87692459541a6d6ba28f5e6b38df8117d6622`

Type:

```lean
Real → Real → Real → HighamBench.P12FastTwoSumTrace
```

Fully explicit type:

```lean
(s t e : Real) → HighamBench.P12FastTwoSumTrace
```

### D041: `HighamBench.P12LeastRepresentation.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2d4d59159a7af7b2506c97dabac598b91c8d3e4bd48e8f3088e2d70ed8b74791`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} →
    (toP12Representation : HighamBench.P12Representation fmt x) →
      (∀ (r : HighamBench.P12Representation fmt x), Int.instLEInt.le toP12Representation.exponent r.exponent) →
        HighamBench.P12LeastRepresentation fmt x
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {x : Real} →
    (toP12Representation : HighamBench.P12Representation fmt x) →
      (least :
          ∀ (r : HighamBench.P12Representation fmt x),
            @LE.le.{0} Int Int.instLEInt (@HighamBench.P12Representation.exponent fmt x toP12Representation)
              (@HighamBench.P12Representation.exponent fmt x r)) →
        HighamBench.P12LeastRepresentation fmt x
```

### D042: `HighamBench.P12TwoProductExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `22213aa97c9201f349c15e097d1db5a5ead0528072c3cd049a3f5f548c62d1f2`

Type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          (highRep : HighamBench.P12LeastRepresentation fmt high) →
            HighamBench.P12LeastRepresentation fmt low →
              HighamBench.p12NearestInFormat fmt (instHMul.hMul left right) high →
                Eq (instHAdd.hAdd high low) (instHMul.hMul left right) →
                  fmt.noOverflow (instHMul.hMul left right) →
                    (Ne (instHMul.hMul left right) 0 →
                        And (Int.instLEInt.le fmt.emin (instHAdd.hAdd leftRep.exponent rightRep.exponent))
                          (Int.instLEInt.le (instHAdd.hAdd leftRep.exponent rightRep.exponent) fmt.emax)) →
                      (Ne (instHMul.hMul left right) 0 → Ne high 0) →
                        Real.instLE.le (abs low) (instHMul.hMul (1 / 2) (fmt.scale highRep.exponent)) →
                          (let bound :=
                              instHMul.hMul (instHMul.hMul fmt.mantissaBound (fmt.scale leftRep.exponent)) (abs right);
                            And (HighamBench.p12Representable fmt bound)
                              (HighamBench.p12Representable fmt (Real.instNeg.neg bound))) →
                            (∀ {leftExponent rightExponent : Int},
                                HighamBench.p12IntegerMultiple fmt left leftExponent →
                                  HighamBench.p12IntegerMultiple fmt right rightExponent →
                                    And
                                      (HighamBench.p12IntegerMultiple fmt high
                                        (instHAdd.hAdd leftExponent rightExponent))
                                      (HighamBench.p12IntegerMultiple fmt low
                                        (instHAdd.hAdd leftExponent rightExponent))) →
                              HighamBench.P12TwoProductExecution fmt leftRep rightRep high low
```

Fully explicit type:

```lean
{fmt : HighamBench.P12RadixFormat} →
  {left right : Real} →
    {leftRep : HighamBench.P12LeastRepresentation fmt left} →
      {rightRep : HighamBench.P12LeastRepresentation fmt right} →
        {high low : Real} →
          (highRep : HighamBench.P12LeastRepresentation fmt high) →
            (lowRep : HighamBench.P12LeastRepresentation fmt low) →
              (high_round :
                  HighamBench.p12NearestInFormat fmt
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) left right) high) →
                (exact :
                    @Eq.{1} Real (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) high low)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) left right)) →
                  (product_no_overflow :
                      HighamBench.P12RadixFormat.noOverflow fmt
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) left right)) →
                    (product_grid_in_range :
                        @Ne.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) left right)
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                          And
                            (@LE.le.{0} Int Int.instLEInt (HighamBench.P12RadixFormat.emin fmt)
                              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                (@HighamBench.P12Representation.exponent fmt left
                                  (@HighamBench.P12LeastRepresentation.toP12Representation fmt left leftRep))
                                (@HighamBench.P12Representation.exponent fmt right
                                  (@HighamBench.P12LeastRepresentation.toP12Representation fmt right rightRep))))
                            (@LE.le.{0} Int Int.instLEInt
                              (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                                (@HighamBench.P12Representation.exponent fmt left
                                  (@HighamBench.P12LeastRepresentation.toP12Representation fmt left leftRep))
                                (@HighamBench.P12Representation.exponent fmt right
                                  (@HighamBench.P12LeastRepresentation.toP12Representation fmt right rightRep)))
                              (HighamBench.P12RadixFormat.emax fmt))) →
                      (high_nonzero :
                          @Ne.{1} Real
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) left right)
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                            @Ne.{1} Real high
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                        (low_error :
                            @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup low)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                                (HighamBench.P12RadixFormat.scale fmt
                                  (@HighamBench.P12Representation.exponent fmt high
                                    (@HighamBench.P12LeastRepresentation.toP12Representation fmt high highRep))))) →
                          (high_envelope_candidates :
                              let bound : Real :=
                                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (HighamBench.P12RadixFormat.mantissaBound fmt)
                                    (HighamBench.P12RadixFormat.scale fmt
                                      (@HighamBench.P12Representation.exponent fmt left
                                        (@HighamBench.P12LeastRepresentation.toP12Representation fmt left leftRep))))
                                  (@abs.{0} Real Real.lattice Real.instAddGroup right);
                              And (HighamBench.p12Representable fmt bound)
                                (HighamBench.p12Representable fmt (@Neg.neg.{0} Real Real.instNeg bound))) →
                            (grid_preserving :
                                ∀ {leftExponent rightExponent : Int},
                                  HighamBench.p12IntegerMultiple fmt left leftExponent →
                                    HighamBench.p12IntegerMultiple fmt right rightExponent →
                                      And
                                        (HighamBench.p12IntegerMultiple fmt high
                                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) leftExponent
                                            rightExponent))
                                        (HighamBench.p12IntegerMultiple fmt low
                                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) leftExponent
                                            rightExponent))) →
                              @HighamBench.P12TwoProductExecution fmt left right leftRep rightRep high low
```

### D043: `HighamBench.p12Nearest`

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

### D044: `HighamBench.P12FastTwoSumTrace.e`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D045: `HighamBench.P12FastTwoSumTrace.s`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D046: `HighamBench.P12FastTwoSumTrace.t`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D047: `HighamBench.p12FaithfulInFormat`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D048: `And`

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

### D049: `DivInvMonoid.toDiv`

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

### D050: `Eq`

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

### D051: `Exists`

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

### D052: `HAdd.hAdd`

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

### D053: `HDiv.hDiv`

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

### D054: `HMul.hMul`

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

### D055: `HSub.hSub`

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

### D056: `LE.le`

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

### D057: `Nat`

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

### D058: `Nat.instAtLeastTwoHAddOfNat`

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

### D059: `Nat.instNeZeroSucc`

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

### D060: `OfNat.ofNat`

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

### D061: `Real`

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

### D062: `Real.instAdd`

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

### D063: `Real.instAddGroup`

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

### D064: `Real.instDivInvMonoid`

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

### D065: `Real.instLE`

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

### D066: `Real.instMul`

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

### D067: `Real.instNatCast`

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

### D068: `Real.instSub`

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

### D069: `Real.lattice`

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

### D070: `abs`

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

### D071: `instHAdd`

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

### D072: `instHDiv`

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

### D073: `instHMul`

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

### D074: `instHSub`

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

### D075: `instOfNatAtLeastTwo`

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

### D076: `instOfNatNat`

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

### D077: `DivInvMonoid.toZPow`

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

### D078: `HPow.hPow`

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

### D079: `Int`

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

### D080: `Monoid.toNatPow`

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

### D081: `Nat.cast`

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

### D082: `Real.instMonoid`

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

### D083: `instHPow`

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

### D084: `Int.cast`

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

### D085: `Int.instAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f3fe827ffb6fc81658773a6ada6451aeb9c1a54d32b216d8dede8eae9142825b`

Type:

```lean
Add Int
```

Fully explicit type:

```lean
Add.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ add := Int.add }
```

### D086: `Int.instLEInt`

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

### D087: `LT.lt`

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

### D088: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (a b : α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D089: `Neg.neg`

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

### D090: `Real.instIntCast`

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

### D091: `Real.instLT`

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

### D092: `Real.instNeg`

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

### D093: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Fully explicit type:

```lean
Zero.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D094: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Fully explicit type:

```lean
{α : Type u_1} → [Zero.{u_1} α] → OfNat.{u_1} α (nat_lit 0)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D095: `instLENat`

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

### D096: `instLTNat`

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

### D097: `Nonempty`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `37c79de378d44cb9dc334502b161bb140da0544579086aded2cf83ff99c462c7`

Type:

```lean
Sort u → Prop
```

Fully explicit type:

```lean
(α : Sort u) → Prop
```

### D098: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Fully explicit type:

```lean
{α : Type u_1} → [One.{u_1} α] → OfNat.{u_1} α (nat_lit 1)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D099: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Fully explicit type:

```lean
One.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D100: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D101: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```
