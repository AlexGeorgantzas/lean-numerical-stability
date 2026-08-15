# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ (fmt : LocalDef001) (x1 x2 x3 : Real) (tr : LocalDef008)
  (run : LocalDef007 fmt x1 x2 x3 tr),
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
∀ (fmt : LocalDef001) (x1 x2 x3 : Real) (tr : LocalDef008)
  (run : LocalDef007 fmt x1 x2 x3 tr),
  And
    (@Exists.{1} (LocalDef005 fmt (LocalDef009 tr))
      fun (ra2 : LocalDef005 fmt (LocalDef009 tr)) =>
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup (LocalDef010 tr))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (LocalDef003 fmt)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (LocalDef002 fmt)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (LocalDef004 fmt
            (@LocalDef006 fmt (LocalDef009 tr) ra2))))
    (And
      (@Eq.{1} Real (LocalDef016 tr)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (LocalDef014 tr)
          (LocalDef009 tr)))
      (And
        (@Eq.{1} Real (LocalDef012 tr)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (LocalDef010 tr) (LocalDef016 tr)))
        (And
          (@Eq.{1} Real
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (LocalDef014 tr) (LocalDef012 tr))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (LocalDef009 tr) (LocalDef010 tr)))
          (And
            (@Eq.{1} Real (LocalDef015 tr)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (LocalDef012 tr) (LocalDef011 tr)))
            (@Eq.{1} Real
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (LocalDef013 tr) (LocalDef014 tr))
                (LocalDef015 tr))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2) x3))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `e9e9215e6d3537ea32d9fb10bf6f9455804915beb41514d3586ea1e906889695`

Type:

```lean
Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `03c195fec72dece4f9a192ae9817181f3999f6355b885b3a3c002b687b4637d6`

Type:

```lean
LocalDef001 → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt => fmt.beta.cast
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fecbead56154f0b704b8757c954ec63c18b3fcf73f8166f18ab5855d63fd9339`

Type:

```lean
LocalDef001 → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt => instHPow.hPow fmt.betaR fmt.precision
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6a88e828c763eb1c5a8f34bdb18576a40d5f6f61cb8e6e52e944c05064802131`

Type:

```lean
LocalDef001 → Int → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt e => instHPow.hPow fmt.betaR e
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `66552fb13211cd9864e1fb0a61a15a50a907336ecc0666099b7c2d9ac5030705`

Type:

```lean
LocalDef001 → Real → Type
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `94b3c2e3f0ba0a5b00b9fb6e78bfb17ca72edcdd738f82976779dc5ceff211f9`

Type:

```lean
{fmt : LocalDef001} → {x : Real} → LocalDef005 fmt x → Int
```

Definition body (one-level semantic boundary):

```lean
fun fmt x self => self.2
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `7b439fd661eb19c11bc1890c7e0bed27f01e6a70063446c40fa46dbdb133b35d`

Type:

```lean
LocalDef001 → Real → Real → Real → LocalDef008 → Type
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9fed7af38298cc99b2584602f8dc6a0ecae65b0e3524385d306f1f4945963b4e`

Type:

```lean
Type
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `289f898f5679c2a96ca1c8d17f6934f7742d6ec4c68888ed4aafe5f38402d989`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `77edbaea043595efa13eca92f6e3b1c04d5161e54a7d4235f73f14741172470c`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `828d7a6b53ceead32456365013d4a8160538bc8ff2ec3ff6410283d994bb6af7`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c7b8dc2fffc1ea267c5802c01cb0380b0063444355e3660b4c7d38051a15dea6`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5b515b8e9df01ce69fb87b7a40875da2512619a5bce988b0b7ab88fe47d01ae`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `453c5b295feb863be4420245e6f5804bd3e6dcb5965719930d27d1e921c25fca`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.7
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0b3865cb5292f8d930c4cce3f1f10e9b96457792babcc341b8baa898c5d8a9de`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.10
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2354459f682bf1297409ae0d53df6f74d3a641652e499bd3a7a237ac3b28f0f4`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0741ffffe19dd11f26d5487b516e0ca383c70e8c6024589a4dccac058822efba`

Type:

```lean
LocalDef001 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1317d4bd617285889f6ec55f3e604baf1f7ea6366d78720d29bb86bb343868cd`

Type:

```lean
(beta precision : Nat) →
  (emin emax : Int) →
    instLENat.le 2 beta → instLTNat.lt 0 precision → Int.instLEInt.le emin emax → LocalDef001
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6b2ee34c11be50e7aa7403e47134cccad80b1411183d7f7501e6e66da9fd5696`

Type:

```lean
LocalDef001 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `4ff833977434de2ee11c5a4657a5c152f48f5464ba0decc2a02d74036246c588`

Type:

```lean
{fmt : LocalDef001} →
  {x : Real} →
    (mantissa exponent : Int) →
      Real.instLT.lt (Real.instNeg.neg fmt.mantissaBound) mantissa.cast →
        Real.instLT.lt mantissa.cast fmt.mantissaBound →
          Int.instLEInt.le fmt.emin exponent →
            Int.instLEInt.le exponent fmt.emax →
              Eq x (instHMul.hMul mantissa.cast (fmt.scale exponent)) → LocalDef005 fmt x
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1595ce6e9b510bbc65ccdd5f2389aca796a44cc6a21f5bd1f3de45937f1236c3`

Type:

```lean
{fmt : LocalDef001} →
  {x1 x2 x3 : Real} →
    {tr : LocalDef008} →
      (x1Rep : LocalDef024 fmt x1) →
        (x2Rep : LocalDef024 fmt x2) →
          (x3Rep : LocalDef024 fmt x3) →
            (first : LocalDef032 fmt x2Rep x3Rep tr.th tr.tl) →
              LocalDef032 fmt x1Rep first.highRep tr.s1 tr.a2 →
                LocalDef032 fmt x1Rep first.lowRep tr.a3 tr.a4 →
                  LocalDef023 fmt tr.a2 tr.a3 tr.mergeTrace →
                    LocalDef035 fmt tr.s2
                        (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent) →
                      (Exists fun candidate =>
                          And (LocalDef037 fmt candidate)
                            (Real.instLE.le (abs (instHSub.hSub (instHAdd.hAdd tr.a2 tr.a3) candidate))
                              (instHMul.hMul (instHDiv.hDiv fmt.mantissaBound 2)
                                (fmt.scale
                                  (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent))))) →
                        LocalDef036 fmt (instHAdd.hAdd tr.r tr.a4) tr.s3 →
                          fmt.noOverflow (instHAdd.hAdd tr.r tr.a4) →
                            (Ne (instHMul.hMul (instHMul.hMul x1 x2) x3) 0 →
                                And
                                  (Int.instLEInt.le fmt.emin
                                    (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent))
                                  (Int.instLEInt.le
                                    (instHAdd.hAdd (instHAdd.hAdd x1Rep.exponent x2Rep.exponent) x3Rep.exponent)
                                    fmt.emax)) →
                              LocalDef007 fmt x1 x2 x3 tr
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d172449bbd7ae28c9391ca6b6804c36b26a5182c00e2723d2f44aa99b2391565`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real → Real → Real → LocalDef008
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `833a4fd2aa477fce008995b87689683174e9251093458eba4d27eef75bfe2820`

Type:

```lean
LocalDef001 → Real → Real → LocalDef039 → Prop
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `302962d04521acd1d09ac7a7f82f59fa6724e0e3d0b7b37ebfbfb6efc9840f91`

Type:

```lean
LocalDef001 → Real → Type
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `dcc2955b45e7466038df0e40cfa413b78faa2c4df1103875b7514f107686f0de`

Type:

```lean
{fmt : LocalDef001} →
  {x : Real} → LocalDef024 fmt x → LocalDef005 fmt x
```

Definition body (one-level semantic boundary):

```lean
fun fmt x self => self.1
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f38fa848bb32249d357ee953ef7afa5993a158f87d0a6892a13670309d624d28`

Type:

```lean
LocalDef001 → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cdabd96613e43077d416fac6544c4096da7469b80e621790c4f79f730b4d6e21`

Type:

```lean
LocalDef001 → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c54879e1cbb5fa40d0432c2b576d60e8fedf1ee2683683c2845c178e79223cea`

Type:

```lean
LocalDef001 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt z => Real.instLT.lt (abs z) (instHMul.hMul fmt.mantissaBound (fmt.scale fmt.emax))
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a0ed7257ee0ae731ef1594f3cc0961dc6ecf0e0918cd1dc80fc4ec35c1801fa0`

Type:

```lean
LocalDef008 → LocalDef039
```

Definition body (one-level semantic boundary):

```lean
fun tr => { s := tr.s2, t := tr.t, e := tr.r }
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef4f8744872c06aa335e817ea788e934c6412092d84ba88ad5d050a85bc11fb2`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fb797a747ceba50411d7c9a8a0944efd03596db1f0470f5236b78c217cccc483`

Type:

```lean
LocalDef008 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `ba53740690be40d4fcfd3ce2a46a53fc2276be2a721809a4479a122dabb9c88e`

Type:

```lean
(fmt : LocalDef001) →
  {left right : Real} →
    LocalDef024 fmt left → LocalDef024 fmt right → Real → Real → Type
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `95634763d2777483c0e8c72f6bacd7dd4294a6a42b83fb23730a691a16e4483e`

Type:

```lean
{fmt : LocalDef001} →
  {left right : Real} →
    {leftRep : LocalDef024 fmt left} →
      {rightRep : LocalDef024 fmt right} →
        {high low : Real} →
          LocalDef032 fmt leftRep rightRep high low → LocalDef024 fmt high
```

Definition body (one-level semantic boundary):

```lean
fun fmt left right leftRep rightRep high low self => self.1
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4721fdd3cb9232bf995c154eeb61e621d98878e609abaf80688f2664bdd2fc56`

Type:

```lean
{fmt : LocalDef001} →
  {left right : Real} →
    {leftRep : LocalDef024 fmt left} →
      {rightRep : LocalDef024 fmt right} →
        {high low : Real} →
          LocalDef032 fmt leftRep rightRep high low → LocalDef024 fmt low
```

Definition body (one-level semantic boundary):

```lean
fun fmt left right leftRep rightRep high low self => self.2
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `99f7d23392d52ed66b8159af4264f7a4e8f8b84d4db3523975d32d43c7342e35`

Type:

```lean
LocalDef001 → Real → Int → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt x e => Exists fun k => Eq x (instHMul.hMul k.cast (fmt.scale e))
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ad6b455941b1f92027ae2a8113d1913f7e0815af688407353d477ba1f82bd29`

Type:

```lean
LocalDef001 → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt exact rounded => LocalDef043 (LocalDef037 fmt) exact rounded
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8691a63b80faf30a782d588bd11e059d3bb19d347a9be2e73125e9a29646ce32`

Type:

```lean
LocalDef001 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt x => Nonempty (LocalDef005 fmt x)
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `f28dba02810eb00e666096914d817e2c6478b73ee41104a83cfe7d11e3a10c5a`

Type:

```lean
∀ {fmt : LocalDef001} {x y : Real} {tr : LocalDef039},
  LocalDef036 fmt (instHAdd.hAdd x y) tr.s →
    LocalDef047 fmt (instHSub.hSub tr.s x) tr.t →
      LocalDef047 fmt (instHSub.hSub y tr.t) tr.e →
        fmt.noOverflow (instHAdd.hAdd x y) →
          fmt.noOverflow (instHSub.hSub tr.s x) →
            fmt.noOverflow (instHSub.hSub y tr.t) → LocalDef023 fmt x y tr
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `a1b5217c0378ce1b740434d1eb47365d42c1c872f1c39dd028fc0b4d3e3dca6f`

Type:

```lean
Type
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `7e1967bc82b8a98cf783796616d87692459541a6d6ba28f5e6b38df8117d6622`

Type:

```lean
Real → Real → Real → LocalDef039
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2d4d59159a7af7b2506c97dabac598b91c8d3e4bd48e8f3088e2d70ed8b74791`

Type:

```lean
{fmt : LocalDef001} →
  {x : Real} →
    (toP12Representation : LocalDef005 fmt x) →
      (∀ (r : LocalDef005 fmt x), Int.instLEInt.le toP12Representation.exponent r.exponent) →
        LocalDef024 fmt x
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `22213aa97c9201f349c15e097d1db5a5ead0528072c3cd049a3f5f548c62d1f2`

Type:

```lean
{fmt : LocalDef001} →
  {left right : Real} →
    {leftRep : LocalDef024 fmt left} →
      {rightRep : LocalDef024 fmt right} →
        {high low : Real} →
          (highRep : LocalDef024 fmt high) →
            LocalDef024 fmt low →
              LocalDef036 fmt (instHMul.hMul left right) high →
                Eq (instHAdd.hAdd high low) (instHMul.hMul left right) →
                  fmt.noOverflow (instHMul.hMul left right) →
                    (Ne (instHMul.hMul left right) 0 →
                        And (Int.instLEInt.le fmt.emin (instHAdd.hAdd leftRep.exponent rightRep.exponent))
                          (Int.instLEInt.le (instHAdd.hAdd leftRep.exponent rightRep.exponent) fmt.emax)) →
                      (Ne (instHMul.hMul left right) 0 → Ne high 0) →
                        Real.instLE.le (abs low) (instHMul.hMul (1 / 2) (fmt.scale highRep.exponent)) →
                          (let bound :=
                              instHMul.hMul (instHMul.hMul fmt.mantissaBound (fmt.scale leftRep.exponent)) (abs right);
                            And (LocalDef037 fmt bound)
                              (LocalDef037 fmt (Real.instNeg.neg bound))) →
                            (∀ {leftExponent rightExponent : Int},
                                LocalDef035 fmt left leftExponent →
                                  LocalDef035 fmt right rightExponent →
                                    And
                                      (LocalDef035 fmt high
                                        (instHAdd.hAdd leftExponent rightExponent))
                                      (LocalDef035 fmt low
                                        (instHAdd.hAdd leftExponent rightExponent))) →
                              LocalDef032 fmt leftRep rightRep high low
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `edcdf2d37cd85e670605f9af536f80bcc7591a77ea9445f0c81565e1f99760d0`

Type:

```lean
(Real → Prop) → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun representable exact rounded =>
  And (representable rounded)
    (∀ (candidate : Real),
      representable candidate →
        Real.instLE.le (abs (instHSub.hSub exact rounded)) (abs (instHSub.hSub exact candidate)))
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `cc3317bbdb2eaa69bc8b7b247535d66ce5c0fef13fe12280bd5801a4ac0f84f9`

Type:

```lean
LocalDef039 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `af611c8df0f69d3f007cfb3f3885d093f4cd4afff8387aa7d47e41db0a02b21a`

Type:

```lean
LocalDef039 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `5a7088d876ae1f159467fb8754df1325283911651abbdf07ea0fba96b9b7bec7`

Type:

```lean
LocalDef039 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b0e8b06f8a120f69d4b19442b95b8de7d5ff64757d0748f35a70b0b2c55eb037`

Type:

```lean
LocalDef001 → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt exact rounded =>
  And (LocalDef037 fmt rounded)
    (∀ (candidate : Real),
      LocalDef037 fmt candidate →
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
