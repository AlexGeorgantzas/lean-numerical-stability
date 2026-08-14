# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {Omega : Type u_1} [inst : MeasurableSpace Omega] {m r : Nat} (model : LocalDef008 Omega)
  (run : LocalDef001 Omega m r model) (c5 : Nat) (lambda : Real),
  instLTNat.lt 0 c5 →
    Real.instLT.lt 0 lambda →
      ∀ (hlocal : LocalDef006 run c5 lambda),
        Exists fun unfactoredRemainder =>
          Exists fun factoredRemainder =>
            And
              (∀ (omega : Omega),
                Set.instMembership.mem hlocal.localEvent omega →
                  LocalDef017 fun u => unfactoredRemainder u omega)
              (And
                (∀ (omega : Omega),
                  Set.instMembership.mem hlocal.localEvent omega →
                    LocalDef017 fun u => factoredRemainder u omega)
                (And
                  (∀ (u : Real) (omega : Omega),
                    Eq (run.computed u omega)
                      (instHAdd.hAdd (LocalDef009 run)
                        (LocalDef016
                          (instHAdd.hAdd (LocalDef012 run u omega)
                            (unfactoredRemainder u omega))
                          run.b)))
                  (And
                    (∀ (u : Real) (omega : Omega),
                      Eq (run.computed u omega)
                        (instHAdd.hAdd (LocalDef009 run)
                          (LocalDef016
                            (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
                              (LocalDef013 run).transpose
                              (instHAdd.hAdd (LocalDef011 run u omega) (factoredRemainder u omega)))
                            run.b)))
                    (∀ (u : Real) (omega : Omega) (j : Fin r),
                      Eq (LocalDef010 run u omega j)
                        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
                          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
                            (LocalDef014
                                (LocalDef015 run.householderVector)
                                (instHAdd.hAdd j.val 1)).transpose
                            (run.localPerturbation u j.val omega))
                          (LocalDef014
                            (LocalDef015 run.householderVector) j.val))))))
```

## Fully explicit elaborated target type

```lean
∀ {Omega : Type u_1} [inst : MeasurableSpace.{u_1} Omega] {m r : Nat} (model : @LocalDef008.{u_1} Omega inst)
  (run : @LocalDef001.{u_1} Omega inst m r model) (c5 : Nat) (lambda : Real)
  (_hc5 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c5)
  (_hlambda :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lambda)
  (hlocal : @LocalDef006.{u_1} Omega inst m r model run c5 lambda),
  @Exists.{u_1 + 1} (Real → Omega → Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
    fun (unfactoredRemainder : Real → Omega → Matrix.{0, 0, 0} (Fin m) (Fin m) Real) =>
    @Exists.{u_1 + 1} (Real → Omega → Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
      fun (factoredRemainder : Real → Omega → Matrix.{0, 0, 0} (Fin m) (Fin m) Real) =>
      And
        (∀ (omega : Omega),
          @Membership.mem.{u_1, u_1} Omega (Set.{u_1} Omega) (@Set.instMembership.{u_1} Omega)
              (@LocalDef007.{u_1} Omega inst m r model run c5 lambda hlocal)
              omega →
            @LocalDef017 m fun (u : Real) => unfactoredRemainder u omega)
        (And
          (∀ (omega : Omega),
            @Membership.mem.{u_1, u_1} Omega (Set.{u_1} Omega) (@Set.instMembership.{u_1} Omega)
                (@LocalDef007.{u_1} Omega inst m r model run c5 lambda hlocal)
                omega →
              @LocalDef017 m fun (u : Real) => factoredRemainder u omega)
          (And
            (∀ (u : Real) (omega : Omega),
              @Eq.{1} (Fin m → Real)
                (@LocalDef003.{u_1} Omega inst m r model run u omega)
                (@HAdd.hAdd.{0, 0, 0} (Fin m → Real) (Fin m → Real) (Fin m → Real)
                  (@instHAdd.{0} (Fin m → Real)
                    (@Pi.instAdd.{0, 0} (Fin m) (fun (a : Fin m) => Real) fun (i : Fin m) => Real.instAdd))
                  (@LocalDef009.{u_1} Omega inst m r model run)
                  (@LocalDef016 m m
                    (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                      (Matrix.{0, 0, 0} (Fin m) (Fin m) Real) (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                      (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                        (@Matrix.add.{0, 0, 0} (Fin m) (Fin m) Real Real.instAdd))
                      (@LocalDef012.{u_1} Omega inst m r model run u omega)
                      (unfactoredRemainder u omega))
                    (@LocalDef002.{u_1} Omega inst m r model run))))
            (And
              (∀ (u : Real) (omega : Omega),
                @Eq.{1} (Fin m → Real)
                  (@LocalDef003.{u_1} Omega inst m r model run u omega)
                  (@HAdd.hAdd.{0, 0, 0} (Fin m → Real) (Fin m → Real) (Fin m → Real)
                    (@instHAdd.{0} (Fin m → Real)
                      (@Pi.instAdd.{0, 0} (Fin m) (fun (a : Fin m) => Real) fun (i : Fin m) => Real.instAdd))
                    (@LocalDef009.{u_1} Omega inst m r model run)
                    (@LocalDef016 m m
                      (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                        (Matrix.{0, 0, 0} (Fin m) (Fin m) Real) (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin m) (Fin m) Real
                          (Fin.fintype m) Real.instMul Real.instAddCommMonoid)
                        (@Matrix.transpose.{0, 0, 0} (Fin m) (Fin m) Real
                          (@LocalDef013.{u_1} Omega inst m r model run))
                        (@HAdd.hAdd.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                          (Matrix.{0, 0, 0} (Fin m) (Fin m) Real) (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                          (@instHAdd.{0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                            (@Matrix.add.{0, 0, 0} (Fin m) (Fin m) Real Real.instAdd))
                          (@LocalDef011.{u_1} Omega inst m r model run u omega)
                          (factoredRemainder u omega)))
                      (@LocalDef002.{u_1} Omega inst m r model run))))
              (∀ (u : Real) (omega : Omega) (j : Fin r),
                @Eq.{1} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                  (@LocalDef010.{u_1} Omega inst m r model run u omega j)
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real) (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                    (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin m) (Fin m) Real
                      (Fin.fintype m) Real.instMul Real.instAddCommMonoid)
                    (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                      (Matrix.{0, 0, 0} (Fin m) (Fin m) Real) (Matrix.{0, 0, 0} (Fin m) (Fin m) Real)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin m) (Fin m) Real
                        (Fin.fintype m) Real.instMul Real.instAddCommMonoid)
                      (@Matrix.transpose.{0, 0, 0} (Fin m) (Fin m) Real
                        (@LocalDef014 m
                          (@LocalDef015 m
                            (@LocalDef004.{u_1} Omega inst m r model
                              run))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val r j)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@LocalDef005.{u_1} Omega inst m r model run u
                        (@Fin.val r j) omega))
                    (@LocalDef014 m
                      (@LocalDef015 m
                        (@LocalDef004.{u_1} Omega inst m r model run))
                      (@Fin.val r j)))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `7a2cacf26b73f015a8a59d6f0d3548f326ab7855e64f321c1408116c9e81069b`

Type:

```lean
(Omega : Type u_1) → [inst : MeasurableSpace Omega] → Nat → Nat → LocalDef008 Omega → Type u_1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8a1ff762e8459a4c24eafe942ec37f10963d01c8c151966f8e23d604aa29be13`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun Omega [MeasurableSpace Omega] m r model self => self.3
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `87411603158a5313d47d2db052bbf8010615c27d5a66fdd0f38b35514d911ed2`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Real → Omega → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun Omega [MeasurableSpace Omega] m r model self => self.6
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `221f5087c99458e25a28e298bd3b654d1d4655b33a213fdf51facb6251078e72`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Nat → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun Omega [MeasurableSpace Omega] m r model self => self.4
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `07662cbf21fb517dcf8bc4aaaeb7d21204520fde40a979761071c30b8b30620e`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Real → Nat → Omega → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun Omega [MeasurableSpace Omega] m r model self => self.5
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `3cd92508b19f666d70e9a24b85abd98b9df788deead70a48402149ff78e2e85b`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Nat → Real → Type u_1
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5b0da5cfdf2c4bafdbd43c5b20f50e8f8a3e39ad8689bb2d27522f5494e0a692`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        {run : LocalDef001 Omega m r model} →
          {c5 : Nat} → {lambda : Real} → LocalDef006 run c5 lambda → Set Omega
```

Definition body (one-level semantic boundary):

```lean
fun Omega [MeasurableSpace Omega] m r model run c5 lambda self => self.1
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `60af93828a964deb2634f1c4e6a0efa3b09c47b526796436a1e2bd861da0e62f`

Type:

```lean
(Ω : Type u_1) → [MeasurableSpace Ω] → Type u_1
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `25bb992e0e47fd8cdd3b395ef40e4d599a789e20f56256d31a08575c371dc07a`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} [MeasurableSpace Omega] {m r} {model} run =>
  LocalDef016
    (LocalDef014 (LocalDef015 run.householderVector) r) run.b
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `08dc73ddcf48315280c912176839de1b5bb5a15a1ba9babf599bd007c6c8abae`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Real → Omega → Fin r → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} [MeasurableSpace Omega] {m r} {model} run u omega j =>
  LocalDef025 (LocalDef015 run.householderVector)
    run.localPerturbation u omega j.val
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `954ba6785702dc73d1414705d54535442330c129670569ea1e41fc17e329411d`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Real → Omega → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} [MeasurableSpace Omega] {m r} {model} run u omega =>
  LocalDef026 (LocalDef015 run.householderVector)
    run.localPerturbation u omega r
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `03686ea2dfb239bbe312ba5daf4b728bc5d110cca28ebd0ab4a40d5fbe79cad8`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Real → Omega → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} [MeasurableSpace Omega] {m r} {model} run u omega =>
  LocalDef021 (LocalDef015 run.householderVector)
    run.localPerturbation u omega r
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `984b577f1061943a6abf9b1ec446796e8b5036fc20b8ce5e462aa8932db44fdf`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        LocalDef001 Omega m r model → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} [MeasurableSpace Omega] {m r} {model} run =>
  (LocalDef014 (LocalDef015 run.householderVector) r).transpose
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `31749fd91a83c236be1a97720f1398b2a67082550c2aceff88446adfcbef2964`

Type:

```lean
{m : Nat} → (Nat → Matrix (Fin m) (Fin m) Real) → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} P x =>
  Nat.brecOn x fun x f =>
    LocalDef023 (fun x => Nat.below x → Matrix (Fin m) (Fin m) Real) x (fun _ x => 1)
      (fun k x => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (P k) x.1) f
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0aada6b8b2a80076b870afc0b0c72024c5e290e7d59208fd763478a32714cc49`

Type:

```lean
{m : Nat} → (Nat → Fin m → Real) → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} v j => LocalDef022 (v j)
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `893dee110847631319ce412fdc634324446f2cfd73af2c3a356c467875edecc9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dbca21097e489bd870d00da8c31febc7486be53f9ad0f08ebf5510caa695fec4`

Type:

```lean
{m : Nat} → (Real → Matrix (Fin m) (Fin m) Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} remainder => LocalDef024 remainder fun u => instHPow.hPow u 2
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `279e9654375b275b01b81a7cf8aa79ac0d361a909b4d882caf0dd51a074a412d`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        instLTNat.lt 0 m →
          instLTNat.lt 0 r →
            (b : Fin m → Real) →
              (householderVector : Nat → Fin m → Real) →
                (localPerturbation : Real → Nat → Omega → Matrix (Fin m) (Fin m) Real) →
                  (computed : Real → Omega → Fin m → Real) →
                    (outputIndex : Fin m → Fin model.operationCount) →
                      (∀ (j : Nat),
                          instLTNat.lt j r → Eq (Finset.univ.sum fun i => instHPow.hPow (householderVector j i) 2) 2) →
                        (∀ (j : Nat),
                            instLTNat.lt j r →
                              Eq
                                (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
                                  (LocalDef015 householderVector j)
                                  (LocalDef015 householderVector j))
                                1) →
                          (∀ (u : Real) (omega : Omega),
                              Eq (computed u omega)
                                (LocalDef016
                                  (LocalDef034
                                    (LocalDef015 householderVector) localPerturbation u
                                    omega r)
                                  b)) →
                            (∀ (omega : Omega) (i : Fin m),
                                Eq (computed model.unitRoundoff omega i) (model.computedValue (outputIndex i) omega)) →
                              LocalDef001 Omega m r model
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e8656ac489e6fee8f7960d4971b2d437d0869e36ec108c6477135a591e449f2f`

Type:

```lean
{Omega : Type u_1} →
  [inst : MeasurableSpace Omega] →
    {m r : Nat} →
      {model : LocalDef008 Omega} →
        {run : LocalDef001 Omega m r model} →
          {c5 : Nat} →
            {lambda : Real} →
              (localEvent : Set Omega) →
                MeasurableSet localEvent →
                  (∀ (omega : Omega),
                      Iff (Set.instMembership.mem localEvent omega)
                        (∀ (j : Fin r),
                          LocalDef036 (run.localPerturbation model.unitRoundoff j.val omega)
                            (instHMul.hMul c5.cast (LocalDef032 m lambda model.unitRoundoff)))) →
                    (∀ (omega : Omega),
                        Set.instMembership.mem localEvent omega →
                          ∀ (j : Nat),
                            instLTNat.lt j r →
                              LocalDef024 (fun u => run.localPerturbation u j omega)
                                fun u => u) →
                      Eq (MeasureTheory.Measure.instFunLike.coe model.probability localEvent) 1 →
                        LocalDef006 run c5 lambda
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `8367bb6c2bdb218092e462451a20aeb1ee71aa0e60c0909a2a6f019f88a33eaa`

Type:

```lean
{Ω : Type u_1} →
  [inst : MeasurableSpace Ω] →
    (probability : MeasureTheory.Measure Ω) →
      Eq (MeasureTheory.Measure.instFunLike.coe probability Set.univ) 1 →
        (operationCount : Nat) →
          (exactValue computedValue error : Fin operationCount → Ω → Real) →
            (unitRoundoff : Real) →
              Real.instLE.le 0 unitRoundoff →
                Real.instLT.lt unitRoundoff 1 →
                  (∀ (k : Fin operationCount) (omega : Ω),
                      Eq (computedValue k omega)
                        (instHMul.hMul (exactValue k omega) (instHAdd.hAdd 1 (error k omega)))) →
                    (∀ (k : Fin operationCount) (omega : Ω), Real.instLE.le (abs (error k omega)) unitRoundoff) →
                      (∀ (k : Fin operationCount), Measurable (error k)) →
                        (∀ (k : Fin operationCount), MeasureTheory.Integrable (error k) probability) →
                          (∀ (k : Fin operationCount),
                              Eq (MeasureTheory.integral probability fun omega => error k omega) 0) →
                            LocalDef033 probability error → LocalDef008 Ω
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `addbee013cb38e4a424c3e3966d1b5682a52a1960bd83662b4a892c324713423`

Type:

```lean
{Omega : Type u_1} →
  {m : Nat} →
    (Nat → Matrix (Fin m) (Fin m) Real) →
      (Real → Nat → Omega → Matrix (Fin m) (Fin m) Real) → Real → Omega → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} {m} P DeltaP x x_1 x_2 =>
  Nat.brecOn (motive := fun x => Real → Omega → Matrix (Fin m) (Fin m) Real) x_2
    (fun x f x_3 x_4 =>
      LocalDef035
        (fun x x_5 x_6 =>
          Nat.below (motive := fun x => Real → Omega → Matrix (Fin m) (Fin m) Real) x_6 → Matrix (Fin m) (Fin m) Real)
        x_3 x_4 x (fun x x_5 x_6 => 0)
        (fun u omega k x =>
          instHAdd.hAdd (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (P k) (x.1 u omega))
            (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (DeltaP u k omega)
              (LocalDef014 P k)))
        f)
    x x_1
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b1eaf54b5999b23d1e3d6ae1b007b70a8ce197affea30728c0924aecac3463dd`

Type:

```lean
{m : Nat} → (Fin m → Real) → Fin m → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} v i j => instHSub.hSub (LocalDef031 i j) (instHMul.hMul (v i) (v j))
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `7643423c3313f6af7168bfe4e0a07185eb8838773ff097827d065b90d7e0a1e0`

Type:

```lean
(motive : Nat → Sort u_1) → (x : Nat) → (Unit → motive 0) → ((k : Nat) → motive k.succ) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 Unit.unit) fun n => h_2 n
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `75e6f85118df8d8e971fec68218922b6370311fcd9abe18f64cffe4abbc9e820`

Type:

```lean
{m : Nat} → (Real → Matrix (Fin m) (Fin m) Real) → (Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} A scale => ∀ (i j : Fin m), Asymptotics.IsBigO (nhds 0) (fun u => A u i j) scale
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cb18e8a95f7e072d81913ada4f23bc984134869a622013c8ac443e0823ca1289`

Type:

```lean
{Omega : Type u_1} →
  {m : Nat} →
    (Nat → Matrix (Fin m) (Fin m) Real) →
      (Real → Nat → Omega → Matrix (Fin m) (Fin m) Real) → Real → Omega → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} {m} P DeltaP u omega j =>
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul
      (LocalDef014 P (instHAdd.hAdd j 1)).transpose (DeltaP u j omega))
    (LocalDef014 P j)
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aa349b5cd939b157f7eea77efb261ea0405bf4bd9d6f0f0384749ab1aa909eb3`

Type:

```lean
{Omega : Type u_1} →
  {m : Nat} →
    (Nat → Matrix (Fin m) (Fin m) Real) →
      (Real → Nat → Omega → Matrix (Fin m) (Fin m) Real) → Real → Omega → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} {m} P DeltaP u omega k =>
  (Finset.range k).sum fun j => LocalDef025 P DeltaP u omega j
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `82e8cda2d5e40b810989ef80bc376f6222d78181a8dac0aae8b579843444bf00`

Type:

```lean
{Ω : Type u_1} → [inst : MeasurableSpace Ω] → (self : LocalDef008 Ω) → Fin self.operationCount → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun Ω [MeasurableSpace Ω] self => self.5
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `370763b5f3e323fed5cebe7a9324a27d2b395dfc17c3dadeccbad4bb7a9748a0`

Type:

```lean
{Ω : Type u_1} → [inst : MeasurableSpace Ω] → LocalDef008 Ω → Nat
```

Definition body (one-level semantic boundary):

```lean
fun Ω [MeasurableSpace Ω] self => self.3
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cc5498c4b0871cdba19639711bfd4c6a66ad1af76ff561a1e763db1d5033bcf9`

Type:

```lean
{Ω : Type u_1} → [inst : MeasurableSpace Ω] → LocalDef008 Ω → MeasureTheory.Measure Ω
```

Definition body (one-level semantic boundary):

```lean
fun Ω [MeasurableSpace Ω] self => self.1
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `26dc1e048fd8bc759ed31f93ffe40ce8bb3ab2d74da5704b06d6ed24991b76c1`

Type:

```lean
{Ω : Type u_1} → [inst : MeasurableSpace Ω] → LocalDef008 Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun Ω [MeasurableSpace Ω] self => self.7
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a9037c406664bfc13b1a434dbaf41ca104afd808a9ca85949e0dd52361ad6016`

Type:

```lean
{ι : Type u_1} → [DecidableEq ι] → ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [DecidableEq ι] i j => ite (Eq i j) 1 0
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb3c5cdb87252caeb2361d4b462375f2c9798d3c399f9a0be7d368fbcdb85286`

Type:

```lean
Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun k lambda u =>
  instHSub.hSub
    (Real.exp
      (instHDiv.hDiv
        (instHAdd.hAdd (instHMul.hMul (instHMul.hMul lambda k.cast.sqrt) u) (instHMul.hMul k.cast (instHPow.hPow u 2)))
        (instHSub.hSub 1 u)))
    1
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6075a71c7b10ac0dc3461cc651ce324e9eb8fb6b9367e7d07be3b7deb3c6024b`

Type:

```lean
{Ω : Type u_1} → [inst : MeasurableSpace Ω] → MeasureTheory.Measure Ω → {steps : Nat} → (Fin steps → Ω → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [MeasurableSpace Ω] mu {steps} error =>
  ∀ (k : Fin steps) (g : (Fin k.val → Real) → Real),
    MeasureTheory.Integrable (fun omega => g (LocalDef037 error k omega)) mu →
      MeasureTheory.Integrable
          (fun omega => instHMul.hMul (g (LocalDef037 error k omega)) (error k omega)) mu →
        Eq
          (MeasureTheory.integral mu fun omega =>
            instHMul.hMul (g (LocalDef037 error k omega)) (error k omega))
          (instHMul.hMul (MeasureTheory.integral mu fun omega => g (LocalDef037 error k omega))
            (MeasureTheory.integral mu fun omega => error k omega))
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3e2611a23f5bc4f73eff5c5d6d1791d39495bb9208a952270a1e1104a10092b5`

Type:

```lean
{Omega : Type u_1} →
  {m : Nat} →
    (Nat → Matrix (Fin m) (Fin m) Real) →
      (Real → Nat → Omega → Matrix (Fin m) (Fin m) Real) → Real → Omega → Nat → Matrix (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} {m} P DeltaP x x_1 x_2 =>
  Nat.brecOn (motive := fun x => Real → Omega → Matrix (Fin m) (Fin m) Real) x_2
    (fun x f x_3 x_4 =>
      LocalDef035
        (fun x x_5 x_6 =>
          Nat.below (motive := fun x => Real → Omega → Matrix (Fin m) (Fin m) Real) x_6 → Matrix (Fin m) (Fin m) Real)
        x_3 x_4 x (fun x x_5 x_6 => 1)
        (fun u omega k x =>
          Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (instHAdd.hAdd (P k) (DeltaP u k omega)) (x.1 u omega))
        f)
    x x_1
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `43ffa850e10bc416015d5dece29e9b3275d6df29e34ed317715ef40e96c8612a`

Type:

```lean
{Omega : Type u_2} →
  (motive : Real → Omega → Nat → Sort u_1) →
    (x : Real) →
      (x_1 : Omega) →
        (x_2 : Nat) →
          ((x : Real) → (x_3 : Omega) → motive x x_3 0) →
            ((u : Real) → (omega : Omega) → (k : Nat) → motive u omega k.succ) → motive x x_1 x_2
```

Definition body (one-level semantic boundary):

```lean
fun {Omega} motive x x_1 x_2 h_1 h_2 => Nat.casesOn x_2 (h_1 x x_1) fun n => h_2 x x_1 n
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2f0f3a599fcba43fced25539e0ee05f966cef66bd1dec61d355e81e51e2bc1f9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A L =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (LocalDef038 (LocalDef016 A x)) (instHMul.hMul L (LocalDef038 x))
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `8f87c320beb50905d80d2218af1665bdf4cfcf451764cfd7746c4ad54d64b88f`

Type:

```lean
{Ω : Type u_1} → {steps : Nat} → (Fin steps → Ω → Real) → (k : Fin steps) → Ω → Fin k.val → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} {steps} error k omega i => error ⟨i.val, ⋯⟩ omega
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `641a08c9509bcfec9f54c8dcf330d38cf5a97f59688d88c388269019be35f39d`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `5b210c22a7b2c02ac85221a296eb3c60253e4d9b0acc57829d574af5f56afe45`

Type:

```lean
∀ {steps : Nat} (k : Fin steps) (i : Fin k.val), Nat.instPreorder.lt i.val steps
```

### D040: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D041: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D042: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D043: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D044: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D045: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D046: `HAdd.hAdd`

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

### D047: `HMul.hMul`

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

### D048: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D049: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D050: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D051: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8eecda35a630fe4097c6149154c07645e87eaf089a78dde5ca01f180806c2a40`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} → [Fintype m] → [Mul α] → [AddCommMonoid α] → HMul (Matrix l m α) (Matrix m n α) (Matrix l n α)
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {α} [Fintype m] [Mul α] [AddCommMonoid α] =>
  { hMul := fun M N i k => dotProduct (fun j => M i j) fun j => N j k }
```

### D052: `Matrix.transpose`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a0ee2c3649fa412f4b56ce3f375ef2f2d84b6b21507e1c4a93e90d3b9562973e`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Matrix m n α → Matrix n m α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} M => EquivLike.toFunLike.coe Matrix.of fun x y => M y x
```

### D053: `MeasurableSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `6825e55082259c6be2028d5ee0624c796293eccdd78af118da4583180067d196`

Type:

```lean
Type u_7 → Type u_7
```

### D054: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `941ea3346e809f919727c21bfcdeea342714a6b83f1cf871d648aa2cb14d6e9e`

Type:

```lean
{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} γ [self : Membership α γ] => self.1
```

### D055: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D056: `OfNat.ofNat`

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

### D057: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D058: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D059: `Real.instAdd`

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

### D060: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D061: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D062: `Real.instMul`

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

### D063: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D064: `Set`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a6e551515032966c16e4f42e4548ff1854c2dce05ffe51e98b66943caecc78ec`

Type:

```lean
Type u → Type u
```

Definition body (one-level semantic boundary):

```lean
fun α => α → Prop
```

### D065: `Set.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5858be77d319c5a0e238602f16818ed6fb2e2b52a81ff7edb07bc219d652f201`

Type:

```lean
{α : Type u} → Membership α (Set α)
```

Definition body (one-level semantic boundary):

```lean
fun {α} => { mem := Set.Mem }
```

### D066: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D067: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D068: `instHAdd`

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

### D069: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D070: `instOfNatNat`

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

### D071: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D072: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D073: `HPow.hPow`

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

### D074: `Matrix.one`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b68e4dde96dc7da148aa68eb622604137a0c2dec462b5c39bdd02d8b07d2a59d`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → [One α] → One (Matrix n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] [One α] => { one := Matrix.diagonal fun x => 1 }
```

### D075: `Monoid.toNatPow`

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

### D076: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D077: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D078: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D079: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D080: `Real.instMonoid`

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

### D081: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D082: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D083: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D084: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D085: `instHPow`

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

### D086: `AddCommMonoidWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `07f48d3cfc3c7c30b6298df8531409d9844ab8c7e0ba94dea2a3fd29879320af`

Type:

```lean
{R : Type u_2} → [self : AddCommMonoidWithOne R] → AddMonoidWithOne R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddCommMonoidWithOne R] => self.1
```

### D087: `AddMonoidWithOne.toOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2ee638fd7292dbcf1e4adb85b14bbd0f304e8a260316e61621bf8eac03f03f6d`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → One R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.3
```

### D088: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D089: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D090: `ENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5b8f4d61311ebccecf6a54ceca44191d394e0108c8596129a77f03c15a7e457f`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
WithTop NNReal
```

### D091: `Finset.range`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Range`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0d8947d3b91a57604f7b7be615f2ff236f2058a47281af31ea2498635666e9e7`

Type:

```lean
Nat → Finset Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => { val := Multiset.range n, nodup := ⋯ }
```

### D092: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D093: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

### D094: `InnerProductSpace.toNormedSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.InnerProductSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `683435a8d27d50ec1482d74d23f541d52d05ff0411c60f88d16c32132aca9f3e`

Type:

```lean
{𝕜 : Type u_4} →
  {E : Type u_5} →
    {inst : RCLike 𝕜} → {inst_1 : SeminormedAddCommGroup E} → [self : InnerProductSpace 𝕜 E] → NormedSpace 𝕜 E
```

Definition body (one-level semantic boundary):

```lean
fun 𝕜 E {inst} {inst_1} [self : InnerProductSpace 𝕜 E] => self.1
```

### D095: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D096: `Matrix.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6b893d81bc298230772e16cd0c8ddf7d2638ac0d6127094b06a1290d88f8c3ae`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [AddCommMonoid α] → AddCommMonoid (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [AddCommMonoid α] => Pi.addCommMonoid
```

### D097: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D098: `Measurable`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6d56983cd98232a62c5c1b4a0368519a8b381777b32b6e8301ade2ccd7f4c3a4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [MeasurableSpace α] → [MeasurableSpace β] → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [MeasurableSpace α] [MeasurableSpace β] f =>
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (Set.preimage f t)
```

### D099: `MeasurableSet`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.MeasurableSpace.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2e9235174f4747f2e37b86692acc96182e23810c202fe6e159a326c4a72cf4ff`

Type:

```lean
{α : Type u_1} → [MeasurableSpace α] → Set α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : MeasurableSpace α] s => inst.MeasurableSet' s
```

### D100: `MeasureTheory.Integrable`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.Function.L1Space.Integrable`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `51e5158e8f2f2a375463d510858200b96afa04fb8f33126da2c5d1c572a76165`

Type:

```lean
{ε : Type u_5} →
  [inst : TopologicalSpace ε] →
    [ContinuousENorm ε] →
      {α : Type u_8} →
        {x : MeasurableSpace α} → (α → ε) → autoParam (MeasureTheory.Measure α) MeasureTheory.Integrable._auto_1 → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ε} [TopologicalSpace ε] [ContinuousENorm ε] {α} {x} f μ =>
  And (MeasureTheory.AEStronglyMeasurable f μ) (MeasureTheory.HasFiniteIntegral f μ)
```

### D101: `MeasureTheory.Measure`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `ba8c23c70f3135407096406cee0b4d7d9f02d088e8b1d1a1e105071821a3a51b`

Type:

```lean
(α : Type u_6) → [MeasurableSpace α] → Type u_6
```

### D102: `MeasureTheory.Measure.instFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `94b2becf9230ce3d438e9b668f79f08e69dbe28c937b1aaca32d96e94b64a5b2`

Type:

```lean
{α : Type u_1} → [inst : MeasurableSpace α] → FunLike (MeasureTheory.Measure α) (Set α) ENNReal
```

Definition body (one-level semantic boundary):

```lean
fun {α} [MeasurableSpace α] =>
  { coe := fun μ => MeasureTheory.OuterMeasure.instFunLikeSetENNReal.coe μ.toOuterMeasure, coe_injective' := ⋯ }
```

### D103: `MeasureTheory.integral`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `428563f3d6b771605a3267457bf33b62ec2efa91a42b57b96121b85c0269a9ab`

Type:

```lean
{α : Type u_6} →
  {G : Type u_7} →
    [inst : NormedAddCommGroup G] →
      [NormedSpace Real G] → {x : MeasurableSpace α} → MeasureTheory.Measure α → (α → G) → G
```

Definition body (one-level semantic boundary):

```lean
MeasureTheory.wrapped✝.1
```

### D104: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D105: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D106: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D107: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D108: `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c697ff5e735ebe18733e51950717037e73ba73e94ac2e99953bfb521708cabd2`

Type:

```lean
{α : Type u_5} → [self : NonUnitalSeminormedCommRing α] → NonUnitalSeminormedRing α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalSeminormedCommRing α] => self.1
```

### D109: `NonUnitalSeminormedRing.toSeminormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `db7996fa414ad67340b9d6991cd145ac2a5d251a870097d20f2f63e371fb101d`

Type:

```lean
{α : Type u_2} → [NonUnitalSeminormedRing α] → SeminormedAddCommGroup α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : NonUnitalSeminormedRing α] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddCommGroup := __src.toAddCommGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D110: `NormedAddCommGroup.toSeminormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7327759e5e9417c54393e7566584cd72d79c77b4ca018ea408c5d024667587be`

Type:

```lean
{E : Type u_5} → [NormedAddCommGroup E] → SeminormedAddCommGroup E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : NormedAddCommGroup E] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddCommGroup := __src.toAddCommGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D111: `NormedCommRing.toSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ad504b2606febc5a066d58ac540c9826bd1b7fce734d59a7fef63c7c27112fe3`

Type:

```lean
{α : Type u_2} → [β : NormedCommRing α] → SeminormedCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : NormedCommRing α] =>
  { toNorm := β.toNorm, toRing := β.toRing, toPseudoMetricSpace := β.toPseudoMetricSpace, dist_eq := ⋯,
    norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D112: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D113: `RCLike.toInnerProductSpaceReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.InnerProductSpace.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f602276baee30d3dbe02bd6b756a9097f750d59a7f91ca7635dcfc935fd22981`

Type:

```lean
{𝕜 : Type u_1} → [inst : RCLike 𝕜] → InnerProductSpace Real 𝕜
```

Definition body (one-level semantic boundary):

```lean
fun {𝕜} [RCLike 𝕜] =>
  let __spread.0 := Inner.rclikeToReal 𝕜 𝕜;
  { toNormedSpace := NormedAlgebra.toNormedSpace 𝕜, toInner := __spread.0, norm_sq_eq_re_inner := ⋯,
    conj_inner_symm := ⋯, add_left := ⋯, smul_left := ⋯ }
```

### D114: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D115: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D116: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D117: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`

Type:

```lean
RCLike Real
```

Definition body (one-level semantic boundary):

```lean
{ toDenselyNormedField := Real.denselyNormedField, toStarRing := instStarRingReal,
  toNormedAlgebra := NormedAlgebra.id Real, toCompleteSpace := Real.instCompleteSpace, re := AddMonoidHom.id Real,
  im := 0, I := 0, I_re_ax := Real.instRCLike._proof_1, I_mul_I_ax := Real.instRCLike._proof_8, re_add_im_ax := ⋯,
  ofReal_re_ax := Real.instRCLike._proof_11, ofReal_im_ax := Real.instRCLike._proof_12, mul_re_ax := ⋯, mul_im_ax := ⋯,
  conj_re_ax := ⋯, conj_im_ax := ⋯, conj_I_ax := Real.instRCLike._proof_7, norm_sq_eq_def_ax := ⋯, mul_im_I_ax := ⋯,
  toPartialOrder := Real.partialOrder, le_iff_re_im := @Real.instRCLike._proof_13, toDecidableEq := Real.decidableEq }
```

### D118: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D119: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D120: `Real.measurableSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `51b107725c4edbe40e50ff5651a2c7ee5a10037e341c2764964a6d6cc26d82a1`

Type:

```lean
MeasurableSpace Real
```

Definition body (one-level semantic boundary):

```lean
borel Real
```

### D121: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```

### D122: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```

### D123: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `69cccc1e864661e103785f4a2712b9ad164d845c03b7737801c37e5ac852bad7`

Type:

```lean
NormedCommRing Real
```

Definition body (one-level semantic boundary):

```lean
let __src := Real.normedAddCommGroup;
let __src_1 := Real.commRing;
{ toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := Real.normedCommRing._proof_1,
  toMul := __src_1.toMul, left_distrib := Real.normedCommRing._proof_2, right_distrib := Real.normedCommRing._proof_3,
  zero_mul := Real.normedCommRing._proof_4, mul_zero := Real.normedCommRing._proof_5,
  mul_assoc := Real.normedCommRing._proof_6, toOne := __src_1.toOne, one_mul := Real.normedCommRing._proof_7,
  mul_one := Real.normedCommRing._proof_8, toNatCast := __src_1.toNatCast, natCast_zero := Real.normedCommRing._proof_9,
  natCast_succ := Real.normedCommRing._proof_10, npow := __src_1.npow, npow_zero := Real.normedCommRing._proof_11,
  npow_succ := Real.normedCommRing._proof_12, toNeg := __src.toNeg, toSub := __src.toSub,
  sub_eq_add_neg := Real.normedCommRing._proof_13, zsmul := __src.zsmul, zsmul_zero' := Real.normedCommRing._proof_14,
  zsmul_succ' := Real.normedCommRing._proof_15, zsmul_neg' := Real.normedCommRing._proof_16,
  neg_add_cancel := Real.normedCommRing._proof_17, toIntCast := __src_1.toIntCast,
  intCast_ofNat := Real.normedCommRing._proof_18, intCast_negSucc := Real.normedCommRing._proof_19,
  toMetricSpace := __src.toMetricSpace, dist_eq := ⋯, norm_mul_le := Real.normedCommRing._proof_20, mul_comm := ⋯ }
```

### D124: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9c0d1d56a04dd3ae3fce36b5fb3c2f4fe632c2bdaed84b5667c1a60a03491a3e`

Type:

```lean
PseudoMetricSpace Real
```

Definition body (one-level semantic boundary):

```lean
{ dist := fun x y => abs (instHSub.hSub x y), dist_self := Real.pseudoMetricSpace._proof_1, dist_comm := ⋯,
  dist_triangle := ⋯, edist_dist := Real.pseudoMetricSpace._proof_2, uniformity_dist := Real.pseudoMetricSpace._proof_3,
  cobounded_sets := Real.pseudoMetricSpace._proof_4 }
```

### D125: `SeminormedAddCommGroup.toSeminormedAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8cf35215f509cdee10a3a95158cbaadd3c5fb584bc0d1f4fad6ecfc69b1bd205`

Type:

```lean
{E : Type u_5} → [SeminormedAddCommGroup E] → SeminormedAddGroup E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : SeminormedAddCommGroup E] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddGroup := __src.toAddGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D126: `SeminormedAddGroup.toContinuousENorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Continuity`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `17a83cbf3059dd0bbaefd43c93ce329f1d6b760d440889322b3582a18b23a141`

Type:

```lean
{E : Type u_4} → [inst : SeminormedAddGroup E] → ContinuousENorm E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [SeminormedAddGroup E] => { toENorm := NNNorm.toENorm, continuous_enorm := ⋯ }
```

### D127: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a29f0377c9baf2265c34aaf85b852e7c4260b34d2dc04574484c335ebc09a6e9`

Type:

```lean
{α : Type u_2} → [β : SeminormedCommRing α] → NonUnitalSeminormedCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : SeminormedCommRing α] =>
  { toNorm := β.toNorm, toAddMonoid := β.toAddMonoid, toNeg := β.toNeg, toSub := β.toSub, sub_eq_add_neg := ⋯,
    zsmul := β.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯,
    toMul := β.toMul, left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    toPseudoMetricSpace := β.toPseudoMetricSpace, dist_eq := ⋯, norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D128: `Set.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4a477fd0b844ae25dae2fe8488226265a7c6b23c8087f3feda3f6197172b13e7`

Type:

```lean
{α : Type u} → Set α
```

Definition body (one-level semantic boundary):

```lean
fun {α} => setOf fun _a => True
```

### D129: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D130: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D131: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D132: `instAddCommMonoidWithOneENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `31d9551885e3007e5d1368365622cfd7638ea41cc6d885234041621de873f55c`

Type:

```lean
AddCommMonoidWithOne ENNReal
```

Definition body (one-level semantic boundary):

```lean
WithTop.addCommMonoidWithOne
```

### D133: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D134: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D135: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```

### D136: `DecidableEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ceb5edcca38a0d8e0cbe42efd319eed4e877a75211690cacfd89ee5799fb1004`

Type:

```lean
Sort u → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun α => (a b : α) → Decidable (Eq a b)
```

### D137: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D138: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D139: `Real.exp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Exponential`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `69806b1af98b09fabed435ccc47a9f2f0840f9c5c140fb62cccc81a80761a984`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => (Complex.exp (Complex.ofReal x)).re
```

### D140: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D141: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D142: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D143: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D144: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D145: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D146: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `8fcf5a8f5a8899408a8cdc310bc44f6f7b84a21905a114103fbc65083f779a43`

Type:

```lean
{α : Type u_2} → [self : Preorder α] → LT α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Preorder α] => self.2
```
