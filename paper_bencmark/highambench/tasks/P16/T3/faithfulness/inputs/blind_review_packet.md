# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} (run : LocalDef003 n),
  And (Real.instLE.le 0 (LocalDef021 run))
      (Real.instLT.lt (LocalDef021 run) 1) →
    Exists fun backwardRemainder =>
      Exists fun forwardRemainder =>
        And (Eq backwardRemainder fun i => (run.restart i).theorem41.backwardRemainder)
          (And (Eq forwardRemainder fun i => (run.restart i).theorem41.forwardRemainder)
            (And (LocalDef023 run.uHigh run.uLow backwardRemainder)
              (And (LocalDef023 run.uHigh run.uLow forwardRemainder)
                (And
                  (∀ (i : Nat),
                    Real.instLE.le (LocalDef017 run.A run.b (run.xHat (instHAdd.hAdd i 1)))
                      (instHAdd.hAdd
                        (instHAdd.hAdd
                          (instHMul.hMul (LocalDef021 run)
                            (LocalDef017 run.A run.b (run.xHat i)))
                          (LocalDef018 run))
                        (abs (backwardRemainder i))))
                  (And
                    (∀ (i : Nat),
                      Real.instLE.le (LocalDef022 run.xExact (run.xHat (instHAdd.hAdd i 1)))
                        (instHAdd.hAdd
                          (instHAdd.hAdd
                            (instHMul.hMul (LocalDef021 run)
                              (LocalDef022 run.xExact (run.xHat i)))
                            (LocalDef019 run))
                          (abs (forwardRemainder i))))
                    (And
                      (LocalDef020 (LocalDef021 run)
                        (LocalDef018 run) run.uHigh run.uLow backwardRemainder fun i =>
                        LocalDef017 run.A run.b (run.xHat i))
                      (LocalDef020 (LocalDef021 run)
                        (LocalDef019 run) run.uHigh run.uLow forwardRemainder fun i =>
                        LocalDef022 run.xExact (run.xHat i))))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : LocalDef003 n)
  (hLambda :
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@LocalDef021 n run))
      (@LT.lt.{0} Real Real.instLT (@LocalDef021 n run)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @Exists.{1} (Nat → Real) fun (backwardRemainder : Nat → Real) =>
    @Exists.{1} (Nat → Real) fun (forwardRemainder : Nat → Real) =>
      And
        (@Eq.{1} (Nat → Real) backwardRemainder fun (i : Nat) =>
          @LocalDef015 n
            (@LocalDef004 n run)
            (@LocalDef005 n run)
            (@LocalDef006 n run)
            (@LocalDef013 n run)
            (@LocalDef014 n run i)
            (@LocalDef014 n run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@LocalDef011 n run)
            (@LocalDef001 n
              (@LocalDef004 n run)
              (@LocalDef005 n run)
              (@LocalDef006 n run)
              (@LocalDef013 n run)
              (@LocalDef014 n run i)
              (@LocalDef014 n run
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@LocalDef009 n run i)
              (@LocalDef007 n run i)
              (@LocalDef011 n run)
              (@LocalDef012 n run)
              (@LocalDef008 n run)
              (@LocalDef010 n run i))
            (@LocalDef008 n run)
            (@LocalDef002 n
              (@LocalDef004 n run)
              (@LocalDef005 n run)
              (@LocalDef006 n run)
              (@LocalDef013 n run)
              (@LocalDef014 n run i)
              (@LocalDef014 n run
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@LocalDef009 n run i)
              (@LocalDef007 n run i)
              (@LocalDef011 n run)
              (@LocalDef012 n run)
              (@LocalDef008 n run)
              (@LocalDef010 n run i)))
        (And
          (@Eq.{1} (Nat → Real) forwardRemainder fun (i : Nat) =>
            @LocalDef016 n
              (@LocalDef004 n run)
              (@LocalDef005 n run)
              (@LocalDef006 n run)
              (@LocalDef013 n run)
              (@LocalDef014 n run i)
              (@LocalDef014 n run
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@LocalDef011 n run)
              (@LocalDef001 n
                (@LocalDef004 n run)
                (@LocalDef005 n run)
                (@LocalDef006 n run)
                (@LocalDef013 n run)
                (@LocalDef014 n run i)
                (@LocalDef014 n run
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@LocalDef009 n run i)
                (@LocalDef007 n run i)
                (@LocalDef011 n run)
                (@LocalDef012 n run)
                (@LocalDef008 n run)
                (@LocalDef010 n run i))
              (@LocalDef008 n run)
              (@LocalDef002 n
                (@LocalDef004 n run)
                (@LocalDef005 n run)
                (@LocalDef006 n run)
                (@LocalDef013 n run)
                (@LocalDef014 n run i)
                (@LocalDef014 n run
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@LocalDef009 n run i)
                (@LocalDef007 n run i)
                (@LocalDef011 n run)
                (@LocalDef012 n run)
                (@LocalDef008 n run)
                (@LocalDef010 n run i)))
          (And
            (LocalDef023 (@LocalDef011 n run)
              (@LocalDef012 n run) backwardRemainder)
            (And
              (LocalDef023 (@LocalDef011 n run)
                (@LocalDef012 n run) forwardRemainder)
              (And
                (∀ (i : Nat),
                  @LE.le.{0} Real Real.instLE
                    (@LocalDef017 n (@LocalDef004 n run)
                      (@LocalDef006 n run)
                      (@LocalDef014 n run
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@LocalDef021 n run)
                          (@LocalDef017 n (@LocalDef004 n run)
                            (@LocalDef006 n run)
                            (@LocalDef014 n run i)))
                        (@LocalDef018 n run))
                      (@abs.{0} Real Real.lattice Real.instAddGroup (backwardRemainder i))))
                (And
                  (∀ (i : Nat),
                    @LE.le.{0} Real Real.instLE
                      (@LocalDef022 n (@LocalDef013 n run)
                        (@LocalDef014 n run
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@LocalDef021 n run)
                            (@LocalDef022 n (@LocalDef013 n run)
                              (@LocalDef014 n run i)))
                          (@LocalDef019 n run))
                        (@abs.{0} Real Real.lattice Real.instAddGroup (forwardRemainder i))))
                  (And
                    (LocalDef020 (@LocalDef021 n run)
                      (@LocalDef018 n run)
                      (@LocalDef011 n run)
                      (@LocalDef012 n run) backwardRemainder fun (i : Nat) =>
                      @LocalDef017 n (@LocalDef004 n run)
                        (@LocalDef006 n run)
                        (@LocalDef014 n run i))
                    (LocalDef020 (@LocalDef021 n run)
                      (@LocalDef019 n run)
                      (@LocalDef011 n run)
                      (@LocalDef012 n run) forwardRemainder fun (i : Nat) =>
                      @LocalDef022 n (@LocalDef013 n run)
                        (@LocalDef014 n run i))))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e103834780415701ab3161b4ac36be726d3941a4b094ecf67239479bd986257c`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext residualHat correctionHat : LocalDef028 n} →
      {uHigh uLow dimensionFactor : Real} →
        LocalDef024 A Ainv b xExact xCurrent xNext residualHat correctionHat uHigh uLow
            dimensionFactor →
          Real
```

Definition body (one-level semantic boundary):

```lean
fun n A Ainv b xExact xCurrent xNext residualHat correctionHat uHigh uLow dimensionFactor self => self.63
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f425f848dd5fa444fcadaa0d533279ee795901c119f6cff18c34559af79e9ed9`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext residualHat correctionHat : LocalDef028 n} →
      {uHigh uLow dimensionFactor : Real} →
        (self :
            LocalDef024 A Ainv b xExact xCurrent xNext residualHat correctionHat uHigh
              uLow dimensionFactor) →
          LocalDef027 A Ainv b xExact xCurrent xNext uHigh self.modularAccuracy
            dimensionFactor
```

Definition body (one-level semantic boundary):

```lean
fun n A Ainv b xExact xCurrent xNext residualHat correctionHat uHigh uLow dimensionFactor self => self.66
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `55036cd282f86279334ebb1a10162482fa61b9f352a4a8453759143a45c0fe7b`

Type:

```lean
Nat → Type
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `84464cc71c0fd1a362e81b05cab85669d9eb3a9507de46b49c9701b8a07df37a`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef026 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d07c0f63ae9a843539c1635ea39da348fcc0c4fc74862aa8440c2324b850b7f8`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef026 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c3218555d4b8c371a555c60c671d8f5b1eebe37e0018715ce24bb4807b9824e4`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bb3cc0c11a9d0b31371bde7eb9f89e63d46dee6ca8de94a7b26ff816dc3ef679`

Type:

```lean
{n : Nat} → LocalDef003 n → Nat → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.8
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b37e5a8a25db37e154d18c479506d5981954771334f70ea51c8190631580ffbb`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.13
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `01dc025f8feb9aaf3fff835b4bf492e284251a0ee8037e7f3454275d3a2f172c`

Type:

```lean
{n : Nat} → LocalDef003 n → Nat → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a0d33a827524a23c55f3f2a9995070d6d5ba77bf5a699559f92ce3cab93f1b0f`

Type:

```lean
{n : Nat} →
  (self : LocalDef003 n) →
    (i : Nat) →
      LocalDef024 self.A self.Ainv self.b self.xExact (self.xHat i)
        (self.xHat (instHAdd.hAdd i 1)) (self.residualHat i) (self.correctionHat i) self.uHigh self.uLow
        self.dimensionFactor
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.30
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cd2ac4d493bb1bd1edb37aa4f91b6d7f69ccecfc8b787056575f25ba026d51d4`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c1aeef9945c0840f4393dbb63df4e40b51a227703ebb844878da8252c84a3753`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.12
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8cd1649b7fdb35e870a6d9f4b671662fb75051335be59c09047c8c6078123b75`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ea45c0013c483a71dc307e984639752349c207a45d9bb0f356df067685086662`

Type:

```lean
{n : Nat} → LocalDef003 n → Nat → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1f51e0a0721aa8f07a5c04f7edc9eb822d6c2a895480f94440b7315889d1776b`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext : LocalDef028 n} →
      {uHigh modularAccuracy dimensionFactor : Real} →
        LocalDef027 A Ainv b xExact xCurrent xNext uHigh modularAccuracy dimensionFactor →
          Real
```

Definition body (one-level semantic boundary):

```lean
fun n A Ainv b xExact xCurrent xNext uHigh modularAccuracy dimensionFactor self => self.5
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `68b06ee9e0c5f5af46926043aa462cfa88103797e11405377bef206e84094a15`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext : LocalDef028 n} →
      {uHigh modularAccuracy dimensionFactor : Real} →
        LocalDef027 A Ainv b xExact xCurrent xNext uHigh modularAccuracy dimensionFactor →
          Real
```

Definition body (one-level semantic boundary):

```lean
fun n A Ainv b xExact xCurrent xNext uHigh modularAccuracy dimensionFactor self => self.6
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f393da23f12434756d498c11e9e2ae4d991fc118a94873a36622b66697bd62ec`

Type:

```lean
{n : Nat} → LocalDef026 n → LocalDef028 n → LocalDef028 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat => LocalDef030 A b xHat
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6228e86d59c8e646843929db99fed46aa3348d58a18d032abdefd3b193390b84`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run => instHMul.hMul run.dimensionFactor run.uHigh
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `10199084b735673b71ceec2f5770424e0bfd5cc5f7893c0ed3c334adef2efc9c`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  instHMul.hMul (instHMul.hMul run.dimensionFactor run.uHigh) (LocalDef029 run.A run.Ainv)
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7efac87eafd88ebb265309ebfd5736d101287a11a7e70f576051c37c7563d5d0`

Type:

```lean
Real → Real → Real → Real → (Nat → Real) → (Nat → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun lambda floor uHigh uLow remainder error =>
  Exists fun C =>
    And (Real.instLE.le 0 C)
      (And
        (∀ (i : Nat), Real.instLE.le (abs (remainder i)) (instHMul.hMul C (instHPow.hPow (instHAdd.hAdd uHigh uLow) 2)))
        (∀ (m : Nat),
          Real.instLE.le (error m)
            (instHAdd.hAdd (instHMul.hMul (instHPow.hPow lambda m) (error 0))
              (instHDiv.hDiv (instHAdd.hAdd floor (instHMul.hMul C (instHPow.hPow (instHAdd.hAdd uHigh uLow) 2)))
                (instHSub.hSub 1 lambda)))))
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ef0be0f713d143858ff02b3900099409cab0295ae80f657ea5bd319dd0869a1`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  instHMul.hMul (instHMul.hMul run.dimensionFactor run.uLow) (LocalDef029 run.A run.Ainv)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ae31da5e50aa0dd2d17a75257cdee20c66bc769f6b0c93726fb999724b14518`

Type:

```lean
{n : Nat} → LocalDef028 n → LocalDef028 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (LocalDef031 (instHSub.hSub xHat x)) (LocalDef031 x)
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `af1257f0f7b11de919008a112197798018c6c8d5d51b3cfbcce3cabcc9ce7ea0`

Type:

```lean
Real → Real → (Nat → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun uHigh uLow remainder =>
  Exists fun C =>
    And (Real.instLE.le 0 C)
      (∀ (i : Nat), Real.instLE.le (abs (remainder i)) (instHMul.hMul C (instHPow.hPow (instHAdd.hAdd uHigh uLow) 2)))
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `0cc6d5c75242ee1f191c5920edce1a40f66290a41d33c14fef461166e8212657`

Type:

```lean
{n : Nat} →
  LocalDef026 n →
    LocalDef026 n →
      LocalDef028 n →
        LocalDef028 n →
          LocalDef028 n →
            LocalDef028 n → LocalDef028 n → LocalDef028 n → Real → Real → Real → Type
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1f22273a152f34a084fcbccc49baf5548b8f123455818b4483c135685a082bae`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv : LocalDef026 n) →
      (b xExact : LocalDef028 n) →
        (xHat residualHat correctionHat residualError updateError : Nat → LocalDef028 n) →
          (uHigh uLow dimensionFactor : Real) →
            Ne b 0 →
              LocalDef037 A →
                (∀ (z : LocalDef028 n), Eq (LocalDef038 Ainv (LocalDef038 A z)) z) →
                  (∀ (z : LocalDef028 n), Eq (LocalDef038 A (LocalDef038 Ainv z)) z) →
                    Eq (LocalDef038 A xExact) b →
                      Real.instLT.lt 0 uHigh →
                        Real.instLT.lt 0 uLow →
                          Real.instLE.le uHigh uLow →
                            Real.instLE.le 0 dimensionFactor →
                              LocalDef032 uHigh n →
                                LocalDef032 uLow n →
                                  Real.instLE.le (LocalDef035 uHigh n) (instHMul.hMul dimensionFactor uHigh) →
                                    (∀ (i : Nat),
                                        Eq (residualHat i)
                                          (instHAdd.hAdd (LocalDef039 A b (xHat i)) (residualError i))) →
                                      (∀ (i : Nat) (j : Fin n),
                                          Real.instLE.le (abs (residualError i j))
                                            (instHMul.hMul (LocalDef035 uHigh n)
                                              (instHAdd.hAdd (abs (b j))
                                                (LocalDef038 (fun row col => abs (A row col))
                                                  (fun col => abs (xHat i col)) j)))) →
                                        (∀ (i : Nat),
                                            Eq (xHat (instHAdd.hAdd i 1))
                                              (instHAdd.hAdd (instHAdd.hAdd (xHat i) (correctionHat i))
                                                (updateError i))) →
                                          (∀ (i : Nat) (j : Fin n),
                                              Real.instLE.le (abs (updateError i j))
                                                (instHMul.hMul uHigh (abs (xHat (instHAdd.hAdd i 1) j)))) →
                                            (restart :
                                                (i : Nat) →
                                                  LocalDef024 A Ainv b xExact (xHat i)
                                                    (xHat (instHAdd.hAdd i 1)) (residualHat i) (correctionHat i) uHigh
                                                    uLow dimensionFactor) →
                                              (iterateCurrentNextRemainder iterateNextExactRemainder : Nat → Real) →
                                                (∀ (i : Nat),
                                                    Real.instLE.le (LocalDef031 (xHat i))
                                                      (instHAdd.hAdd (LocalDef031 (xHat (instHAdd.hAdd i 1)))
                                                        (abs (iterateCurrentNextRemainder i)))) →
                                                  (∀ (i : Nat),
                                                      Real.instLE.le (LocalDef031 (xHat (instHAdd.hAdd i 1)))
                                                        (instHAdd.hAdd (LocalDef031 xExact)
                                                          (abs (iterateNextExactRemainder i)))) →
                                                    LocalDef023 uHigh uLow
                                                        iterateCurrentNextRemainder →
                                                      LocalDef023 uHigh uLow
                                                          iterateNextExactRemainder →
                                                        (LocalDef023 uHigh uLow fun i =>
                                                            (restart i).theorem41.backwardRemainder) →
                                                          (LocalDef023 uHigh uLow fun i =>
                                                              (restart i).theorem41.forwardRemainder) →
                                                            LocalDef003 n
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `36b086346c3347b53ec18d195e2ddb2540e7ae44e2039744f1587ecb712cd8f4`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `0dce4bdcb51883502f44accbe0a7bf014a6e236ecbb7de2a1b1180d4cc3a135a`

Type:

```lean
{n : Nat} →
  LocalDef026 n →
    LocalDef026 n →
      LocalDef028 n →
        LocalDef028 n → LocalDef028 n → LocalDef028 n → Real → Real → Real → Type
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b643f0f6e4b56118846938b88a1ae79ef2b1849df9e9a3440a9ac88a10e94782`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aad128e1ff242bef74849f83be7b08fd1b3bf6883dc807497f55a0fff18e7456`

Type:

```lean
{n : Nat} → LocalDef026 n → LocalDef026 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef036 Ainv) (LocalDef036 A)
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fcb08c14cdc1ff672554092cd5e6a93c5458a19a318e4c8f88e0e1ba2906b439`

Type:

```lean
{n : Nat} → LocalDef026 n → LocalDef028 n → LocalDef028 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat =>
  instHDiv.hDiv (LocalDef031 (LocalDef039 A b xHat))
    (instHAdd.hAdd (instHMul.hMul (LocalDef036 A) (LocalDef031 xHat)) (LocalDef031 b))
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `bd8e44de2b8f8d577e4ee9f3b2ffb202461eebd6324f041a2f505422a111cd66`

Type:

```lean
{n : Nat} → LocalDef028 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `651ef903a8d9a3c8f539284f6c70325cebe6e199aad808cb56d9123f31e258c9`

Type:

```lean
Real → Nat → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u n => Real.instLT.lt (instHMul.hMul n.cast u) 1
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `bee5eb576f7cca24080510e9b176ecf4ed7287c64a5c58c11194e25420f63381`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext residualHat correctionHat : LocalDef028 n} →
      {uHigh uLow dimensionFactor : Real} →
        (keyDimension : Nat) →
          instLTNat.lt 0 keyDimension →
            instLENat.le keyDimension n →
              (basis : LocalDef040 n keyDimension) →
                (basisNext : LocalDef040 n (instHAdd.hAdd keyDimension 1)) →
                  (hessenberg : LocalDef040 (instHAdd.hAdd keyDimension 1) keyDimension) →
                    (arnoldiProduct arnoldiProductError : LocalDef040 n keyDimension) →
                      Eq arnoldiProduct (instHAdd.hAdd (LocalDef048 A basis) arnoldiProductError) →
                        (∀ (row : Fin n) (col : Fin keyDimension), Eq (basis row col) (basisNext row col.castSucc)) →
                          (mgsWork : Fin keyDimension → Nat → LocalDef028 n) →
                            (mgsProjectionError : Fin keyDimension → Fin keyDimension → Real) →
                              (mgsUpdateError : Fin keyDimension → Fin keyDimension → LocalDef028 n) →
                                (mgsNormalizationError : Fin keyDimension → LocalDef028 n) →
                                  (∀ (j : Fin keyDimension) (row : Fin n),
                                      Eq (mgsWork j 0 row) (arnoldiProduct row j)) →
                                    (∀ (j q : Fin keyDimension),
                                        instLENat.le q.val j.val →
                                          Eq (hessenberg q.castSucc j)
                                            (instHAdd.hAdd
                                              (Finset.univ.sum fun row =>
                                                instHMul.hMul (basisNext row q.castSucc) (mgsWork j q.val row))
                                              (mgsProjectionError j q))) →
                                      (∀ (j q : Fin keyDimension),
                                          instLENat.le q.val j.val →
                                            Real.instLE.le (abs (mgsProjectionError j q))
                                              (instHMul.hMul (LocalDef035 uLow n)
                                                (Finset.univ.sum fun row =>
                                                  abs
                                                    (instHMul.hMul (basisNext row q.castSucc)
                                                      (mgsWork j q.val row))))) →
                                        (∀ (j q : Fin keyDimension),
                                            instLENat.le q.val j.val →
                                              Eq (mgsWork j (instHAdd.hAdd q.val 1))
                                                (instHAdd.hAdd
                                                  (instHSub.hSub (mgsWork j q.val) fun row =>
                                                    instHMul.hMul (hessenberg q.castSucc j) (basisNext row q.castSucc))
                                                  (mgsUpdateError j q))) →
                                          (∀ (j q : Fin keyDimension),
                                              instLENat.le q.val j.val →
                                                Real.instLE.le (LocalDef031 (mgsUpdateError j q))
                                                  (instHMul.hMul uLow
                                                    (instHAdd.hAdd (LocalDef031 (mgsWork j q.val))
                                                      (instHMul.hMul (abs (hessenberg q.castSucc j))
                                                        (LocalDef031 fun row =>
                                                          basisNext row q.castSucc))))) →
                                            (∀ (j : Fin keyDimension),
                                                Eq
                                                  (fun row =>
                                                    instHMul.hMul (hessenberg j.succ j) (basisNext row j.succ))
                                                  (instHAdd.hAdd (mgsWork j (instHAdd.hAdd j.val 1))
                                                    (mgsNormalizationError j))) →
                                              (∀ (j : Fin keyDimension),
                                                  Real.instLE.le (LocalDef031 (mgsNormalizationError j))
                                                    (instHMul.hMul uLow
                                                      (LocalDef031 (mgsWork j (instHAdd.hAdd j.val 1))))) →
                                                (epsilonC epsilonB epsilonLS epsilonX : Real) →
                                                  (residualLow residualCastError : LocalDef028 n) →
                                                    Eq residualLow (instHAdd.hAdd residualHat residualCastError) →
                                                      Real.instLE.le (LocalDef031 residualCastError)
                                                          (instHMul.hMul uLow (LocalDef031 residualHat)) →
                                                        Eq epsilonB uLow →
                                                          Real.instLE.le
                                                              (LocalDef046 arnoldiProductError)
                                                              (instHMul.hMul epsilonC
                                                                (LocalDef046
                                                                  (LocalDef048 A basis))) →
                                                            (leastSquaresRhsError : LocalDef028 n) →
                                                              (leastSquaresMatrixError :
                                                                  LocalDef040 n keyDimension) →
                                                                (leastSquaresY : LocalDef028 keyDimension) →
                                                                  LocalDef043
                                                                      (instHAdd.hAdd arnoldiProduct
                                                                        leastSquaresMatrixError)
                                                                      (instHAdd.hAdd residualLow leastSquaresRhsError)
                                                                      leastSquaresY →
                                                                    (∀ (j : Fin (instHAdd.hAdd keyDimension 1)),
                                                                        Real.instLE.le
                                                                          (LocalDef031
                                                                            (LocalDef042
                                                                              leastSquaresRhsError
                                                                              leastSquaresMatrixError j))
                                                                          (instHMul.hMul epsilonLS
                                                                            (LocalDef031
                                                                              (LocalDef042
                                                                                residualLow arnoldiProduct j)))) →
                                                                      (correctionFormationError :
                                                                          LocalDef028 n) →
                                                                        Eq correctionHat
                                                                            (instHAdd.hAdd
                                                                              (LocalDef047 basis
                                                                                leastSquaresY)
                                                                              correctionFormationError) →
                                                                          Real.instLE.le
                                                                              (LocalDef031
                                                                                correctionFormationError)
                                                                              (instHMul.hMul
                                                                                (instHMul.hMul epsilonX
                                                                                  (LocalDef046 basis))
                                                                                (LocalDef031
                                                                                  leastSquaresY)) →
                                                                            And (Real.instLE.le 0 epsilonC)
                                                                                (And (Real.instLE.le 0 epsilonB)
                                                                                  (And (Real.instLE.le 0 epsilonLS)
                                                                                    (Real.instLE.le 0 epsilonX))) →
                                                                              (productWeight leastSquaresWeight
                                                                                  correctionWeight : Real) →
                                                                                And (Real.instLE.le 0 productWeight)
                                                                                    (And
                                                                                      (Real.instLE.le 0
                                                                                        leastSquaresWeight)
                                                                                      (Real.instLE.le 0
                                                                                        correctionWeight)) →
                                                                                  Real.instLE.le epsilonC
                                                                                      (instHMul.hMul productWeight
                                                                                        uLow) →
                                                                                    Real.instLE.le epsilonLS
                                                                                        (instHMul.hMul
                                                                                          leastSquaresWeight uLow) →
                                                                                      Real.instLE.le epsilonX
                                                                                          (instHMul.hMul
                                                                                            correctionWeight uLow) →
                                                                                        (basisLowerGain imageLowerGain :
                                                                                            Real) →
                                                                                          Real.instLT.lt 0
                                                                                              basisLowerGain →
                                                                                            LocalDef044
                                                                                                basis basisLowerGain →
                                                                                              LocalDef044
                                                                                                  (LocalDef048
                                                                                                    A basis)
                                                                                                  imageLowerGain →
                                                                                                Real.instLT.lt
                                                                                                    (instHMul.hMul
                                                                                                      epsilonX
                                                                                                      (LocalDef046
                                                                                                        basis))
                                                                                                    basisLowerGain →
                                                                                                  (instLTNat.lt
                                                                                                        keyDimension n →
                                                                                                      ⋯) →
                                                                                                    ⋯ → ⋯
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `8fe2febf6102807a7c64b7a5b0420c7ec5a6e1a58b6ea582db35027cd51c43d0`

Type:

```lean
{n : Nat} →
  {A Ainv : LocalDef026 n} →
    {b xExact xCurrent xNext : LocalDef028 n} →
      {uHigh modularAccuracy dimensionFactor : Real} →
        (backwardFactor forwardFactor backwardHighCoefficient forwardHighCoefficient backwardRemainder
            forwardRemainder : Real) →
          Real.instLE.le 0 backwardFactor →
            Real.instLE.le 0 forwardFactor →
              Real.instLE.le 0 backwardHighCoefficient →
                Real.instLE.le 0 forwardHighCoefficient →
                  Real.instLE.le backwardFactor
                      (instHMul.hMul modularAccuracy (LocalDef029 A Ainv)) →
                    Real.instLE.le forwardFactor
                        (instHMul.hMul modularAccuracy (LocalDef029 A Ainv)) →
                      Real.instLE.le backwardHighCoefficient dimensionFactor →
                        Real.instLE.le forwardHighCoefficient
                            (instHMul.hMul dimensionFactor (LocalDef029 A Ainv)) →
                          Real.instLE.le (LocalDef017 A b xNext)
                              (instHAdd.hAdd
                                (instHAdd.hAdd
                                  (instHMul.hMul backwardFactor (LocalDef017 A b xCurrent))
                                  (instHMul.hMul backwardHighCoefficient uHigh))
                                (abs backwardRemainder)) →
                            Real.instLE.le (LocalDef022 xExact xNext)
                                (instHAdd.hAdd
                                  (instHAdd.hAdd
                                    (instHMul.hMul forwardFactor (LocalDef022 xExact xCurrent))
                                    (instHMul.hMul forwardHighCoefficient uHigh))
                                  (abs forwardRemainder)) →
                              LocalDef027 A Ainv b xExact xCurrent xNext uHigh modularAccuracy
                                dimensionFactor
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

Type:

```lean
Real → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`

Type:

```lean
{n : Nat} → LocalDef026 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.frobeniusNormedRing.norm A
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `85b5f4df299401a78ff2042ddbaff615a4f2e4dd7ac6d5eeddc8091ccb86d714`

Type:

```lean
{n : Nat} → LocalDef026 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Function.Bijective (LocalDef038 A)
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `633fcb3583fab70e7665e594e28a11707a692d4c14a396ea9eeda2a3724f56b9`

Type:

```lean
{n : Nat} → LocalDef026 n → LocalDef028 n → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b6efd2406b4d95a62ec33a870000fff88d929437b9b4152b36fbbe02063a3602`

Type:

```lean
{n : Nat} → LocalDef026 n → LocalDef028 n → LocalDef028 n → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b x => instHSub.hSub b (LocalDef038 A x)
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ed6ed4c3dc41190752faa97194bb8058e9dd7deadfbd18631c282a8f04103d81`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b8a20ccd1a0141e32676a45d1777c354b7c37d97677afb2234a664e7158d3cea`

Type:

```lean
{n k : Nat} →
  LocalDef028 n → Real → LocalDef040 n k → LocalDef040 n (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b phi C i i_1 => Fin.cases (instHMul.hMul (b i) phi) (fun j => C i j) i_1
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `edff7146376ef770366aba2e1853be47a9dd93c72ecd327c90997fcd05811128`

Type:

```lean
{n k : Nat} →
  LocalDef028 n → LocalDef040 n k → Fin (instHAdd.hAdd k 1) → LocalDef028 n
```

Definition body (one-level semantic boundary):

```lean
fun {n k} rhs C j => Fin.cases rhs (fun q row => C row q) j
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `bdfc265c3df9de57c6f0acfa56fa518d59187a9636cb68597f1faf194c63a797`

Type:

```lean
{m k : Nat} → LocalDef040 m k → LocalDef028 m → LocalDef028 k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : LocalDef028 k),
    Real.instLE.le (LocalDef031 (instHSub.hSub b (LocalDef047 A y)))
      (LocalDef031 (instHSub.hSub b (LocalDef047 A z)))
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `aea1bd8a88cb85c24aad7b9fbf82abc6098fc02caa123478bbd558b3d3759768`

Type:

```lean
{m k : Nat} → LocalDef040 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigma =>
  ∀ (x : LocalDef028 k),
    Real.instLE.le (instHMul.hMul sigma (LocalDef031 x))
      (LocalDef031 (LocalDef047 A x))
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `552e2d22c81360084216ba06ab4ea330e4c6339472649bada4698b2510af7ab9`

Type:

```lean
{m k : Nat} → LocalDef040 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A delta =>
  Exists fun x =>
    And (Eq (LocalDef031 x) 1)
      (Real.instLE.le (LocalDef031 (LocalDef047 A x)) delta)
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `a2ed232b7b5960b8a6f9c5907344e0b80314d5f88f6285f45b4409ed2a6d7203`

Type:

```lean
{m k : Nat} → LocalDef040 m k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `6f698af222e83d101b281cbccf24e989a885c3a996fa1b73f33092817b45db0c`

Type:

```lean
{m k : Nat} → LocalDef040 m k → LocalDef028 k → LocalDef028 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `0053caf146fae0af9f54e65099d1a3e27476c2f20502180d10ba739f1bc05026`

Type:

```lean
{n k : Nat} → LocalDef026 n → LocalDef040 n k → LocalDef040 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D049: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
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

### D053: `HMul.hMul`

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

### D054: `LE.le`

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

### D055: `LT.lt`

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

### D056: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D057: `OfNat.ofNat`

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

### D058: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D059: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D060: `Real.instAdd`

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

### D061: `Real.instAddGroup`

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

### D062: `Real.instLE`

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

### D063: `Real.instLT`

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

### D064: `Real.instMul`

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

### D065: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D066: `Real.instZero`

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

### D067: `Real.lattice`

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

### D068: `Zero.toOfNat0`

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

### D069: `abs`

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

### D070: `instAddNat`

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

### D072: `instHMul`

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

### D073: `instOfNatNat`

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

### D074: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D075: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D076: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D077: `HPow.hPow`

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

### D078: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D079: `Monoid.toNatPow`

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

### D080: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`

Type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub (G i)] → Sub ((i : ι) → G i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {G} [(i : ι) → Sub (G i)] => { sub := fun f g i => instHSub.hSub (f i) (g i) }
```

### D081: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D083: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D084: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
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

### D086: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D087: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D088: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D089: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D090: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D091: `Ne`

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

### D092: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D093: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```

### D094: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D095: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
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

### D097: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D098: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D099: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D100: `Function.Bijective`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2da1e723243113bf4396d64f6b64f6ee8db3b9e981ad6ec7448e7745e511e5e2`

Type:

```lean
{α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => And (Function.Injective f) (Function.Surjective f)
```

### D101: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D102: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`

Type:

```lean
{m : Type u_3} → {α : Type u_5} → [Fintype m] → [RCLike α] → [DecidableEq m] → NormedRing (Matrix m m α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {α} [Fintype m] [RCLike α] [DecidableEq m] =>
  let __src := Matrix.frobeniusSeminormedAddCommGroup;
  let __src_1 := Matrix.instRing;
  { toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := ⋯, toMul := __src_1.toMul, left_distrib := ⋯,
    right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, toOne := __src_1.toOne, one_mul := ⋯,
    mul_one := ⋯, toNatCast := __src_1.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯, npow := __src_1.npow,
    npow_zero := ⋯, npow_succ := ⋯, toNeg := __src.toNeg, toSub := __src.toSub, sub_eq_add_neg := ⋯,
    zsmul := __src.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    toIntCast := __src_1.toIntCast, intCast_ofNat := ⋯, intCast_negSucc := ⋯,
    toPseudoMetricSpace := __src.toPseudoMetricSpace, eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D103: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `6fa198061d1b8595a7b8b0ed74bd9e48f2c7a18aa01bf39d9c30be49c1d4741c`

Type:

```lean
{α : Type u} → [self : Max α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Max α] => self.1
```

### D104: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D105: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D106: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`

Type:

```lean
{α : Type u_5} → [self : NormedRing α] → Norm α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NormedRing α] => self.1
```

### D107: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `313f6558836157f8e8b4ea7be18fb6953bf9aefc4dcb68940ef5c4889e18a763`

Type:

```lean
Max Real
```

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```

### D108: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D109: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D110: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D111: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D112: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `38edd2256cd8f4f33f2c43ce7c36a1e1c7aded652580ec57a0adaf0ec346b64d`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive 0 → ((i : Fin n) → motive i.succ) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} zero succ i => Fin.induction zero (fun i x => succ i) i
```

### D113: `Matrix.frobeniusNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3f944d9003e72c887b38048a3f469c42c010d0e141780ed19b0137eb25d742ba`

Type:

```lean
{m : Type u_3} →
  {n : Type u_4} →
    {α : Type u_5} → [Fintype m] → [Fintype n] → [NormedAddCommGroup α] → NormedAddCommGroup (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Fintype m] [Fintype n] [NormedAddCommGroup α] => PiLp.normedAddCommGroupToPi 2 fun a => n → α
```

### D114: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D115: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```
