# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m n : Nat} (run : LocalDef001 m n),
  And
    (∀ (k j : Fin n),
      instLENat.le k.val j.val →
        Real.instLE.le
          (abs
            (instHSub.hSub (run.A (LocalDef012 ⋯ k) j)
              (LocalDef009 run.LHat run.UHat (LocalDef012 ⋯ k) j k)))
          (instHMul.hMul (instHMul.hMul k.val.cast run.format.unitRoundoff)
            (LocalDef008 run.LHat run.UHat (LocalDef012 ⋯ k) j k)))
    (And
      (∀ (i : Fin m) (k : Fin n),
        instLTNat.lt k.val i.val →
          Real.instLE.le
            (abs (instHSub.hSub (run.A i k) (LocalDef009 run.LHat run.UHat i k k)))
            (instHMul.hMul (instHMul.hMul (instHAdd.hAdd k.val 1).cast run.format.unitRoundoff)
              (LocalDef008 run.LHat run.UHat i k k)))
      (Exists fun ΔA =>
        And (Eq (LocalDef011 run.LHat run.UHat) (instHAdd.hAdd run.A ΔA))
          (And
            (∀ (i : Fin m) (j : Fin n),
              Real.instLE.le (abs (ΔA i j))
                (instHMul.hMul (instHMul.hMul n.cast run.format.unitRoundoff)
                  (LocalDef010 run.LHat run.UHat i j)))
            (Eq m n →
              And
                (∀ (i : Fin m) (j : Fin n),
                  Real.instLE.le (abs (ΔA i j))
                    (instHMul.hMul (instHMul.hMul i.val.cast run.format.unitRoundoff)
                      (LocalDef010 run.LHat run.UHat i j)))
                (∀ (i : Fin m) (j : Fin n),
                  Real.instLE.le (abs (ΔA i j))
                    (instHMul.hMul (instHMul.hMul (instHSub.hSub n 1).cast run.format.unitRoundoff)
                      (LocalDef010 run.LHat run.UHat i j)))))))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (run : LocalDef001 m n),
  And
    (∀ (k j : Fin n),
      @LE.le.{0} Nat instLENat (@Fin.val n k) (@Fin.val n j) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@LocalDef002 m n run
                (@LocalDef012 m n (@LocalDef006 m n run) k) j)
              (@LocalDef009 m n (@LocalDef003 m n run)
                (@LocalDef004 m n run)
                (@LocalDef012 m n (@LocalDef006 m n run) k) j k)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast (@Fin.val n k))
              (LocalDef007 (@LocalDef005 m n run)))
            (@LocalDef008 m n (@LocalDef003 m n run)
              (@LocalDef004 m n run)
              (@LocalDef012 m n (@LocalDef006 m n run) k) j k)))
    (And
      (∀ (i : Fin m) (k : Fin n),
        @LT.lt.{0} Nat instLTNat (@Fin.val n k) (@Fin.val m i) →
          @LE.le.{0} Real Real.instLE
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@LocalDef002 m n run i k)
                (@LocalDef009 m n (@LocalDef003 m n run)
                  (@LocalDef004 m n run) i k k)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (LocalDef007 (@LocalDef005 m n run)))
              (@LocalDef008 m n (@LocalDef003 m n run)
                (@LocalDef004 m n run) i k k)))
      (@Exists.{1} (Fin m → Fin n → Real) fun (ΔA : Fin m → Fin n → Real) =>
        And
          (@Eq.{1} (Fin m → Fin n → Real)
            (@LocalDef011 m n (@LocalDef003 m n run)
              (@LocalDef004 m n run))
            (@HAdd.hAdd.{0, 0, 0} (Fin m → Fin n → Real) (Fin m → Fin n → Real) (Fin m → Fin n → Real)
              (@instHAdd.{0} (Fin m → Fin n → Real)
                (@Pi.instAdd.{0, 0} (Fin m) (fun (a : Fin m) => Fin n → Real) fun (i : Fin m) =>
                  @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
              (@LocalDef002 m n run) ΔA))
          (And
            (∀ (i : Fin m) (j : Fin n),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast n)
                    (LocalDef007
                      (@LocalDef005 m n run)))
                  (@LocalDef010 m n (@LocalDef003 m n run)
                    (@LocalDef004 m n run) i j)))
            (@Eq.{1} Nat m n →
              And
                (∀ (i : Fin m) (j : Fin n),
                  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast (@Fin.val m i))
                        (LocalDef007
                          (@LocalDef005 m n run)))
                      (@LocalDef010 m n (@LocalDef003 m n run)
                        (@LocalDef004 m n run) i j)))
                (∀ (i : Fin m) (j : Fin n),
                  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (LocalDef007
                          (@LocalDef005 m n run)))
                      (@LocalDef010 m n (@LocalDef003 m n run)
                        (@LocalDef004 m n run) i j)))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `c53aaa88f9293f0661a3c4f48f61b2716ee5a371072f41cb67922aad8ff0f3f8`

Type:

```lean
Nat → Nat → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2a9b2a6c7f506f6e44949230f40ef27d7015e0972308661fb8dce2fbc1ca0b89`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.4
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `aedc79bc377f1bc7fff574d7290bfd015c881dc0203cd346f2cee0948db9a24e`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.5
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `de52eabfe4fbeb7b2de9eb3e5b463af932d80512cd20681c88286c36b5128adf`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.6
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b8aa7e5d9372c6b62b8de3d24b076426f69088c69d2f6c1c75a41105124a5b69`

Type:

```lean
{m n : Nat} → LocalDef001 m n → LocalDef014
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.1
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `45e8dda54b96a0c31c913132c201d1aab0f5627ea00c41ed1f765eefe8a8fad2`

Type:

```lean
∀ {m n : Nat} (self : LocalDef001 m n), instLENat.le n m
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3630b109f8786a050a03b7576d18b02aca25f370b7c3aeacef8aeb8f4eded07d`

Type:

```lean
LocalDef014 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.12
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `435771eb7f49ed974ab3b6e31ad356019f1c252a1138d260de35e9e20b5c16c7`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j k =>
  instHAdd.hAdd (LocalDef015 L U i j k) (instHMul.hMul (abs (L i k)) (abs (U k j)))
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2bdb52cf278f3714dbd1045be326cdc5eba3bf5642dab2c2b430e71657de0db6`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j k => instHAdd.hAdd (LocalDef016 L U i j k) (instHMul.hMul (L i k) (U k j))
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4cf9d1f7d032936b8e0cef1ed546918c9df5a06178a511c99472659c4af3d5a7`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j => Finset.univ.sum fun k => instHMul.hMul (abs (L i k)) (abs (U k j))
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bb8e607a47b435a9f208d4bae68d6938c638256ab589d9b68dd55f3bec7bade5`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j => Finset.univ.sum fun k => instHMul.hMul (L i k) (U k j)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `352c178629e34a95985cf5e2fbd5b01bca9da7768f1a022b7b89a091dfb9364a`

Type:

```lean
{m n : Nat} → instLENat.le n m → Fin n → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} hmn k => Fin.castLE hmn k
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `946f3fd716dd14ea7060471abedd08ff555a70fc31892b8e002522f54393bee6`

Type:

```lean
{m n : Nat} →
  (format : LocalDef014) →
    (rows_ge_columns : instLENat.le n m) →
      instLTNat.lt 0 n →
        (A LHat : Fin m → Fin n → Real) →
          (UHat : Fin n → Fin n → Real) →
            (∀ (i : Fin m) (j : Fin n), format.representable (A i j)) →
              (∀ (i : Fin m) (j : Fin n), format.representable (LHat i j)) →
                (∀ (i j : Fin n), format.representable (UHat i j)) →
                  (∀ (k : Fin n), Eq (LHat (LocalDef012 rows_ge_columns k) k) 1) →
                    (∀ (i : Fin m) (j : Fin n), instLTNat.lt i.val j.val → Eq (LHat i j) 0) →
                      (∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (UHat i j) 0) →
                        ((k j : Fin n) →
                            instLENat.le k.val j.val →
                              LocalDef018 format rows_ge_columns A LHat UHat k j) →
                          ((i : Fin m) →
                              (k : Fin n) →
                                instLTNat.lt k.val i.val → LocalDef017 format A LHat UHat i k) →
                            LocalDef001 m n
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `0ddacc640e57cd98fa542c796ebf4288f8e3c1b48d1de954147bdb407876ca70`

Type:

```lean
Type
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f1a22159b98b584727c1aa9ce88f3191ea9c06d8d222d4d0e63753f77d7d9f53`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j k =>
  Finset.univ.sum fun s =>
    instHMul.hMul (abs (L i (LocalDef021 k s))) (abs (U (LocalDef021 k s) j))
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ce00013604155b7918089a848b017e5e8f16458ef3de18ee1787cc9cf2c5d577`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} L U i j k =>
  Finset.univ.sum fun s => instHMul.hMul (L i (LocalDef021 k s)) (U (LocalDef021 k s) j)
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `06d8dab22535281142a3afc06d755cfc7cc0c2affbdee27e806c302247265424`

Type:

```lean
{m n : Nat} →
  LocalDef014 →
    (Fin m → Fin n → Real) → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin m → Fin n → Type
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `16758ccb523701d1781581b1e2744f2b9bfb2eea93db8313c8e4d5dcdf4ba1fe`

Type:

```lean
{m n : Nat} →
  LocalDef014 →
    instLENat.le n m → (Fin m → Fin n → Real) → (Fin m → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Type
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `12567c74ebb12a1d6821773c68b68a5d2df28fa0be58bacf4154a30b87c2b81e`

Type:

```lean
(radix precision : Nat) →
  (minExponent maxExponent : Int) →
    instLENat.le 2 radix →
      instLTNat.lt 0 precision →
        Int.instLTInt.lt minExponent maxExponent →
          (representable : Real → Prop) →
            (setOf fun x => representable x).Finite →
              (safeRange : Real → Prop) →
                (round : Real → Real) →
                  (unitRoundoff : Real) →
                    Real.instLE.le 0 unitRoundoff →
                      Eq
                          (instHMul.hMul unitRoundoff
                            (instHMul.hMul 2 (instHPow.hPow radix.cast (instHSub.hSub precision 1))))
                          1 →
                        representable 0 →
                          representable 1 →
                            (∀ (x : Real), safeRange x → representable (round x)) →
                              (∀ (x : Real),
                                  safeRange x →
                                    ∀ (z : Real),
                                      representable z →
                                        Real.instLE.le (abs (instHSub.hSub x (round x))) (abs (instHSub.hSub x z))) →
                                (∀ (x : Real), representable x → Eq (round x) x) →
                                  LocalDef014
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `939843e6234b6b60e9493201a37a6f0770ba8ba2ffd11eb2e38ddcaa236b4ed2`

Type:

```lean
LocalDef014 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `702d4429ada9455cd5959efae9f932331aeac5d37604b4119d20204d6d9270c3`

Type:

```lean
{n : Nat} → (k : Fin n) → Fin k.val → Fin n
```

Definition body (one-level semantic boundary):

```lean
fun {n} k s => ⟨s.val, ⋯⟩
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `25de31b3600c5bfa7f57dafc865308bde28ccb0c7e7cd50e7b7ff58fb8be70b9`

Type:

```lean
{m n : Nat} →
  {fmt : LocalDef014} →
    {A L : Fin m → Fin n → Real} →
      {U : Fin n → Fin n → Real} →
        {i : Fin m} →
          {k : Fin n} →
            (execution : LocalDef025 k.val) →
              Eq execution.format fmt →
                (∀ (s : Fin k.val), Eq (execution.a s) (L i (LocalDef021 k s))) →
                  (∀ (s : Fin k.val), Eq (execution.b s) (U (LocalDef021 k s) k)) →
                    Eq execution.bK (U k k) →
                      Eq execution.c (A i k) →
                        Eq execution.yHat (L i k) → LocalDef017 fmt A L U i k
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `d97830b914a8a4d02be24f3e78ea955b102aa8b563bdbe807866517b58cdd037`

Type:

```lean
{m n : Nat} →
  {fmt : LocalDef014} →
    {hmn : instLENat.le n m} →
      {A L : Fin m → Fin n → Real} →
        {U : Fin n → Fin n → Real} →
          {k j : Fin n} →
            (execution : LocalDef025 k.val) →
              Eq execution.format fmt →
                (∀ (s : Fin k.val),
                    Eq (execution.a s) (L (LocalDef012 hmn k) (LocalDef021 k s))) →
                  (∀ (s : Fin k.val), Eq (execution.b s) (U (LocalDef021 k s) j)) →
                    Eq execution.bK 1 →
                      Eq execution.c (A (LocalDef012 hmn k) j) →
                        Eq execution.yHat (U k j) → LocalDef018 fmt hmn A L U k j
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `5e79f8abda33d6147717bad7b59dcf91acde006099614092f0e02069833b9bac`

Type:

```lean
∀ {n : Nat} (k : Fin n) (s : Fin k.val), Nat.instPreorder.lt s.val n
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `54f7fb21338d460d95ba24f4f68ec1e88485ff544bfc11cf2639399316ad8dad`

Type:

```lean
Nat → Type
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c74f6cc7255c2553bd8a9833b413e7541ce56f438556ea843f8fc99f4156b157`

Type:

```lean
{m : Nat} → LocalDef025 m → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.2
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bad0fe7139c08bbb1859577b06ffb3ed0e035d3317d600ae0b0da9051afed006`

Type:

```lean
{m : Nat} → LocalDef025 m → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.3
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `91a236cf4b3aba3f088617d30f2b25bdb2774e5b236857b4989ee1b529b3db9e`

Type:

```lean
{m : Nat} → LocalDef025 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.4
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `efe594e7c21046e128f080bccd7ed684eaf4183c2a331fb724ec19789e7e476a`

Type:

```lean
{m : Nat} → LocalDef025 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.5
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `aadc2a3d9c85a3ab5b73d3632b6c83d3467e27ed03f5d86fced67a9d0489ddc8`

Type:

```lean
{m : Nat} → LocalDef025 m → LocalDef014
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.1
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `24b9b4796c449d802022b0dc73b1270acab8eb937804ebf1c6169ecba412af34`

Type:

```lean
{m : Nat} → LocalDef025 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.17
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `c846b40599e7d4a3d66b55c917495caee8618b1e9b0f894f80f5936e203a1201`

Type:

```lean
{m : Nat} →
  (format : LocalDef014) →
    (a b : Fin m → Real) →
      (bK c : Real) →
        (∀ (i : Fin m), format.representable (a i)) →
          (∀ (i : Fin m), format.representable (b i)) →
            format.representable bK →
              format.representable c →
                Ne bK 0 →
                  (∀ (i : Fin m), format.safeRange (instHMul.hMul (a i) (b i))) →
                    (tree : LocalDef035 (instHAdd.hAdd m 1)) →
                      (order : Equiv.Perm (Fin (instHAdd.hAdd m 1))) →
                        (LocalDef038 format tree fun i =>
                            LocalDef036 format a b c (EquivLike.toFunLike.coe order i)) →
                          (numerator : Real) →
                            Eq numerator
                                (LocalDef037 format tree fun i =>
                                  LocalDef036 format a b c (EquivLike.toFunLike.coe order i)) →
                              (yHat : Real) →
                                (Eq bK 1 → Eq yHat numerator) →
                                  (Ne bK 1 → format.safeRange (instHDiv.hDiv numerator bK)) →
                                    (Ne bK 1 → Eq yHat (format.round (instHDiv.hDiv numerator bK))) →
                                      Real.instLE.le
                                          (abs
                                            (instHSub.hSub
                                              (instHSub.hSub c (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                              (instHMul.hMul bK yHat)))
                                          (instHMul.hMul (instHMul.hMul (instHAdd.hAdd m 1).cast format.unitRoundoff)
                                            (instHAdd.hAdd (abs (instHMul.hMul bK yHat))
                                              (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i))))) →
                                        (Eq bK 1 →
                                            Real.instLE.le
                                              (abs
                                                (instHSub.hSub
                                                  (instHSub.hSub c (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                                  yHat))
                                              (instHMul.hMul (instHMul.hMul m.cast format.unitRoundoff)
                                                (instHAdd.hAdd (abs yHat)
                                                  (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i)))))) →
                                          LocalDef025 m
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `0bebeeb156b3b1d6c4fb9f9ec0c12486071422fb52bff0d1206d805e87292cbc`

Type:

```lean
LocalDef014 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.11
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `6b66b03c590cc2c1654bd9631fb5645291a21681e905b136a1f85d1fd928c436`

Type:

```lean
LocalDef014 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.10
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `7`
- Semantic SHA-256: `443a0aa6f83664582344d89f72b609bc7af3d2025eacff100aebdbcacb0938fc`

Type:

```lean
Nat → Type
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `53288ef5dcd6dce907f195ffd0fdcbfaebf7b436ac8098403000f49182a3ede0`

Type:

```lean
{m : Nat} →
  LocalDef014 → (Fin m → Real) → (Fin m → Real) → Real → Fin (instHAdd.hAdd m 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b c i => Fin.cases c (fun i => Real.instNeg.neg (LocalDef043 fmt a b i)) i
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `5276000dc42400351a4955f3911dcae4de8b74de2fb84b50d07230a884af2020`

Type:

```lean
LocalDef014 → {n : Nat} → LocalDef035 n → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  LocalDef040 (motive := fun {n} tree => (Fin n → Real) → Real) tree
    (fun {n} tree f v =>
      LocalDef045
        (fun n tree v => LocalDef039 (motive := fun {n} tree => (Fin n → Real) → Real) tree → Real) n
        tree v (fun v x => v ⟨0, LocalDef044⟩)
        (fun m n left right v x =>
          fmt.round (instHAdd.hAdd (x.1.1 fun i => v (Fin.castAdd n i)) (x.2.1 fun i => v (Fin.natAdd m i))))
        f)
    v
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `28c67f1f1f332ec7ed8f24f988fff25480a126aa5735959a513d27837bc19587`

Type:

```lean
LocalDef014 → {n : Nat} → LocalDef035 n → (Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  LocalDef040 (motive := fun {n} tree => (Fin n → Real) → Prop) tree
    (fun {n} tree f v =>
      LocalDef045
        (fun n tree v => LocalDef039 (motive := fun {n} tree => (Fin n → Real) → Prop) tree → Prop) n
        tree v (fun v x => fmt.representable (v ⟨0, LocalDef044⟩))
        (fun m n left right v x =>
          And (x.1.1 fun i => v (Fin.castAdd n i))
            (And (x.2.1 fun i => v (Fin.natAdd m i))
              (fmt.safeRange
                (instHAdd.hAdd (LocalDef037 fmt left fun i => v (Fin.castAdd n i))
                  (LocalDef037 fmt right fun i => v (Fin.natAdd m i))))))
        f)
    v
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `04678a12719fff926622b3e9fbf38f572093e387c69fa03eb32cb222cd68fe1a`

Type:

```lean
{motive : (a : Nat) → LocalDef035 a → Sort u} → {a : Nat} → LocalDef035 a → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t =>
  LocalDef048 PUnit
    (fun {m n} a a_1 a_ih a_ih_1 => PProd (PProd (motive m a) a_ih) (PProd (motive n a_1) a_ih_1)) t
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `cb3c6322835a978db412df67d07972af7f5ebc95b2fe7fffd3f78ab7c1c10544`

Type:

```lean
{motive : (a : Nat) → LocalDef035 a → Sort u} →
  {a : Nat} →
    (t : LocalDef035 a) →
      ((a : Nat) → (t : LocalDef035 a) → LocalDef039 t → motive a t) → motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 => (LocalDef046 t F_1).1
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `d400482110f6735443dd560bbbc8525a6db52e539e45f92488e808fd742cb999`

Type:

```lean
LocalDef035 1
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `47eb0dcdab89e52469860668ea9ff917c63ab85960c92a40c58d7885ba4b7f44`

Type:

```lean
{m n : Nat} → LocalDef035 m → LocalDef035 n → LocalDef035 (instHAdd.hAdd m n)
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `9cc6e82bd9680cd814e1f49e1260fe201a0535af0efdf7c523fa734c4b1cf26e`

Type:

```lean
{m : Nat} → LocalDef014 → (Fin m → Real) → (Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b i => fmt.round (instHMul.hMul (a i) (b i))
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `8`
- Semantic SHA-256: `3837ff05fe96904abf1d46536ea66370e1afc147c8f02d6219701e1854673c5f`

Type:

```lean
Nat.instPartialOrder.lt 0 1
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `628dea76c4d1a3a85ca7248eb8dbbe9298030d0d3d089ceb2f318990b1196f40`

Type:

```lean
(motive : (n : Nat) → LocalDef035 n → (Fin n → Real) → Sort u_1) →
  (n : Nat) →
    (tree : LocalDef035 n) →
      (v : Fin n → Real) →
        ((v : Fin 1 → Real) → motive 1 LocalDef041 v) →
          ((m n : Nat) →
              (left : LocalDef035 m) →
                (right : LocalDef035 n) →
                  (v : Fin (instHAdd.hAdd m n) → Real) → motive (instHAdd.hAdd m n) (left.node right) v) →
            motive n tree v
```

Definition body (one-level semantic boundary):

```lean
fun motive n tree v h_1 h_2 =>
  (fun tree_1 =>
      LocalDef047 (motive := fun a x => Eq n a → HEq tree x → motive n tree v) tree_1
        (fun h =>
          Eq.ndrec (motive := fun n =>
            (tree : LocalDef035 n) →
              (v : Fin n → Real) → HEq tree LocalDef041 → motive n tree v)
            (fun tree v h => Eq.ndrec (h_1 v) ⋯) ⋯ tree v)
        fun {m n_1} a a_1 h =>
        Eq.ndrec (motive := fun n =>
          (tree : LocalDef035 n) → (v : Fin n → Real) → HEq tree (a.node a_1) → motive n tree v)
          (fun tree v h => Eq.ndrec (h_2 m n_1 a a_1 v) ⋯) ⋯ tree v)
    tree ⋯ ⋯
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `a1f5b5d0ff724fb25f8c6eb41f3392a734a4bd8a54fa24702cb5c1c49c98e9b7`

Type:

```lean
{motive : (a : Nat) → LocalDef035 a → Sort u} →
  {a : Nat} →
    (t : LocalDef035 a) →
      ((a : Nat) → (t : LocalDef035 a) → LocalDef039 t → motive a t) →
        PProd (motive a t) (LocalDef039 t)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 =>
  LocalDef048 ⟨F_1 1 LocalDef041 PUnit.unit, PUnit.unit⟩
    (fun {m n} a a_1 a_ih a_ih_1 => ⟨F_1 (instHAdd.hAdd m n) (a.node a_1) ⟨a_ih, a_ih_1⟩, a_ih, a_ih_1⟩) t
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `6a2f271359e9f74faaece28f70b9cc38b461b3d2ac2b2cacdbb565586e6814f8`

Type:

```lean
{motive : (a : Nat) → LocalDef035 a → Sort u} →
  {a : Nat} →
    (t : LocalDef035 a) →
      motive 1 LocalDef041 →
        ({m n : Nat} →
            (a : LocalDef035 m) →
              (a_1 : LocalDef035 n) → motive (instHAdd.hAdd m n) (a.node a_1)) →
          motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t leaf node => LocalDef048 leaf (fun {m n} a a_1 a_ih a_ih_1 => node a a_1) t
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `9`
- Semantic SHA-256: `9b30df98c9e7570f0a4522ebeddf3fffb65f3cfaa16bd8c18752e6df00414a03`

Type:

```lean
{motive : (a : Nat) → LocalDef035 a → Sort u} →
  motive 1 LocalDef041 →
    ({m n : Nat} →
        (a : LocalDef035 m) →
          (a_1 : LocalDef035 n) → motive m a → motive n a_1 → motive (instHAdd.hAdd m n) (a.node a_1)) →
      {a : Nat} → (t : LocalDef035 a) → motive a t
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

### D052: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D053: `Fin.val`

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

### D054: `HAdd.hAdd`

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

### D055: `HMul.hMul`

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

### D056: `HSub.hSub`

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

### D057: `LE.le`

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

### D058: `LT.lt`

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

### D059: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D060: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D061: `OfNat.ofNat`

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

### D062: `Pi.instAdd`

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

### D063: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D064: `Real.instAdd`

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

### D065: `Real.instAddGroup`

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

### D066: `Real.instLE`

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

### D067: `Real.instMul`

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

### D068: `Real.instNatCast`

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

### D069: `Real.instSub`

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

### D070: `Real.lattice`

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

### D071: `abs`

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

### D072: `instAddNat`

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

### D073: `instHAdd`

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

### D074: `instHMul`

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

### D075: `instHSub`

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

### D076: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D077: `instLTNat`

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

### D078: `instOfNatNat`

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

### D079: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

Type:

```lean
Sub Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
```

### D080: `Fin.castLE`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `741eedcc1330cedb8ff0a69095d6df1438c40a8c734f1526dc385e45bb9ae135`

Type:

```lean
{n m : Nat} → instLENat.le n m → Fin n → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} h i => ⟨i.val, ⋯⟩
```

### D081: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D082: `Finset.sum`

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

### D083: `Finset.univ`

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

### D084: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D085: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D086: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D087: `Real.instZero`

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

### D088: `Zero.toOfNat0`

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

### D089: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D090: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D091: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

### D092: `Int.instLTInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `c6ba6b2af0ba0b1e59e45f9e25272ad271a1e55993be47eb5029dc9e9dbfc5ab`

Type:

```lean
LT Int
```

Definition body (one-level semantic boundary):

```lean
{ lt := Int.lt }
```

### D093: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D094: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D095: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D096: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D097: `Set.Finite`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finite.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cd1248ce5442277e3732ae7b908af0837d4e3ee0bff49bbaa908aef80f57bfbc`

Type:

```lean
{α : Type u} → Set α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} s => Finite s.Elem
```

### D098: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D099: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D100: `setOf`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cee4433aebd78c308ec85f62ccd30489c00ec9cc23a98f4d2139c17f840f4988`

Type:

```lean
{α : Type u} → (α → Prop) → Set α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p => p
```

### D101: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D102: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `8fcf5a8f5a8899408a8cdc310bc44f6f7b84a21905a114103fbc65083f779a43`

Type:

```lean
{α : Type u_2} → [self : Preorder α] → LT α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Preorder α] => self.2
```

### D103: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D104: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D105: `Equiv.Perm`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c8be4339de7efaee2aff8b13efc12794f5acd112d4188f63d38d39f9e4bd687c`

Type:

```lean
Sort u_1 → Sort (max 1 u_1)
```

Definition body (one-level semantic boundary):

```lean
fun α => Equiv α α
```

### D106: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D107: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D108: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D109: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D110: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D111: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D112: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `8`
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

### D113: `Fin.castAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `bff7b13dfc77fda725a938338f6d0c6fbe5d5b328cd5c9a1c9de44224915838b`

Type:

```lean
{n : Nat} → (m : Nat) → Fin n → Fin (instHAdd.hAdd n m)
```

Definition body (one-level semantic boundary):

```lean
fun {n} m => Fin.castLE ⋯
```

### D114: `Fin.natAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `06007c678fab1dc171aa2b490b41eb467e5f51799a25bb0c10890e6946480989`

Type:

```lean
{m : Nat} → (n : Nat) → Fin m → Fin (instHAdd.hAdd n m)
```

Definition body (one-level semantic boundary):

```lean
fun {m} n i => ⟨instHAdd.hAdd n i.val, ⋯⟩
```

### D115: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D116: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D117: `Eq.ndrec`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `f86cb68b5cbbf1ddc06f9f211e3421eced11542c1e459b8ba4c1e06c0f8ca7d2`

Type:

```lean
{α : Sort u2} → {a : α} → {motive : α → Sort u1} → motive a → {b : α} → Eq a b → motive b
```

Definition body (one-level semantic boundary):

```lean
fun {α} {a} {motive} m {b} h => Eq.rec m h
```

### D118: `Eq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `9`
- Semantic SHA-256: `62d4020b7012db70e44624c7d64dd267524e7e75e4b869680e0c95d2231c85d1`

Type:

```lean
∀ {α : Sort u_1} (a : α), Eq a a
```

### D119: `Eq.symm`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `9`
- Semantic SHA-256: `7c9d5428fd9feab69045077277e3f895072f20edba5f2a9479559efbee9f7cf2`

Type:

```lean
∀ {α : Sort u} {a b : α}, Eq a b → Eq b a
```

### D120: `HEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `a71d8d31511fc844f0f70ae865b109282edf2e9593d6acbdee9925cd9e03d1db`

Type:

```lean
{α : Sort u} → α → {β : Sort u} → β → Prop
```

### D121: `HEq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `9`
- Semantic SHA-256: `15ec9e197e90776f1db6670d1ce41d43e6ba50700a0f4752439b345b47e5d1c9`

Type:

```lean
∀ {α : Sort u} (a : α), HEq a a
```

### D122: `Nat.instPartialOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `2759981f152e80eec9150e4e0e23de292150f9cea0c8c910125cf9e56acf2f67`

Type:

```lean
PartialOrder Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D123: `PProd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `f220f3fbfda558146d81aa3a9391a551a0b414f82b31ddca68583a9f3b829035`

Type:

```lean
Sort u → Sort v → Sort (max (max 1 u) v)
```

### D124: `PUnit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `766f980214e36af1ff35d2ec98c8393266d25d4a847f71e22766f564898fc02c`

Type:

```lean
Sort u
```

### D125: `PartialOrder.toPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `079686fa1ec6d596bcdb475c56a12b7f5a0594bf346c64220c2c992e0f0aae3b`

Type:

```lean
{α : Type u_2} → [self : PartialOrder α] → Preorder α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PartialOrder α] => self.1
```

### D126: `eq_of_heq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `9`
- Semantic SHA-256: `17dda0f4fb758715279a058b25c7babf034d9cf08d6d9ae8a500eaf0c83d4724`

Type:

```lean
∀ {α : Sort u} {a a' : α}, HEq a a' → Eq a a'
```

### D127: `PProd.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `10`
- Semantic SHA-256: `77a288dd932e98f780ede81f87af6b4ae802bc357db102e11bc037200b5d6eb0`

Type:

```lean
{α : Sort u} → {β : Sort v} → α → β → PProd α β
```

### D128: `PUnit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `10`
- Semantic SHA-256: `50562948622e7272ab5a2c0f9fcc2a46933f516e02ad00c5deddc196666390b0`

Type:

```lean
PUnit
```
