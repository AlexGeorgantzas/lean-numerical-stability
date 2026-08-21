# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m : Nat} (run : LocalDef002 m),
  And
    (Exists fun θ0 =>
      Exists fun θ =>
        And (Real.instLE.le (abs θ0) (instHMul.hMul (instHAdd.hAdd m 1).cast run.format.unitRoundoff))
          (And
            (∀ (i : Fin m), Real.instLE.le (abs (θ i)) (instHMul.hMul (instHAdd.hAdd m 1).cast run.format.unitRoundoff))
            (Eq (instHMul.hMul (instHMul.hMul run.bK run.yHat) (instHAdd.hAdd 1 θ0))
              (instHSub.hSub run.c
                (Finset.univ.sum fun i => instHMul.hMul (instHMul.hMul (run.a i) (run.b i)) (instHAdd.hAdd 1 (θ i)))))))
    (Eq run.bK 1 →
      Exists fun θ0 =>
        Exists fun θ =>
          And (Real.instLE.le (abs θ0) (instHMul.hMul m.cast run.format.unitRoundoff))
            (And (∀ (i : Fin m), Real.instLE.le (abs (θ i)) (instHMul.hMul m.cast run.format.unitRoundoff))
              (Eq (instHMul.hMul run.yHat (instHAdd.hAdd 1 θ0))
                (instHSub.hSub run.c
                  (Finset.univ.sum fun i =>
                    instHMul.hMul (instHMul.hMul (run.a i) (run.b i)) (instHAdd.hAdd 1 (θ i)))))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} (run : LocalDef002 m),
  And
    (@Exists.{1} Real fun (θ0 : Real) =>
      @Exists.{1} (Fin m → Real) fun (θ : Fin m → Real) =>
        And
          (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θ0)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (LocalDef001 (@LocalDef007 m run))))
          (And
            (∀ (i : Fin m),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (θ i))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (LocalDef001 (@LocalDef007 m run))))
            (@Eq.{1} Real
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@LocalDef005 m run) (@LocalDef008 m run))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) θ0))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@LocalDef006 m run)
                (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
                  fun (i : Fin m) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@LocalDef003 m run i) (@LocalDef004 m run i))
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (θ i)))))))
    (@Eq.{1} Real (@LocalDef005 m run)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Exists.{1} Real fun (θ0 : Real) =>
        @Exists.{1} (Fin m → Real) fun (θ : Fin m → Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θ0)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast m)
                (LocalDef001 (@LocalDef007 m run))))
            (And
              (∀ (i : Fin m),
                @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (θ i))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast m)
                    (LocalDef001 (@LocalDef007 m run))))
              (@Eq.{1} Real
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@LocalDef008 m run)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) θ0))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@LocalDef006 m run)
                  (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
                    fun (i : Fin m) =>
                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@LocalDef003 m run i) (@LocalDef004 m run i))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (θ i)))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `240724a17aa0df9cc56d34d7095bbb0b8cdde2c0852bf68b221e250958fd7af6`

Type:

```lean
LocalDef009 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.13
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `54f7fb21338d460d95ba24f4f68ec1e88485ff544bfc11cf2639399316ad8dad`

Type:

```lean
Nat → Type
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c74f6cc7255c2553bd8a9833b413e7541ce56f438556ea843f8fc99f4156b157`

Type:

```lean
{m : Nat} → LocalDef002 m → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.2
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bad0fe7139c08bbb1859577b06ffb3ed0e035d3317d600ae0b0da9051afed006`

Type:

```lean
{m : Nat} → LocalDef002 m → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.3
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `91a236cf4b3aba3f088617d30f2b25bdb2774e5b236857b4989ee1b529b3db9e`

Type:

```lean
{m : Nat} → LocalDef002 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.4
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `efe594e7c21046e128f080bccd7ed684eaf4183c2a331fb724ec19789e7e476a`

Type:

```lean
{m : Nat} → LocalDef002 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.5
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `aadc2a3d9c85a3ab5b73d3632b6c83d3467e27ed03f5d86fced67a9d0489ddc8`

Type:

```lean
{m : Nat} → LocalDef002 m → LocalDef009
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.1
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0ea6a1e617cc6ab3454bdd82d96f6a2e77e34b288a84c60f304a9999b7957d65`

Type:

```lean
{m : Nat} → LocalDef002 m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.18
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `0ddacc640e57cd98fa542c796ebf4288f8e3c1b48d1de954147bdb407876ca70`

Type:

```lean
Type
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `862950970286edcafebebdba5b40a3a83b3bdeb0cbcf22fa67880fa1716ca75e`

Type:

```lean
{m : Nat} →
  (format : LocalDef009) →
    (a b : Fin m → Real) →
      (bK c : Real) →
        (∀ (i : Fin m), format.representable (a i)) →
          (∀ (i : Fin m), format.representable (b i)) →
            format.representable bK →
              format.representable c →
                Ne bK 0 →
                  (∀ (i : Fin m), format.safeRange (instHMul.hMul (a i) (b i))) →
                    (tree : LocalDef016 (instHAdd.hAdd m 1)) →
                      (order : Equiv.Perm (Fin (instHAdd.hAdd m 1))) →
                        (LocalDef019 format tree fun i =>
                            LocalDef017 format a b c (EquivLike.toFunLike.coe order i)) →
                          (numerator : Real) →
                            Eq numerator
                                (LocalDef018 format tree fun i =>
                                  LocalDef017 format a b c (EquivLike.toFunLike.coe order i)) →
                              LocalDef015 format (instHAdd.hAdd m 1) c
                                  (Real.instNeg.neg (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                  (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i))) numerator →
                                (yHat : Real) →
                                  (Eq bK 1 → Eq yHat numerator) →
                                    (Ne bK 1 → format.safeRange (instHDiv.hDiv numerator bK)) →
                                      (Ne bK 1 → Eq yHat (format.round (instHDiv.hDiv numerator bK))) →
                                        LocalDef002 m
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `ecaddec79880b04dfdf13674f536ffbb4d7235acab8561630b95068d92769d1e`

Type:

```lean
(radix precision : Nat) →
  (minExponent maxExponent : Int) →
    instLENat.le 2 radix →
      instLTNat.lt 0 precision →
        Int.instLTInt.lt minExponent maxExponent →
          (representable : Real → Prop) →
            (setOf fun x => representable x).Finite →
              (∀ (x : Real),
                  representable x →
                    Or (Eq x 0)
                      (Exists fun m =>
                        Exists fun e =>
                          And (instLTNat.lt m.natAbs (instHPow.hPow radix precision))
                            (And (Int.instLEInt.le minExponent e)
                              (And (Int.instLEInt.le e maxExponent)
                                (Eq x
                                  (instHMul.hMul m.cast
                                    (instHPow.hPow radix.cast
                                      (instHSub.hSub e (instHSub.hSub precision.cast 1))))))))) →
                (safeRange : Real → Prop) →
                  (round : Real → Real) →
                    (unitRoundoff : Real) →
                      Real.instLE.le 0 unitRoundoff →
                        Real.instLE.le unitRoundoff (1 / 2) →
                          Eq
                              (instHMul.hMul unitRoundoff
                                (instHMul.hMul 2 (instHPow.hPow radix.cast (instHSub.hSub precision 1))))
                              1 →
                            representable 0 →
                              representable 1 →
                                (∀ (x : Real), representable x → representable (Real.instNeg.neg x)) →
                                  (∀ (x : Real), safeRange x → representable (round x)) →
                                    (∀ (x : Real),
                                        safeRange x →
                                          ∀ (z : Real),
                                            representable z →
                                              Real.instLE.le (abs (instHSub.hSub x (round x)))
                                                (abs (instHSub.hSub x z))) →
                                      (∀ (x : Real),
                                          safeRange x →
                                            Real.instLE.le (abs (instHSub.hSub (round x) x))
                                              (instHMul.hMul unitRoundoff (abs (round x)))) →
                                        (∀ (x : Real), Real.instLE.le 0 x → safeRange x → Real.instLE.le 0 (round x)) →
                                          (∀ (x : Real),
                                              Real.instLE.le 0 x →
                                                representable x →
                                                  safeRange x.sqrt →
                                                    Real.instLE.le
                                                      (abs (instHSub.hSub (instHPow.hPow (round x.sqrt) 2) x))
                                                      (instHMul.hMul (instHMul.hMul 2 unitRoundoff)
                                                        (abs (instHPow.hPow (round x.sqrt) 2)))) →
                                            (∀ (x : Real), representable x → Eq (round x) x) →
                                              LocalDef009
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `939843e6234b6b60e9493201a37a6f0770ba8ba2ffd11eb2e38ddcaa236b4ed2`

Type:

```lean
LocalDef009 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9809b8471476999f734ffd0dd64b33e1b0bf7334f8f013398d3e4e55bfbf9844`

Type:

```lean
LocalDef009 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.12
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `df0de3d94a11777d107bf4cb6f38361be0bd84e36bc1d91b5eaffe534762b511`

Type:

```lean
LocalDef009 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.11
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `af57b1332cc6b515c4631fb5af5b6e4263bd0074340bbc55f856fecb3398b943`

Type:

```lean
LocalDef009 → Nat → Real → Real → Real → Real → Prop
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `443a0aa6f83664582344d89f72b609bc7af3d2025eacff100aebdbcacb0938fc`

Type:

```lean
Nat → Type
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `53288ef5dcd6dce907f195ffd0fdcbfaebf7b436ac8098403000f49182a3ede0`

Type:

```lean
{m : Nat} →
  LocalDef009 → (Fin m → Real) → (Fin m → Real) → Real → Fin (instHAdd.hAdd m 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b c i => Fin.cases c (fun i => Real.instNeg.neg (LocalDef026 fmt a b i)) i
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5276000dc42400351a4955f3911dcae4de8b74de2fb84b50d07230a884af2020`

Type:

```lean
LocalDef009 → {n : Nat} → LocalDef016 n → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  LocalDef023 (motive := fun {n} tree => (Fin n → Real) → Real) tree
    (fun {n} tree f v =>
      LocalDef028
        (fun n tree v => LocalDef022 (motive := fun {n} tree => (Fin n → Real) → Real) tree → Real) n
        tree v (fun v x => v ⟨0, LocalDef027⟩)
        (fun m n left right v x =>
          fmt.round (instHAdd.hAdd (x.1.1 fun i => v (Fin.castAdd n i)) (x.2.1 fun i => v (Fin.natAdd m i))))
        f)
    v
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `28c67f1f1f332ec7ed8f24f988fff25480a126aa5735959a513d27837bc19587`

Type:

```lean
LocalDef009 → {n : Nat} → LocalDef016 n → (Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  LocalDef023 (motive := fun {n} tree => (Fin n → Real) → Prop) tree
    (fun {n} tree f v =>
      LocalDef028
        (fun n tree v => LocalDef022 (motive := fun {n} tree => (Fin n → Real) → Prop) tree → Prop) n
        tree v (fun v x => fmt.representable (v ⟨0, LocalDef027⟩))
        (fun m n left right v x =>
          And (x.1.1 fun i => v (Fin.castAdd n i))
            (And (x.2.1 fun i => v (Fin.natAdd m i))
              (fmt.safeRange
                (instHAdd.hAdd (LocalDef018 fmt left fun i => v (Fin.castAdd n i))
                  (LocalDef018 fmt right fun i => v (Fin.natAdd m i))))))
        f)
    v
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e109540049043b0f228eae43e83638898445f10954918e8f096d36020385dc81`

Type:

```lean
∀ {fmt : LocalDef009} (pivotValue : Real),
  fmt.representable pivotValue → LocalDef015 fmt 1 pivotValue 0 0 pivotValue
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `ebe05edeb007569f5d6a1f98a923ce7a193878cfbce59f91cfd85618a32289c0`

Type:

```lean
∀ {fmt : LocalDef009} {outerCount siblingCount : Nat}
  {pivotValue siblingExact siblingAbs siblingComputed outerExact outerAbs computed : Real},
  fmt.representable pivotValue →
    instLTNat.lt 0 siblingCount →
      Real.instLE.le 0 siblingAbs →
        Real.instLE.le (abs siblingExact) siblingAbs →
          fmt.representable siblingComputed →
            Real.instLE.le (abs (instHSub.hSub siblingComputed siblingExact))
                (instHMul.hMul (instHMul.hMul siblingCount.cast fmt.unitRoundoff) siblingAbs) →
              fmt.safeRange (instHAdd.hAdd pivotValue siblingComputed) →
                LocalDef015 fmt outerCount (fmt.round (instHAdd.hAdd pivotValue siblingComputed))
                    outerExact outerAbs computed →
                  LocalDef015 fmt (instHAdd.hAdd outerCount siblingCount) pivotValue
                    (instHAdd.hAdd siblingExact outerExact) (instHAdd.hAdd siblingAbs outerAbs) computed
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `04678a12719fff926622b3e9fbf38f572093e387c69fa03eb32cb222cd68fe1a`

Type:

```lean
{motive : (a : Nat) → LocalDef016 a → Sort u} → {a : Nat} → LocalDef016 a → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t =>
  LocalDef031 PUnit
    (fun {m n} a a_1 a_ih a_ih_1 => PProd (PProd (motive m a) a_ih) (PProd (motive n a_1) a_ih_1)) t
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cb3c6322835a978db412df67d07972af7f5ebc95b2fe7fffd3f78ab7c1c10544`

Type:

```lean
{motive : (a : Nat) → LocalDef016 a → Sort u} →
  {a : Nat} →
    (t : LocalDef016 a) →
      ((a : Nat) → (t : LocalDef016 a) → LocalDef022 t → motive a t) → motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 => (LocalDef029 t F_1).1
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `d400482110f6735443dd560bbbc8525a6db52e539e45f92488e808fd742cb999`

Type:

```lean
LocalDef016 1
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `47eb0dcdab89e52469860668ea9ff917c63ab85960c92a40c58d7885ba4b7f44`

Type:

```lean
{m n : Nat} → LocalDef016 m → LocalDef016 n → LocalDef016 (instHAdd.hAdd m n)
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `9cc6e82bd9680cd814e1f49e1260fe201a0535af0efdf7c523fa734c4b1cf26e`

Type:

```lean
{m : Nat} → LocalDef009 → (Fin m → Real) → (Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b i => fmt.round (instHMul.hMul (a i) (b i))
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `3837ff05fe96904abf1d46536ea66370e1afc147c8f02d6219701e1854673c5f`

Type:

```lean
Nat.instPartialOrder.lt 0 1
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `628dea76c4d1a3a85ca7248eb8dbbe9298030d0d3d089ceb2f318990b1196f40`

Type:

```lean
(motive : (n : Nat) → LocalDef016 n → (Fin n → Real) → Sort u_1) →
  (n : Nat) →
    (tree : LocalDef016 n) →
      (v : Fin n → Real) →
        ((v : Fin 1 → Real) → motive 1 LocalDef024 v) →
          ((m n : Nat) →
              (left : LocalDef016 m) →
                (right : LocalDef016 n) →
                  (v : Fin (instHAdd.hAdd m n) → Real) → motive (instHAdd.hAdd m n) (left.node right) v) →
            motive n tree v
```

Definition body (one-level semantic boundary):

```lean
fun motive n tree v h_1 h_2 =>
  (fun tree_1 =>
      LocalDef030 (motive := fun a x => Eq n a → HEq tree x → motive n tree v) tree_1
        (fun h =>
          Eq.ndrec (motive := fun n =>
            (tree : LocalDef016 n) →
              (v : Fin n → Real) → HEq tree LocalDef024 → motive n tree v)
            (fun tree v h => Eq.ndrec (h_1 v) ⋯) ⋯ tree v)
        fun {m n_1} a a_1 h =>
        Eq.ndrec (motive := fun n =>
          (tree : LocalDef016 n) → (v : Fin n → Real) → HEq tree (a.node a_1) → motive n tree v)
          (fun tree v h => Eq.ndrec (h_2 m n_1 a a_1 v) ⋯) ⋯ tree v)
    tree ⋯ ⋯
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a1f5b5d0ff724fb25f8c6eb41f3392a734a4bd8a54fa24702cb5c1c49c98e9b7`

Type:

```lean
{motive : (a : Nat) → LocalDef016 a → Sort u} →
  {a : Nat} →
    (t : LocalDef016 a) →
      ((a : Nat) → (t : LocalDef016 a) → LocalDef022 t → motive a t) →
        PProd (motive a t) (LocalDef022 t)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 =>
  LocalDef031 ⟨F_1 1 LocalDef024 PUnit.unit, PUnit.unit⟩
    (fun {m n} a a_1 a_ih a_ih_1 => ⟨F_1 (instHAdd.hAdd m n) (a.node a_1) ⟨a_ih, a_ih_1⟩, a_ih, a_ih_1⟩) t
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `6a2f271359e9f74faaece28f70b9cc38b461b3d2ac2b2cacdbb565586e6814f8`

Type:

```lean
{motive : (a : Nat) → LocalDef016 a → Sort u} →
  {a : Nat} →
    (t : LocalDef016 a) →
      motive 1 LocalDef024 →
        ({m n : Nat} →
            (a : LocalDef016 m) →
              (a_1 : LocalDef016 n) → motive (instHAdd.hAdd m n) (a.node a_1)) →
          motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t leaf node => LocalDef031 leaf (fun {m n} a a_1 a_ih a_ih_1 => node a a_1) t
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `5`
- Semantic SHA-256: `9b30df98c9e7570f0a4522ebeddf3fffb65f3cfaa16bd8c18752e6df00414a03`

Type:

```lean
{motive : (a : Nat) → LocalDef016 a → Sort u} →
  motive 1 LocalDef024 →
    ({m n : Nat} →
        (a : LocalDef016 m) →
          (a_1 : LocalDef016 n) → motive m a → motive n a_1 → motive (instHAdd.hAdd m n) (a.node a_1)) →
      {a : Nat} → (t : LocalDef016 a) → motive a t
```

### D032: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D033: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D034: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D035: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D036: `Fin.fintype`

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

### D037: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D038: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D039: `HAdd.hAdd`

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

### D040: `HMul.hMul`

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

### D041: `HSub.hSub`

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

### D042: `LE.le`

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

### D043: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D044: `Nat.cast`

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

### D045: `OfNat.ofNat`

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

### D046: `One.toOfNat1`

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

### D047: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D048: `Real.instAdd`

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

### D049: `Real.instAddCommMonoid`

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

### D050: `Real.instAddGroup`

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

### D051: `Real.instLE`

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

### D052: `Real.instMul`

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

### D053: `Real.instNatCast`

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

### D054: `Real.instOne`

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

### D055: `Real.instSub`

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

### D056: `Real.lattice`

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

### D057: `abs`

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

### D058: `instAddNat`

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

### D059: `instHAdd`

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

### D060: `instHMul`

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

### D061: `instHSub`

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

### D062: `instOfNatNat`

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

### D063: `DFunLike.coe`

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

### D064: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D065: `Equiv.Perm`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c8be4339de7efaee2aff8b13efc12794f5acd112d4188f63d38d39f9e4bd687c`

Type:

```lean
Sort u_1 → Sort (max 1 u_1)
```

Definition body (one-level semantic boundary):

```lean
fun α => Equiv α α
```

### D066: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D067: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D068: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D069: `Ne`

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

### D070: `Neg.neg`

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

### D071: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D072: `Real.instNeg`

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

### D073: `Real.instZero`

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

### D074: `Zero.toOfNat0`

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

### D075: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D076: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `1e8b6758b3a3bf88b78eeff1bb4effb1dce39e6b9e38153dab79b664d58d89b5`

Type:

```lean
{M : Type u_2} → [DivInvMonoid M] → Pow M Int
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : DivInvMonoid M] => { pow := fun x n => inst.zpow n x }
```

### D077: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D078: `Fin.castAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `bff7b13dfc77fda725a938338f6d0c6fbe5d5b328cd5c9a1c9de44224915838b`

Type:

```lean
{n : Nat} → (m : Nat) → Fin n → Fin (instHAdd.hAdd n m)
```

Definition body (one-level semantic boundary):

```lean
fun {n} m => Fin.castLE ⋯
```

### D079: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D080: `Fin.natAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `06007c678fab1dc171aa2b490b41eb467e5f51799a25bb0c10890e6946480989`

Type:

```lean
{m : Nat} → (n : Nat) → Fin m → Fin (instHAdd.hAdd n m)
```

Definition body (one-level semantic boundary):

```lean
fun {m} n i => ⟨instHAdd.hAdd n i.val, ⋯⟩
```

### D081: `HPow.hPow`

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

### D082: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

### D083: `Int.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `3347681a56db726f3d5ec40fea35e331466578d6194deeb554a0c70ba5189971`

Type:

```lean
{R : Type u} → [IntCast R] → Int → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : IntCast R] => inst.intCast
```

### D084: `Int.instLEInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f51330a4994f7ae8126646c50493b06244696bcf7ecd84ee76d837ba05820e15`

Type:

```lean
LE Int
```

Definition body (one-level semantic boundary):

```lean
{ le := Int.le }
```

### D085: `Int.instLTInt`

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

### D086: `Int.instSub`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cdec027f4b1a52ca9841248e8efbabc901ed4e9b4220aa4074044d4c9537c68c`

Type:

```lean
Sub Int
```

Definition body (one-level semantic boundary):

```lean
{ sub := Int.sub }
```

### D087: `Int.natAbs`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2471688866fdc8c23fee672544006ebded1ade779a01e774c737876f989b77f9`

Type:

```lean
Int → Nat
```

Definition body (one-level semantic boundary):

```lean
fun m => Int.neg.match_1 (fun m => Nat) m (fun m => m) fun m => m.succ
```

### D088: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D089: `Monoid.toNatPow`

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

### D090: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D091: `Nat.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `de0cbde8dd75c1a0c6d5d08b9cfa1cd5908aeb874409a1c880c9c9616deb1709`

Type:

```lean
Monoid Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D092: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D093: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

### D094: `Real.instIntCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7ad2826677bdd498c1fca7a01f5af78c74e38b65a4f1e767cdf3670649eac222`

Type:

```lean
IntCast Real
```

Definition body (one-level semantic boundary):

```lean
{ intCast := fun z => { cauchy := z.cast } }
```

### D095: `Real.instMonoid`

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

### D096: `Real.sqrt`

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

### D099: `instLENat`

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

### D100: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D101: `instNatCastInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7fb46bceee4f1142c75008c8ac4be64c11c4bdbc7972ff89c0a5335ad80a2033`

Type:

```lean
NatCast Int
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => Int.ofNat n }
```

### D102: `instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d01cf83431e28a96433c57a624e20a771e5e0ddc02355969c5044adf1ba168a5`

Type:

```lean
{n : Nat} → OfNat Int n
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { ofNat := Int.ofNat n }
```

### D103: `instOfNatAtLeastTwo`

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

### D104: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

Type:

```lean
Sub Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
```

### D105: `setOf`

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

### D106: `Eq.ndrec`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `f86cb68b5cbbf1ddc06f9f211e3421eced11542c1e459b8ba4c1e06c0f8ca7d2`

Type:

```lean
{α : Sort u2} → {a : α} → {motive : α → Sort u1} → motive a → {b : α} → Eq a b → motive b
```

Definition body (one-level semantic boundary):

```lean
fun {α} {a} {motive} m {b} h => Eq.rec m h
```

### D107: `Eq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `62d4020b7012db70e44624c7d64dd267524e7e75e4b869680e0c95d2231c85d1`

Type:

```lean
∀ {α : Sort u_1} (a : α), Eq a a
```

### D108: `Eq.symm`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `7c9d5428fd9feab69045077277e3f895072f20edba5f2a9479559efbee9f7cf2`

Type:

```lean
∀ {α : Sort u} {a b : α}, Eq a b → Eq b a
```

### D109: `HEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `a71d8d31511fc844f0f70ae865b109282edf2e9593d6acbdee9925cd9e03d1db`

Type:

```lean
{α : Sort u} → α → {β : Sort u} → β → Prop
```

### D110: `HEq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `15ec9e197e90776f1db6670d1ce41d43e6ba50700a0f4752439b345b47e5d1c9`

Type:

```lean
∀ {α : Sort u} (a : α), HEq a a
```

### D111: `Nat.instPartialOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `2759981f152e80eec9150e4e0e23de292150f9cea0c8c910125cf9e56acf2f67`

Type:

```lean
PartialOrder Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D112: `PProd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `f220f3fbfda558146d81aa3a9391a551a0b414f82b31ddca68583a9f3b829035`

Type:

```lean
Sort u → Sort v → Sort (max (max 1 u) v)
```

### D113: `PUnit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `766f980214e36af1ff35d2ec98c8393266d25d4a847f71e22766f564898fc02c`

Type:

```lean
Sort u
```

### D114: `PartialOrder.toPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `079686fa1ec6d596bcdb475c56a12b7f5a0594bf346c64220c2c992e0f0aae3b`

Type:

```lean
{α : Type u_2} → [self : PartialOrder α] → Preorder α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PartialOrder α] => self.1
```

### D115: `Preorder.toLT`

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

### D116: `eq_of_heq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `17dda0f4fb758715279a058b25c7babf034d9cf08d6d9ae8a500eaf0c83d4724`

Type:

```lean
∀ {α : Sort u} {a a' : α}, HEq a a' → Eq a a'
```

### D117: `PProd.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `77a288dd932e98f780ede81f87af6b4ae802bc357db102e11bc037200b5d6eb0`

Type:

```lean
{α : Sort u} → {β : Sort v} → α → β → PProd α β
```

### D118: `PUnit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `50562948622e7272ab5a2c0f9fcc2a46933f516e02ad00c5deddc196666390b0`

Type:

```lean
PUnit
```
