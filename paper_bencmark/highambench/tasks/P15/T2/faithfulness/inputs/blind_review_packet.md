# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {b r : Nat} (run : LocalDef001 b r),
  have Atilde := LocalDef016 run.X run.Y;
  have deltaAtilde := LocalDef017 run;
  have deltaA := LocalDef018 run;
  have gammaC := LocalDef014 (LocalDef015 b r) run.unitRoundoff;
  And (Eq run.zHat (LocalDef019 (instHAdd.hAdd Atilde deltaAtilde) run.v))
    (And (Real.instLE.le (LocalDef013 deltaAtilde) (instHMul.hMul gammaC (LocalDef013 Atilde)))
      (And (Eq deltaA (instHAdd.hAdd run.truncError deltaAtilde))
        (And (Eq run.zHat (LocalDef019 (instHAdd.hAdd run.A deltaA) run.v))
          (And
            (Real.instLE.le (LocalDef013 deltaA)
              (instHAdd.hAdd (instHMul.hMul gammaC (LocalDef013 run.A))
                (instHMul.hMul (instHMul.hMul run.epsilon (instHAdd.hAdd 1 gammaC)) run.beta)))
            (Eq
              (instHAdd.hAdd (instHMul.hMul gammaC (LocalDef013 run.A))
                (instHMul.hMul (instHMul.hMul run.epsilon (instHAdd.hAdd 1 gammaC)) run.beta))
              (instHAdd.hAdd
                (instHAdd.hAdd (instHMul.hMul gammaC (LocalDef013 run.A))
                  (instHMul.hMul run.epsilon run.beta))
                (instHMul.hMul (instHMul.hMul run.epsilon gammaC) run.beta)))))))
```

## Fully explicit elaborated target type

```lean
∀ {b r : Nat} (run : LocalDef001 b r),
  have Atilde : LocalDef011 b :=
    @LocalDef016 b r (@LocalDef003 b r run)
      (@LocalDef004 b r run);
  have deltaAtilde : LocalDef011 b := @LocalDef017 b r run;
  have deltaA : LocalDef011 b := @LocalDef018 b r run;
  have gammaC : Real :=
    LocalDef014 (LocalDef015 b r)
      (@LocalDef008 b r run);
  And
    (@Eq.{1} (LocalDef012 b) (@LocalDef010 b r run)
      (@LocalDef019 b
        (@HAdd.hAdd.{0, 0, 0} (LocalDef011 b) (LocalDef011 b) (LocalDef011 b)
          (@instHAdd.{0} (LocalDef011 b) (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd)) Atilde
          deltaAtilde)
        (@LocalDef009 b r run)))
    (And
      (@LE.le.{0} Real Real.instLE (@LocalDef013 b deltaAtilde)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
          (@LocalDef013 b Atilde)))
      (And
        (@Eq.{1} (LocalDef011 b) deltaA
          (@HAdd.hAdd.{0, 0, 0} (LocalDef011 b) (LocalDef011 b) (LocalDef011 b)
            (@instHAdd.{0} (LocalDef011 b) (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
            (@LocalDef007 b r run) deltaAtilde))
        (And
          (@Eq.{1} (LocalDef012 b) (@LocalDef010 b r run)
            (@LocalDef019 b
              (@HAdd.hAdd.{0, 0, 0} (LocalDef011 b) (LocalDef011 b) (LocalDef011 b)
                (@instHAdd.{0} (LocalDef011 b) (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                (@LocalDef002 b r run) deltaA)
              (@LocalDef009 b r run)))
          (And
            (@LE.le.{0} Real Real.instLE (@LocalDef013 b deltaA)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
                  (@LocalDef013 b (@LocalDef002 b r run)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@LocalDef006 b r run)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC))
                  (@LocalDef005 b r run))))
            (@Eq.{1} Real
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
                  (@LocalDef013 b (@LocalDef002 b r run)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@LocalDef006 b r run)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC))
                  (@LocalDef005 b r run)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
                    (@LocalDef013 b (@LocalDef002 b r run)))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@LocalDef006 b r run)
                    (@LocalDef005 b r run)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@LocalDef006 b r run) gammaC)
                  (@LocalDef005 b r run))))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `67a164adfad3cffa94f2cf1fde51e4f3703e1403fde3b8ae568b6895ec64299b`

Type:

```lean
Nat → Nat → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6e30d22cfc669f6856dbab37de86385c57e1b4dc4d742c07ef8518fd6b803249`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef011 b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.1
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8e77e19d70fd221905e4136fe4b01d621a7939fc4f27aaa6638e6e70ed54907c`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef023 b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.2
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `62a00b7ed147a54c969c3b9660854e1b7e8aa27e7064637ecc439065f7c1f1e7`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef023 b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.3
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `df90d9c7d4607e6e387b46e97cffd3aa7280ed588826bdd4b208fbbfad78ddac`

Type:

```lean
{b r : Nat} → LocalDef001 b r → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.6
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3b183d83dcac470a80c6c878f5c2f45c8387c8a490b6b03555df117bcac25509`

Type:

```lean
{b r : Nat} → LocalDef001 b r → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.5
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `48809e8b04fca8107ec6b21aa9221313129c4e765111be9f48e218792888b74a`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef011 b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.14
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ab98e38f648e04dd2490415472c70d00d3b4d586006201b69d23196c9f026fc4`

Type:

```lean
{b r : Nat} → LocalDef001 b r → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.7
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3dcb50974bdb8854d08a5bb633d7d01ceaab930f21239aa688f0fcaf7e683a1f`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef012 b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.4
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `47cc025833c11804ed58cb1e81c0ec91285a182bc64d4e15591de45494fd650a`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef012 b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.18
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `15e7e37c5731d7df61fbacb22e39e6f80678f5f9880fecbb579e57644d05505c`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837bd1b4fd433e90b49e653f1245c95156c8bd043250d89a7117737646408c28`

Type:

```lean
{n : Nat} → LocalDef011 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => LocalDef024 A
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `271296c936d7dd54bb763543aed321ddd01215dbcf43ad0f046996eedec71821`

Type:

```lean
Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun k u => instHDiv.hDiv (instHMul.hMul k u) (instHSub.hSub 1 (instHMul.hMul k u))
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c2fe5f62aae01995df6fd00f4964b121fe67637620e558fead3ee0984d93d978`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r => instHAdd.hAdd b.cast (instHMul.hMul r.cast r.cast.sqrt)
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1842193034dc631c3f6c3edebfa469daf6e8b41c15a0037f9331a904ad932e6f`

Type:

```lean
{b r : Nat} → LocalDef023 b r → LocalDef023 b r → LocalDef011 b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X Y => LocalDef025 X (LocalDef026 Y)
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0166a93fefabdd5c8742e70f488e51ff14d6f04a642f1928cf4c446d5fdc9483`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef011 b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} run =>
  instHAdd.hAdd
    (instHAdd.hAdd (LocalDef025 run.X (LocalDef026 run.deltaY))
      (LocalDef025 run.deltaX (LocalDef026 run.Y)))
    (LocalDef025 run.deltaX (LocalDef026 run.deltaY))
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0d552b63905aa2488b56da39ce2722e44456405d7caf4cba2224db361cbc47f0`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef011 b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} run => instHAdd.hAdd run.truncError (LocalDef017 run)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `46653426fb5f80e06b04a77772652321fa618edf797127f16a95ad856ba2a7a8`

Type:

```lean
{n : Nat} → LocalDef011 n → LocalDef012 n → LocalDef012 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `87c2eb3b57cef1e88e0d9b5554099487b3cacf3e5ed82a787eb90098423a4c72`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef023 b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.20
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2bf98a6c631b0b7707666fca51c464d756448a67f8213576e729bfc681bcadf9`

Type:

```lean
{b r : Nat} → LocalDef001 b r → LocalDef023 b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.19
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1f282b82b969ca6e09539ac78b6cb586f7df10620bacb33764f3f855bd2a275c`

Type:

```lean
{b r : Nat} →
  (A : LocalDef011 b) →
    (X Y : LocalDef023 b r) →
      (v : LocalDef012 b) →
        (epsilon beta unitRoundoff : Real) →
          Real.instLT.lt 0 epsilon →
            Real.instLT.lt 0 beta →
              Real.instLT.lt 0 unitRoundoff →
                Real.instLT.lt unitRoundoff epsilon →
                  Real.instLT.lt (instHMul.hMul (LocalDef015 b r) unitRoundoff) 1 →
                    LocalDef027 X →
                      (truncError : LocalDef011 b) →
                        Eq (LocalDef016 X Y) (instHAdd.hAdd A truncError) →
                          Real.instLE.le (LocalDef013 truncError) (instHMul.hMul epsilon beta) →
                            (wHat : LocalDef012 r) →
                              (zHat : LocalDef012 b) →
                                (deltaY deltaX : LocalDef023 b r) →
                                  Eq wHat
                                      (LocalDef028 (LocalDef026 (instHAdd.hAdd Y deltaY))
                                        v) →
                                    Real.instLE.le (LocalDef024 deltaY)
                                        (instHMul.hMul (LocalDef014 b.cast unitRoundoff)
                                          (LocalDef024 Y)) →
                                      Eq zHat (LocalDef028 (instHAdd.hAdd X deltaX) wHat) →
                                        Real.instLE.le (LocalDef024 deltaX)
                                            (instHMul.hMul (LocalDef014 r.cast unitRoundoff)
                                              (LocalDef024 X)) →
                                          LocalDef001 b r
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8feb40d08c5292d10bb340b09678c4d176088c4c97bb1880d9f95a2c76fde9a2`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f8df59150997c9c35d296b01efb6efe480f420d12b4d3873085fbf5fff732e33`

Type:

```lean
{m n : Nat} → LocalDef023 m n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f6707f2e526a146358f007d2349847963679a3556d53c05f30fd242f90c18238`

Type:

```lean
{m n p : Nat} → LocalDef023 m n → LocalDef023 n p → LocalDef023 m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5d09057ba3a21630e320ba9e9e5153de687ba08c185951b20149ba794d3de258`

Type:

```lean
{m n : Nat} → LocalDef023 m n → LocalDef023 n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A j i => A i j
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `deb9d644f031d8e71a57f0238d55fc37a145cb41cbb82b90abe8a87780c03815`

Type:

```lean
{b r : Nat} → LocalDef023 b r → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X => ∀ (j k : Fin r), Eq (Finset.univ.sum fun i => instHMul.hMul (X i j) (X i k)) (ite (Eq j k) 1 0)
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `970543238cae5239ce90751326e588c2728317ac37bdac78ce2f145b8ad3cf35`

Type:

```lean
{m n : Nat} → LocalDef023 m n → (Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D029: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D030: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D031: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D032: `HAdd.hAdd`

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

### D033: `HMul.hMul`

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

### D034: `LE.le`

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

### D035: `Matrix.add`

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

### D036: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
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

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D038: `One.toOfNat1`

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

### D039: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D040: `Real.instAdd`

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

### D041: `Real.instLE`

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

### D042: `Real.instMul`

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

### D043: `Real.instOne`

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

### D044: `instHAdd`

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

### D045: `instHMul`

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

### D046: `DivInvMonoid.toDiv`

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

### D047: `Fin.fintype`

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

### D048: `Finset.sum`

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

### D049: `Finset.univ`

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

### D050: `HDiv.hDiv`

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

### D051: `HSub.hSub`

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

### D052: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D053: `Nat.cast`

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

### D054: `Real.instAddCommMonoid`

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

### D055: `Real.instDivInvMonoid`

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

### D056: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D057: `Real.instSub`

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

### D058: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D059: `instHDiv`

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

### D060: `instHSub`

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

### D061: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D062: `LT.lt`

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

### D063: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D064: `Real.instLT`

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

### D065: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D066: `Real.instZero`

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

### D067: `Zero.toOfNat0`

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

### D068: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D069: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D070: `instDecidableEqFin`

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

### D071: `ite`

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
