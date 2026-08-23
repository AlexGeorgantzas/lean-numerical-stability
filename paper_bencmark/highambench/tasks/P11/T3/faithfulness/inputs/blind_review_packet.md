# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m n : Nat} (family : LocalDef001 m n)
  (analysis : LocalDef007 family) (epsilonM : LocalDef006),
  Real.instLE.le epsilonM.val (LocalDef014 family analysis) →
    ∀ (k : Fin n),
      Real.instLE.le
        (LocalDef012
          (LocalDef013 (LocalDef009 (family.run epsilonM).Q k)))
        (instHAdd.hAdd
          (instHMul.hMul
            (instHMul.hMul (LocalDef008 m (instHAdd.hAdd k.val 1))
              (instHPow.hPow
                (LocalDef010 (LocalDef011 (family.run epsilonM).R k)
                  ((family.run epsilonM).leadingInverse k))
                2))
            epsilonM.val)
          (instHMul.hMul (LocalDef015 family analysis k)
            (instHPow.hPow epsilonM.val 2)))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (family : LocalDef001 m n)
  (analysis : @LocalDef007 m n family) (epsilonM : LocalDef006),
  @LE.le.{0} Real Real.instLE
      (@Subtype.val.{1} Real
        (fun (epsilonM : Real) =>
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            epsilonM)
        epsilonM)
      (@LocalDef014 m n family analysis) →
    ∀ (k : Fin n),
      @LE.le.{0} Real Real.instLE
        (@LocalDef012
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LocalDef013 m
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LocalDef009 m n
              (@LocalDef003 m n
                (@Subtype.val.{1} Real
                  (fun (epsilonM : Real) =>
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonM)
                  epsilonM)
                (@LocalDef002 m n family epsilonM))
              k)))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (LocalDef008 m
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (@LocalDef010
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@LocalDef011 n
                    (@LocalDef004 m n
                      (@Subtype.val.{1} Real
                        (fun (epsilonM : Real) =>
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonM)
                        epsilonM)
                      (@LocalDef002 m n family epsilonM))
                    k)
                  (@LocalDef005 m n
                    (@Subtype.val.{1} Real
                      (fun (epsilonM : Real) =>
                        @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonM)
                      epsilonM)
                    (@LocalDef002 m n family epsilonM) k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Subtype.val.{1} Real
              (fun (epsilonM : Real) =>
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  epsilonM)
              epsilonM))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@LocalDef015 m n family analysis k)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@Subtype.val.{1} Real
                (fun (epsilonM : Real) =>
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonM)
                epsilonM)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `88a1935a02345a7ece7f24d25d54db276a40ce62a31346678c19bc06888e4ec8`

Type:

```lean
Nat → Nat → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0af00203f35742cc830892a7abb6bd69539c231e0166920e5832d810b92c5a2d`

Type:

```lean
{m n : Nat} →
  LocalDef001 m n →
    (epsilonM : LocalDef006) → LocalDef022 m n epsilonM.val
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.2
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `581f4de292608e15b8e0532f19dbfe00df2f883d58b084d873ee576ba7bedd06`

Type:

```lean
{m n : Nat} → {epsilonM : Real} → LocalDef022 m n epsilonM → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n epsilonM self => self.5
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0efd4ec0000a47b04b116e0dc6570a51e9d2be911554eb18ca4b475be12bcb94`

Type:

```lean
{m n : Nat} → {epsilonM : Real} → LocalDef022 m n epsilonM → LocalDef023 n
```

Definition body (one-level semantic boundary):

```lean
fun m n epsilonM self => self.6
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `21c30ccaa5cbde88415cfde251ca0f535bda4cef9520e73605ae3a2797c012c5`

Type:

```lean
{m n : Nat} →
  {epsilonM : Real} →
    LocalDef022 m n epsilonM → (k : Fin n) → LocalDef023 (instHAdd.hAdd k.val 1)
```

Definition body (one-level semantic boundary):

```lean
fun m n epsilonM self => self.10
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bb2d959973ba6236a46c87a35e27742fe58ee6aabb2729bd7bd98aed1fab3a7b`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
Subtype fun epsilonM => Real.instLT.lt 0 epsilonM
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `27916e70fda34265f406f0ca22bf37bd69c970cec8694e0363b5e94c8e429bf8`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Type
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8f2c155c77d4c16aea80738b5ae7b604b872a12e62760f1c0ac8a302fbc4f743`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k => instHAdd.hAdd (LocalDef032 m k) (instHMul.hMul 2 (LocalDef030 m k))
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c78c40f5672660e00e3a8b29d027870cd22b7a49d516a1e5098f2d8afa8d83e`

Type:

```lean
{m n : Nat} → LocalDef024 m n → (k : Fin n) → LocalDef024 m (instHAdd.hAdd k.val 1)
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A k i j => A i (Fin.castLE ⋯ j)
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1f027b9831ac4b41c191c8155e75d236b1c2a94366da21461f0895f5a074537d`

Type:

```lean
{n : Nat} → LocalDef023 n → LocalDef023 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R Rinv => instHMul.hMul (LocalDef012 R) (LocalDef012 Rinv)
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1efb31586e183a13446325718b87a7358f5cc51a349c897b72d2e1837e075d2a`

Type:

```lean
{n : Nat} → LocalDef023 n → (k : Fin n) → LocalDef023 (instHAdd.hAdd k.val 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} R k i j => R (Fin.castLE ⋯ i) (Fin.castLE ⋯ j)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9e3c517d428a26eec754111d483048d655c05f52bfdd2a9013cb15cff394ccee`

Type:

```lean
{n : Nat} → LocalDef023 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cf3a0f08435f90398f8b694ecf96446b253704af09c791b454e534eea2c5f7f8`

Type:

```lean
{m k : Nat} → LocalDef024 m k → LocalDef023 k
```

Definition body (one-level semantic boundary):

```lean
fun {m k} Q => instHSub.hSub (LocalDef034 k) (LocalDef036 (LocalDef038 Q) Q)
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0679cdb3a79ec63e28b1865db2820205b0afb7b350bc1b8e8598968f1081014e`

Type:

```lean
{m n : Nat} →
  (family : LocalDef001 m n) → LocalDef007 family → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} family analysis =>
  Real.instMin.min 1 (Real.instMin.min family.normBoundRadius (Real.instMin.min family.conditionRadius analysis.radius))
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `daf3c0beb3b8de1795ac8efb4d4363ea1ba6079497b52e361efb97cc87f950e6`

Type:

```lean
{m n : Nat} →
  (family : LocalDef001 m n) → LocalDef007 family → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} family analysis k =>
  have a := LocalDef037 (LocalDef009 family.A k);
  have rBound := family.rNormBound k;
  have inverseBound := family.inverseNormBound k;
  have normSlope :=
    instHAdd.hAdd (instHMul.hMul (LocalDef033 m (instHAdd.hAdd k.val 1)) rBound)
      (analysis.reverseNormSecondOrderCoeff k);
  have aSquareRemainder := instHAdd.hAdd (instHMul.hMul (instHMul.hMul 2 rBound) normSlope) (instHPow.hPow normSlope 2);
  have coreRemainder :=
    instHAdd.hAdd
      (instHAdd.hAdd (analysis.normalEquationSecondOrderCoeff k)
        (instHMul.hMul (instHMul.hMul 2 a) (analysis.factorizationSecondOrderCoeff k)))
      (instHPow.hPow
        (instHAdd.hAdd (instHMul.hMul (LocalDef030 m (instHAdd.hAdd k.val 1)) a)
          (analysis.factorizationSecondOrderCoeff k))
        2);
  instHMul.hMul (instHPow.hPow inverseBound 2)
    (instHAdd.hAdd (instHMul.hMul (LocalDef008 m (instHAdd.hAdd k.val 1)) aSquareRemainder) coreRemainder)
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `66cebf208963153caa509363b1c69714e536de1dd8080805cc59752867695b37`

Type:

```lean
{m n : Nat} → LocalDef001 m n → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.1
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6bc6cdbf4885a9deea5169d4a5b5a0681c9cc1e26bc416fc4f41a23d4d5c1bda`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.7
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1c2c32b6b9674d27e526876035a2d13cbd9704787f5e5526ed4f3505353a394f`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.5
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e0902c17763465a7b5a5eec4c11db2f74a8cbe8aad09e3da60ecc6306fbbbeda`

Type:

```lean
{m n : Nat} →
  (A : LocalDef024 m n) →
    (run : (epsilonM : LocalDef006) → LocalDef022 m n epsilonM.val) →
      (∀ (epsilonM : LocalDef006), Eq (run epsilonM).A A) →
        (rNormBound inverseNormBound : Fin n → Real) →
          (normBoundRadius conditionRadius : Real) →
            (∀ (k : Fin n), Real.instLE.le 0 (rNormBound k)) →
              (∀ (k : Fin n), Real.instLE.le 0 (inverseNormBound k)) →
                Real.instLT.lt 0 normBoundRadius →
                  Real.instLT.lt 0 conditionRadius →
                    (∀ (epsilonM : LocalDef006),
                        Real.instLE.le epsilonM.val normBoundRadius →
                          ∀ (k : Fin n),
                            Real.instLE.le (LocalDef012 (LocalDef011 (run epsilonM).R k))
                              (rNormBound k)) →
                      (∀ (epsilonM : LocalDef006),
                          Real.instLE.le epsilonM.val normBoundRadius →
                            ∀ (k : Fin n),
                              Real.instLE.le (LocalDef012 ((run epsilonM).leadingInverse k))
                                (inverseNormBound k)) →
                        (∀ (epsilonM : LocalDef006),
                            Real.instLE.le epsilonM.val conditionRadius →
                              ∀ (k : Fin n),
                                Real.instLT.lt
                                  (instHMul.hMul
                                    (instHMul.hMul (LocalDef008 m (instHAdd.hAdd k.val 1)) epsilonM.val)
                                    (instHPow.hPow
                                      (LocalDef010 (LocalDef011 (run epsilonM).R k)
                                        ((run epsilonM).leadingInverse k))
                                      2))
                                  1) →
                          LocalDef001 m n
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d11f6489a4a5472a85ff4f7abce601dc3528bfcb2648ef52dd3e0f6c030957bc`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.6
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a2fae4a96e544a316e9341fae3a2ac8a12542ec653dc07de98ae42fbdb3025fe`

Type:

```lean
{m n : Nat} → LocalDef001 m n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.4
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e151c45c3ec3ee714d94ed8106a6261c518dabc8ae96c0947bdd075e38bb9e51`

Type:

```lean
Nat → Nat → Real → Type
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `36cb62df059104618b8f64e14d1c7515ec97591f02a19d69708a101cde0e7dce`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `157fc1c63f67a701a836e52c7a1efe6c7c8816987afb4e184e7e849df6494e90`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4e91a1581c477a43d2069916a22cd9e2475db899d06582be1b7a3697a17c24da`

Type:

```lean
{m n : Nat} →
  {family : LocalDef001 m n} → LocalDef007 family → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n family self => self.1
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2262d8e81b97f436f5566d4fc78dcb80407fa784eb6f48da388143556e4d4e35`

Type:

```lean
{m n : Nat} →
  {family : LocalDef001 m n} →
    (factorizationSecondOrderCoeff normalEquationSecondOrderCoeff reverseNormSecondOrderCoeff : Fin n → Real) →
      (radius : Real) →
        (∀ (k : Fin n), Real.instLE.le 0 (factorizationSecondOrderCoeff k)) →
          (∀ (k : Fin n), Real.instLE.le 0 (normalEquationSecondOrderCoeff k)) →
            (∀ (k : Fin n), Real.instLE.le 0 (reverseNormSecondOrderCoeff k)) →
              Real.instLT.lt 0 radius →
                (∀ (epsilonM : LocalDef006),
                    Real.instLE.le epsilonM.val radius →
                      ∀ (k : Fin n),
                        Real.instLE.le
                          (LocalDef037 (LocalDef045 family epsilonM k))
                          (instHAdd.hAdd
                            (instHMul.hMul
                              (instHMul.hMul (LocalDef030 m (instHAdd.hAdd k.val 1))
                                (LocalDef037 (LocalDef009 family.A k)))
                              epsilonM.val)
                            (instHMul.hMul (factorizationSecondOrderCoeff k) (instHPow.hPow epsilonM.val 2)))) →
                  (∀ (epsilonM : LocalDef006),
                      Real.instLE.le epsilonM.val radius →
                        ∀ (k : Fin n),
                          Real.instLE.le
                            (LocalDef012
                              (LocalDef044 (LocalDef009 family.A k)
                                (LocalDef011 (family.run epsilonM).R k)))
                            (instHAdd.hAdd
                              (instHMul.hMul
                                (instHMul.hMul (LocalDef032 m (instHAdd.hAdd k.val 1))
                                  (instHPow.hPow (LocalDef037 (LocalDef009 family.A k))
                                    2))
                                epsilonM.val)
                              (instHMul.hMul (normalEquationSecondOrderCoeff k) (instHPow.hPow epsilonM.val 2)))) →
                    (∀ (epsilonM : LocalDef006),
                        Real.instLE.le epsilonM.val radius →
                          ∀ (k : Fin n),
                            Real.instLE.le (LocalDef037 (LocalDef009 family.A k))
                              (instHAdd.hAdd
                                (instHMul.hMul
                                  (instHAdd.hAdd 1
                                    (instHMul.hMul (LocalDef033 m (instHAdd.hAdd k.val 1)) epsilonM.val))
                                  (LocalDef012 (LocalDef011 (family.run epsilonM).R k)))
                                (instHMul.hMul (reverseNormSecondOrderCoeff k) (instHPow.hPow epsilonM.val 2)))) →
                      LocalDef007 family
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `43af9658a78bbb6d2e6fda54350c2b96765db5011186d5f604a789cfcbd3348b`

Type:

```lean
{m n : Nat} →
  {family : LocalDef001 m n} → LocalDef007 family → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n family self => self.2
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e1a86dc145731bb2ff528811b89781063bf08e9e1ef1e004fb1038538ce1d074`

Type:

```lean
{m n : Nat} →
  {family : LocalDef001 m n} → LocalDef007 family → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n family self => self.4
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `eaf843c607343eac361393b9a8f05a8fda4b2d5463e0fb4ca50523a00d58e639`

Type:

```lean
{m n : Nat} →
  {family : LocalDef001 m n} → LocalDef007 family → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n family self => self.3
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b7b08e3c7e58aa7c905346648ccb433c270d24b16ce1b39a791f3a8b77c4f09f`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k =>
  ite (Eq k 1) 1
    (instHAdd.hAdd (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 (Real.sqrt 2)) m.cast) k.cast)
      (instHMul.hMul 2 k.cast.sqrt))
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `52067e5a77dcfefcf6fcc3dd88352b7497aba5f0a24254ae20d387e9e2f2faf7`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d798e6a8b8ba59dbcb92ee2cfc3d3d4168700ab660301680a184a00da12fe4b1`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k =>
  ite (Eq k 1) (instHAdd.hAdd m.cast 2)
    (instHAdd.hAdd
      (instHSub.hSub (instHMul.hMul (instHMul.hMul (7 / 2) m.cast) (instHPow.hPow k.cast 2))
        (instHMul.hMul (instHMul.hMul (3 / 2) m.cast) k.cast))
      (instHMul.hMul 16 k.cast))
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c0ecb567dcc422d45ddb50bd71c12eace0cf0bad73f7974c28e5b5fc39325954`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k => instHMul.hMul (1 / 2) (LocalDef032 m k)
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `00a8fef3c8e11f6c84bb5d143a23f246869ac3bd80853c7ec3de93f1add99fda`

Type:

```lean
(n : Nat) → LocalDef023 n
```

Definition body (one-level semantic boundary):

```lean
fun n => 1
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `60564d03e1dd6754e3f768cd633cfa899d84059307025fff5d0e1d2c20189049`

Type:

```lean
∀ {n : Nat} (k : Fin n), instLENat.le k.val.succ n
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `45dbaf27eb1bfa2cd0daa5ab3a20f4c59e27000bb35c7e9ee94b4e37d117677d`

Type:

```lean
{m n p : Nat} → LocalDef024 m n → LocalDef024 n p → LocalDef024 m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1b2d7c2d7e8f4d40657845bb9aa69ad3127ead898c03c302f25c632a978029d0`

Type:

```lean
{m n : Nat} → LocalDef024 m n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6e4fb23abd6b03197c4fe854dbe27e151d6ef4dbe4698963a4bedfa69b00bee2`

Type:

```lean
{m n : Nat} → LocalDef024 m n → LocalDef024 n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => Matrix.transpose A
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7cb0279bb3dac58e4bb3da58311ddb531622c127f1778226875ee9ece32e6ddc`

Type:

```lean
{m n : Nat} → {epsilonM : Real} → LocalDef022 m n epsilonM → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n epsilonM self => self.4
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `750e8de18fcdb932aa1a1c09b0af4bf777402bee218c5bf7cfd3c416da630e36`

Type:

```lean
{m n : Nat} →
  {epsilonM : Real} →
    instLTNat.lt 0 m →
      instLTNat.lt 0 n →
        instLENat.le n m →
          (A Q : LocalDef024 m n) →
            (R : LocalDef023 n) →
              Function.Injective (Matrix.mulVec A) →
                (∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (R i j) 0) →
                  (arithmetic : LocalDef047 epsilonM) →
                    (leadingInverse : (k : Fin n) → LocalDef023 (instHAdd.hAdd k.val 1)) →
                      (∀ (k : Fin n),
                          Eq
                            (LocalDef048 (instHAdd.hAdd k.val 1) (leadingInverse k)
                              (LocalDef011 R k))
                            (LocalDef034 (instHAdd.hAdd k.val 1))) →
                        (∀ (k : Fin n),
                            Eq
                              (LocalDef048 (instHAdd.hAdd k.val 1) (LocalDef011 R k)
                                (leadingInverse k))
                              (LocalDef034 (instHAdd.hAdd k.val 1))) →
                          ((k : Fin n) → LocalDef046 arithmetic A Q R k) →
                            LocalDef022 m n epsilonM
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7c4860c0f215e578204f5411971cf76e3cca164a37651cfc446acaa760c945e4`

Type:

```lean
(instHAdd.hAdd 6 1).AtLeastTwo
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `43da9e2478acfcc10315652cd8017ae5008c9946f416851d0614bcf8778b9474`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `1aa79886ab5282243bf93d3fba3d63ed20aa22eb2ac713e36b95342b25d8a763`

Type:

```lean
(instHAdd.hAdd 15 1).AtLeastTwo
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06dacf14b4a26dd49f7011d96c291c69e6764b535d764a9c3677303af781b31f`

Type:

```lean
{m k : Nat} → LocalDef024 m k → LocalDef023 k → LocalDef023 k
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A R =>
  instHSub.hSub (LocalDef048 k (LocalDef049 R) R)
    (LocalDef036 (LocalDef038 A) A)
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f3d2321eed783f06c71099af291e9a60e245623b9237a634de506133a9c79a13`

Type:

```lean
{m n : Nat} →
  LocalDef001 m n →
    LocalDef006 → (k : Fin n) → LocalDef024 m (instHAdd.hAdd k.val 1)
```

Definition body (one-level semantic boundary):

```lean
fun {m n} family epsilonM k =>
  instHSub.hSub
    (LocalDef036 (LocalDef009 (family.run epsilonM).Q k)
      (LocalDef011 (family.run epsilonM).R k))
    (LocalDef009 family.A k)
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `58676f0c9cf50293bec28232f6d42a3aea963c106083b364c0e052c53ed9ee7a`

Type:

```lean
{epsilonM : Real} →
  {m n : Nat} →
    LocalDef047 epsilonM →
      LocalDef024 m n → LocalDef024 m n → LocalDef023 n → Fin n → Type
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `fa7de182724c676a8b15bbf1fa275f91515545373781a478307542120c523cc0`

Type:

```lean
Real → Type
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5a88abf3460b515aae8930a3c3f8e801fd2d6dc6711b9f813b357ae40f5166b9`

Type:

```lean
(n : Nat) → LocalDef023 n → LocalDef023 n → LocalDef023 n
```

Definition body (one-level semantic boundary):

```lean
fun n A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `df902c1363a2c4d532efa052274ff9934e76027f6f628e6b7d8cbc207418820a`

Type:

```lean
{n : Nat} → LocalDef023 n → LocalDef023 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.transpose A
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `eb9487efe712303ab1e9c1372c5bb4d9fa06316eeedf7080b6b27ee9d7628d10`

Type:

```lean
{epsilonM : Real} →
  {m n : Nat} →
    {arithmetic : LocalDef047 epsilonM} →
      {A Q : LocalDef024 m n} →
        {R : LocalDef023 n} →
          {k : Fin n} →
            (s : Fin n → Real) →
              (v : Fin m → Real) →
                (psi phi : Real) →
                  (∀ (j : Fin n), instLENat.le k.val j.val → Eq (s j) 0) →
                    (Eq k.val 0 → Eq (R k k) (arithmetic.computedNorm fun i => A i k)) →
                      (Eq k.val 0 → ∀ (i : Fin m), arithmetic.normalized (instHDiv.hDiv (A i k) (R k k))) →
                        (Eq k.val 0 → ∀ (i : Fin m), Eq (Q i k) (arithmetic.divide (A i k) (R k k))) →
                          (instLTNat.lt 0 k.val →
                              ∀ (j : Fin n),
                                instLTNat.lt j.val k.val → Eq (s j) (arithmetic.dot (fun i => Q i j) fun i => A i k)) →
                            (instLTNat.lt 0 k.val → ∀ (j : Fin n), instLTNat.lt j.val k.val → Eq (R j k) (s j)) →
                              (instLTNat.lt 0 k.val →
                                  ∀ (i : Fin m),
                                    Eq (v i)
                                      (arithmetic.subtract (A i k)
                                        (arithmetic.dot (fun j => Q i j) (LocalDef062 k s)))) →
                                (instLTNat.lt 0 k.val → Eq psi (arithmetic.computedNorm fun i => A i k)) →
                                  (instLTNat.lt 0 k.val →
                                      Eq phi (arithmetic.computedNorm (LocalDef062 k s))) →
                                    (instLTNat.lt 0 k.val → Real.instLE.le 0 (arithmetic.subtract psi phi)) →
                                      (instLTNat.lt 0 k.val →
                                          Eq (R k k)
                                            (arithmetic.multiply (arithmetic.squareRoot (arithmetic.subtract psi phi))
                                              (arithmetic.squareRoot (arithmetic.add psi phi)))) →
                                        (instLTNat.lt 0 k.val →
                                            ∀ (i : Fin m), arithmetic.normalized (instHDiv.hDiv (v i) (R k k))) →
                                          (instLTNat.lt 0 k.val →
                                              ∀ (i : Fin m), Eq (Q i k) (arithmetic.divide (v i) (R k k))) →
                                            Real.instLT.lt 0 (R k k) → LocalDef046 arithmetic A Q R k
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `e2e1c0f2f274198e5ea069cf5578987b835cc08927303c3e9bfc4cd1d27b5dfe`

Type:

```lean
{epsilonM : Real} →
  (toP11NormalizedIEEEArithmetic : LocalDef058 epsilonM) →
    (add subtract multiply : Real → Real → Real) →
      (squareRoot : Real → Real) →
        (dot : {dimension : Nat} → (Fin dimension → Real) → (Fin dimension → Real) → Real) →
          (∀ (x y : Real),
              toP11NormalizedIEEEArithmetic.normalized (instHAdd.hAdd x y) →
                Exists fun delta =>
                  And (Real.instLE.le (abs delta) epsilonM)
                    (Eq (add x y) (instHMul.hMul (instHAdd.hAdd x y) (instHAdd.hAdd 1 delta)))) →
            (∀ (x y : Real),
                toP11NormalizedIEEEArithmetic.normalized (instHSub.hSub x y) →
                  Exists fun delta =>
                    And (Real.instLE.le (abs delta) epsilonM)
                      (Eq (subtract x y) (instHMul.hMul (instHSub.hSub x y) (instHAdd.hAdd 1 delta)))) →
              (∀ (x y : Real),
                  toP11NormalizedIEEEArithmetic.normalized (instHMul.hMul x y) →
                    Exists fun delta =>
                      And (Real.instLE.le (abs delta) epsilonM)
                        (Eq (multiply x y) (instHMul.hMul (instHMul.hMul x y) (instHAdd.hAdd 1 delta)))) →
                (∀ (x : Real),
                    Real.instLE.le 0 x →
                      toP11NormalizedIEEEArithmetic.normalized x.sqrt →
                        Exists fun delta =>
                          And (Real.instLE.le (abs delta) epsilonM)
                            (Eq (squareRoot x) (instHMul.hMul x.sqrt (instHAdd.hAdd 1 delta)))) →
                  (∀ {dimension : Nat} (x y : Fin dimension → Real),
                      Exists fun theta =>
                        And
                          (∀ (i : Fin dimension),
                            Real.instLE.le (abs (theta i)) (instHMul.hMul dimension.cast epsilonM))
                          (Eq (dot x y)
                            (Finset.univ.sum fun i =>
                              instHMul.hMul (instHMul.hMul (x i) (y i)) (instHAdd.hAdd 1 (theta i))))) →
                    LocalDef047 epsilonM
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `4a1e2d74a39db77a1961715b59d980942a267249e8f02a4a434ca1c96e842578`

Type:

```lean
{epsilonM : Real} → LocalDef047 epsilonM → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.2
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `70f78fc5e866d515cba415ee3b7847987756205a374158486e75b2d88738d3e3`

Type:

```lean
{epsilonM : Real} →
  LocalDef047 epsilonM →
    {dimension : Nat} → (Fin dimension → Real) → (Fin dimension → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.6
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `c596c728f2aa0d0809966a9a6548a6e7cf814cd755d509e992914ff7b2c1f25c`

Type:

```lean
{epsilonM : Real} → LocalDef047 epsilonM → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.4
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `900317dbc6212a82bee8526922244be6eccab78470260efb3edeae2e5e0ae78f`

Type:

```lean
{epsilonM : Real} → LocalDef047 epsilonM → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.5
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `8afee97006bfef7f3b3c410ac5f333fa91501a29eb310c316d8f09fa8b90a6e3`

Type:

```lean
{epsilonM : Real} → LocalDef047 epsilonM → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.3
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `bf9f41a7af0d79905cbe82392f0173c43a0705dcbd45ac1262007e2f8d3303e5`

Type:

```lean
{epsilonM : Real} → LocalDef047 epsilonM → LocalDef058 epsilonM
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.1
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `6bfad9707eb1614f58f51f173591081213b3485b488338c640574d543a7d283b`

Type:

```lean
Real → Type
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `6d4c2b8ece9829f777600a0141f4ff86469cb652ac589ae795d9f9a683733ac8`

Type:

```lean
{epsilonM : Real} → LocalDef058 epsilonM → {m : Nat} → (Fin m → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.3
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `8294149a85ea5526102d1089e6d57f13d9039c7d58f22d287ef5a04664f622b0`

Type:

```lean
{epsilonM : Real} → LocalDef058 epsilonM → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.2
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `1b985c4542821baacd7f3343c0070ee8b7d1666027c272ae12ca85cb6bfa5cba`

Type:

```lean
{epsilonM : Real} → LocalDef058 epsilonM → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun epsilonM self => self.1
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `6796d402d487f33a7b0f0afafe89d1b692a281e2162a117226a2872b745b1fda`

Type:

```lean
{n : Nat} → Fin n → (Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} k x j => ite (instLTNat.lt j.val k.val) (x j) 0
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `919e72580f3e6ea95642d1e3ec0ba90b82c79d9fba71c29d9bc8ff790f1fcbf2`

Type:

```lean
{epsilonM : Real} →
  (normalized : Real → Prop) →
    (divide : Real → Real → Real) →
      (computedNorm : {m : Nat} → (Fin m → Real) → Real) →
        (normSecondOrderCoeff : Nat → Real) →
          (∀ (m : Nat), Real.instLE.le 0 (normSecondOrderCoeff m)) →
            (∀ {m : Nat} (a : Fin m → Real),
                Exists fun delta =>
                  And (Eq (computedNorm a) (instHMul.hMul (LocalDef064 a) (instHAdd.hAdd 1 delta)))
                    (Real.instLE.le (abs delta)
                      (instHAdd.hAdd (instHMul.hMul (instHAdd.hAdd (instHMul.hMul (1 / 2) m.cast) 1) epsilonM)
                        (instHMul.hMul (normSecondOrderCoeff m) (instHPow.hPow epsilonM 2))))) →
              (∀ {m : Nat} (a : Fin m → Real), Real.instLE.le 0 (computedNorm a)) →
                (∀ (x denominator : Real),
                    Ne denominator 0 →
                      normalized (instHDiv.hDiv x denominator) →
                        Exists fun delta =>
                          And (Real.instLE.le (abs delta) epsilonM)
                            (Eq (divide x denominator)
                              (instHMul.hMul (instHDiv.hDiv x denominator) (instHAdd.hAdd 1 delta)))) →
                  LocalDef058 epsilonM
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `ee71eed419dd20d9388ea70276d8f8cce111468786138bd0438db1313846d0c6`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D065: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D066: `Fin.val`

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

### D067: `HAdd.hAdd`

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

### D068: `HMul.hMul`

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

### D069: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D070: `LE.le`

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

### D071: `LT.lt`

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

### D072: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D073: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D074: `OfNat.ofNat`

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

### D075: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D076: `Real.instAdd`

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

### D077: `Real.instLE`

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

### D078: `Real.instLT`

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

### D079: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D080: `Real.instMul`

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

### D081: `Real.instZero`

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

### D082: `Subtype.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `69c61ab82498e5563eaf5f0313ea7f2164c284c3dc742024a30332372a46663d`

Type:

```lean
{α : Sort u} → {p : α → Prop} → Subtype p → α
```

Definition body (one-level semantic boundary):

```lean
fun α p self => self.1
```

### D083: `Zero.toOfNat0`

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

### D084: `instAddNat`

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

### D085: `instHAdd`

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

### D086: `instHMul`

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

### D087: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D088: `instOfNatNat`

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

### D089: `Fin.castLE`

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

### D090: `Fin.fintype`

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

### D091: `HSub.hSub`

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

### D092: `Matrix`

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

### D093: `Matrix.instL2OpNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.CStarAlgebra.Matrix`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dc6ff9e1f662ed3b176ef586f3e0ff253c161538742e908216485822af6e00c3`

Type:

```lean
{𝕜 : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} → [RCLike 𝕜] → [Fintype m] → [Fintype n] → [DecidableEq n] → NormedAddCommGroup (Matrix m n 𝕜)
```

Definition body (one-level semantic boundary):

```lean
fun {𝕜} {m} {n} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n] =>
  { toNorm := Matrix.l2OpNormedAddCommGroupAux.toNorm, toAddCommGroup := Matrix.addCommGroup,
    toMetricSpace := Matrix.instL2OpMetricSpace, dist_eq := ⋯ }
```

### D094: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f9a0c1f5b41c8d9a8658798c73b295495f6dfbf0bd7d081817aec4f598bbfc46`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub α] → Sub (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Sub α] => Pi.instSub
```

### D095: `Min.min`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4781b8f14117c86f8d250ccd7a9bf20c2b8b6554a48ba0b45f9010ff26a72ea7`

Type:

```lean
{α : Type u} → [self : Min α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Min α] => self.1
```

### D096: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D097: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D098: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D099: `One.toOfNat1`

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

### D100: `Real.instMin`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d2cd90660c09f0530ecb3d8bd97eb9c8e1ed4fc9eebe2650e6a65a653c99fcb0`

Type:

```lean
Min Real
```

Definition body (one-level semantic boundary):

```lean
{ min := Real.inf✝ }
```

### D101: `Real.instNatCast`

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

### D102: `Real.instOne`

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

### D103: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D104: `Real.instSub`

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

### D105: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

### D106: `instDecidableEqFin`

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

### D107: `instHSub`

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

### D108: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D109: `DivInvMonoid.toDiv`

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

### D110: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D111: `HDiv.hDiv`

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

### D112: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D113: `Matrix.one`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b68e4dde96dc7da148aa68eb622604137a0c2dec462b5c39bdd02d8b07d2a59d`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → [One α] → One (Matrix n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] [One α] => { one := Matrix.diagonal fun x => 1 }
```

### D114: `Matrix.transpose`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a0ee2c3649fa412f4b56ce3f375ef2f2d84b6b21507e1c4a93e90d3b9562973e`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Matrix m n α → Matrix n m α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} M => EquivLike.toFunLike.coe Matrix.of fun x y => M y x
```

### D115: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D116: `Nat.cast`

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

### D117: `Real.instAddCommMonoid`

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

### D118: `Real.instDivInvMonoid`

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

### D119: `Real.sqrt`

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

### D120: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

Type:

```lean
DecidableEq Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D121: `instHDiv`

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

### D122: `instLENat`

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

### D123: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D124: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```

### D125: `Matrix.mulVec`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `715de3f0bd9e7bcf034726e1efbf1b4dad42a16e2ce790d4403774d16ed5b549`

Type:

```lean
{m : Type u_2} →
  {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemiring α] → [Fintype n] → Matrix m n α → (n → α) → m → α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [NonUnitalNonAssocSemiring α] [Fintype n] M v x =>
  have i := x;
  dotProduct (fun j => M i j) v
```

### D126: `NonUnitalCommRing.toNonUnitalNonAssocCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `3bd70454a5180abed6221bb3f73922ebc30c10136298d23eb30d358cdd2fdb82`

Type:

```lean
{α : Type u} → [self : NonUnitalCommRing α] → NonUnitalNonAssocCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalNonAssocRing := self.toNonUnitalNonAssocRing, mul_comm := ⋯ }
```

### D127: `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `1082112ee2b1424cb7e1eff69df85640d23793811157d8a4401f364710bc21d2`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing α] → NonUnitalNonAssocRing α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocCommRing α] => self.1
```

### D128: `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ffc3b0b49d777bb976662d9282026e03ef869205e45f90008bd1659a4e78f2d7`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocRing α] → NonUnitalNonAssocSemiring α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toAddMonoid := self.toAddMonoid, add_comm := ⋯, toMul := self.toMul, left_distrib := ⋯, right_distrib := ⋯,
    zero_mul := ⋯, mul_zero := ⋯ }
```

### D129: `NonUnitalNormedCommRing.toNonUnitalCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `4a44c0a0630b1766c12bb0c5456f4f914c813b6dcb179e8b3d87084d495efd1f`

Type:

```lean
{α : Type u_5} → [self : NonUnitalNormedCommRing α] → NonUnitalCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalRing := self.toNonUnitalRing, mul_comm := ⋯ }
```

### D130: `NormedCommRing.toNonUnitalNormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ce5ba4f454145f64923f4d555eb95891cb66dc2df21d2ef730bfa600ea6a22e5`

Type:

```lean
{α : Type u_2} → [β : NormedCommRing α] → NonUnitalNormedCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : NormedCommRing α] =>
  { toNorm := β.toNorm, toAddMonoid := β.toAddMonoid, toNeg := β.toNeg, toSub := β.toSub, sub_eq_add_neg := ⋯,
    zsmul := β.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯,
    toMul := β.toMul, left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    toMetricSpace := β.toMetricSpace, dist_eq := ⋯, norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D131: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D132: `instLTNat`

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

### D133: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D134: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D135: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D136: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D137: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D138: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D139: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D140: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
```

### D141: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `8`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D142: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `8`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D143: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```
