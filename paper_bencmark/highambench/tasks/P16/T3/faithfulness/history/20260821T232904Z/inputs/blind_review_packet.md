# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (run : LocalDef001 l),
  LocalDef013 l (LocalDef011 run) →
    And
      (∀ (i : Nat),
        LocalDef008 l (LocalDef012 run)
          (fun t => LocalDef006 run.A run.b (run.xHat (instHAdd.hAdd i 1) t)) fun t =>
          instHAdd.hAdd
            (instHMul.hMul (LocalDef011 run t)
              (LocalDef006 run.A run.b (run.xHat i t)))
            (LocalDef007 run t))
      (∀ (i : Nat),
        LocalDef008 l (LocalDef012 run)
          (fun t => LocalDef009 run.xExact (run.xHat (instHAdd.hAdd i 1) t)) fun t =>
          instHAdd.hAdd
            (instHMul.hMul (LocalDef011 run t)
              (LocalDef009 run.xExact (run.xHat i t)))
            (LocalDef010 run t))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (run : @LocalDef001.{u_1} n ι l)
  (hLambda : @LocalDef013.{u_1} ι l (@LocalDef011.{u_1} n ι l run)),
  And
    (∀ (i : Nat),
      @LocalDef008.{u_1} ι l (@LocalDef012.{u_1} n ι l run)
        (fun (t : ι) =>
          @LocalDef006 n (@LocalDef002.{u_1} n ι l run)
            (@LocalDef003.{u_1} n ι l run)
            (@LocalDef005.{u_1} n ι l run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t))
        fun (t : ι) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@LocalDef011.{u_1} n ι l run t)
            (@LocalDef006 n (@LocalDef002.{u_1} n ι l run)
              (@LocalDef003.{u_1} n ι l run)
              (@LocalDef005.{u_1} n ι l run i t)))
          (@LocalDef007.{u_1} n ι l run t))
    (∀ (i : Nat),
      @LocalDef008.{u_1} ι l (@LocalDef012.{u_1} n ι l run)
        (fun (t : ι) =>
          @LocalDef009 n (@LocalDef004.{u_1} n ι l run)
            (@LocalDef005.{u_1} n ι l run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t))
        fun (t : ι) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@LocalDef011.{u_1} n ι l run t)
            (@LocalDef009 n (@LocalDef004.{u_1} n ι l run)
              (@LocalDef005.{u_1} n ι l run i t)))
          (@LocalDef010.{u_1} n ι l run t))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `51458db0c51de2a96234380865d7469752042444011e63ace5bdf3c17f32d9b6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e28b6875676e8c359449b7668ee15841cc9217b6d7aa2aa89366e84c7f084b2b`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → LocalDef014 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ae1e650774899a6ecd2d298fd6fa794cef6f1a7c999865bd394783ae8b14263f`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → LocalDef020 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.4
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e41083c321cb651d26a8bb2b9ca8a11ac8b5d2c3fc2cb48821271a48185307e6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → LocalDef020 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.5
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1f967da311d03daf58abaca30d28927dfff89a9bdb8380a8194642062c68e885`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → Nat → ι → LocalDef020 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.6
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f393da23f12434756d498c11e9e2ae4d991fc118a94873a36622b66697bd62ec`

Type:

```lean
{n : Nat} → LocalDef014 n → LocalDef020 n → LocalDef020 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat => LocalDef022 A b xHat
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1dd328aa23f56f00539a1a671c1678b407df7d8674c99cfd90b802e239733cc6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t => instHMul.hMul (LocalDef023 run.polynomialFactor n n) (run.uHigh t)
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f8fb89f45dff8ea408faebbf7940e52c3a8135ec7c9fa4489c8e3a8540da3a7b`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (LocalDef024 l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ae31da5e50aa0dd2d17a75257cdee20c66bc769f6b0c93726fb999724b14518`

Type:

```lean
{n : Nat} → LocalDef020 n → LocalDef020 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (LocalDef025 (instHSub.hSub xHat x)) (LocalDef025 x)
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `07175b6eeecdc25ff174e86e12050da2978093bef10bace3dedfda70c0cd784c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHMul.hMul (instHMul.hMul (LocalDef023 run.polynomialFactor n n) (run.uHigh t))
    (LocalDef021 run.A run.Ainv)
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5c7c6465ffab9f805655532e5a5e83bf1d168c08e878480078fcd2231bc1612e`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHMul.hMul (instHMul.hMul (LocalDef023 run.polynomialFactor n n) (run.uLow t))
    (LocalDef021 run.A run.Ainv)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `708175afe78342782c0fbd8b99965642cc8024089ae16c33ecc907c016c35eb9`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t => instHAdd.hAdd (run.uHigh t) (run.uLow t)
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe11d8a7495ed132c0b3333870c07122ca62d29111e5137f4d42ebb136cb2426`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l lambda =>
  And (Filter.Tendsto lambda l (nhds 0))
    (Filter.Eventually (fun t => And (Real.instLE.le 0 (lambda t)) (Real.instLT.lt (lambda t) 1)) l)
```

### D014: `LocalDef014`

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

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `270eda0230af7580e6c1ae66307da68ad740caeb9f4491043cdfacc50e84490c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → LocalDef014 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.3
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2d46d32f1d8eb2ec8801d0d21371249e7112ad81d62c1f331dc43292124ddec6`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      instLTNat.lt 0 n →
        (A Ainv : LocalDef014 n) →
          (b xExact : LocalDef020 n) →
            (xHat residualHat correctionHat residualError updateError : Nat → ι → LocalDef020 n) →
              (uHigh uLow : ι → Real) →
                (polynomialFactor : LocalDef028) →
                  Ne b 0 →
                    LocalDef034 A →
                      (∀ (z : LocalDef020 n), Eq (LocalDef035 Ainv (LocalDef035 A z)) z) →
                        (∀ (z : LocalDef020 n),
                            Eq (LocalDef035 A (LocalDef035 Ainv z)) z) →
                          Eq (LocalDef035 A xExact) b →
                            (∀ (t : ι), Real.instLE.le 0 (uHigh t)) →
                              (∀ (t : ι), Real.instLE.le 0 (uLow t)) →
                                (∀ (t : ι), Real.instLE.le (uHigh t) (uLow t)) →
                                  Filter.Tendsto uHigh l (nhds 0) →
                                    Filter.Tendsto uLow l (nhds 0) →
                                      (∀ (t : ι), LocalDef026 (uHigh t) n) →
                                        (∀ (i : Nat) (t : ι),
                                            Eq (residualHat i t)
                                              (instHAdd.hAdd (LocalDef036 A b (xHat i t))
                                                (residualError i t))) →
                                          (∀ (i : Nat) (t : ι) (j : Fin n),
                                              Real.instLE.le (abs (residualError i t j))
                                                (instHMul.hMul (LocalDef032 (uHigh t) n)
                                                  (instHAdd.hAdd (abs (b j))
                                                    (LocalDef035 (fun row col => abs (A row col))
                                                      (fun col => abs (xHat i t col)) j)))) →
                                            (∀ (i : Nat) (t : ι),
                                                Eq (xHat (instHAdd.hAdd i 1) t)
                                                  (instHAdd.hAdd (instHAdd.hAdd (xHat i t) (correctionHat i t))
                                                    (updateError i t))) →
                                              (∀ (i : Nat) (t : ι) (j : Fin n),
                                                  Real.instLE.le (abs (updateError i t j))
                                                    (instHMul.hMul (uHigh t) (abs (xHat (instHAdd.hAdd i 1) t j)))) →
                                                ((i : Nat) →
                                                    LocalDef027 l
                                                      (fun t => instHAdd.hAdd (uHigh t) (uLow t)) A Ainv b xExact
                                                      (xHat i) (xHat (instHAdd.hAdd i 1)) (residualHat i)
                                                      (correctionHat i) uLow polynomialFactor) →
                                                  (∀ (i : Nat),
                                                      LocalDef008 l
                                                        (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                        (fun t => LocalDef025 (xHat i t)) fun t =>
                                                        LocalDef025 (xHat (instHAdd.hAdd i 1) t)) →
                                                    (∀ (i : Nat),
                                                        LocalDef008 l
                                                          (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                          (fun t => LocalDef025 (xHat (instHAdd.hAdd i 1) t))
                                                          fun x => LocalDef025 xExact) →
                                                      (∀ (i : Nat),
                                                          LocalDef008 l
                                                            (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                            (fun t =>
                                                              instHDiv.hDiv
                                                                (instHAdd.hAdd
                                                                  (LocalDef025 (residualError i t))
                                                                  (LocalDef025
                                                                    (LocalDef035 A (updateError i t))))
                                                                (instHAdd.hAdd (LocalDef025 b)
                                                                  (instHMul.hMul (LocalDef033 A)
                                                                    (LocalDef025
                                                                      (xHat (instHAdd.hAdd i 1) t)))))
                                                            fun t =>
                                                            instHMul.hMul
                                                              (LocalDef023 polynomialFactor n
                                                                n)
                                                              (uHigh t)) →
                                                        (∀ (i : Nat),
                                                            LocalDef008 l
                                                              (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                              (fun t =>
                                                                instHDiv.hDiv (LocalDef025 (updateError i t))
                                                                  (LocalDef025 xExact))
                                                              fun t =>
                                                              instHMul.hMul
                                                                (instHMul.hMul
                                                                  (LocalDef023 polynomialFactor
                                                                    n n)
                                                                  (uHigh t))
                                                                (LocalDef021 A Ainv)) →
                                                          LocalDef001 l
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1007f4b6a0c6e4705c1a6856afa04909a8cc859086d0998eecd0b8b7a11e1e01`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → LocalDef028
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.13
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c918ae2d5722eb61527ca7f064fa91fff18127862bf1947e1f1ea4e3605cd3d8`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.11
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `050a7c54f7eb4705624e61e49e6219a91055717d6df8b41a725aab429fb1d485`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef001 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.12
```

### D020: `LocalDef020`

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

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aad128e1ff242bef74849f83be7b08fd1b3bf6883dc807497f55a0fff18e7456`

Type:

```lean
{n : Nat} → LocalDef014 n → LocalDef014 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef033 Ainv) (LocalDef033 A)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fcb08c14cdc1ff672554092cd5e6a93c5458a19a318e4c8f88e0e1ba2906b439`

Type:

```lean
{n : Nat} → LocalDef014 n → LocalDef020 n → LocalDef020 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat =>
  instHDiv.hDiv (LocalDef025 (LocalDef036 A b xHat))
    (instHAdd.hAdd (instHMul.hMul (LocalDef033 A) (LocalDef025 xHat)) (LocalDef025 b))
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `760fbb54d1bbc51a3cb9ef42d3d96bd053f7f673cb6af6cf627e47cd48d589c8`

Type:

```lean
LocalDef028 → Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun c n k =>
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      instHMul.hMul (instHMul.hMul (c.coefficient i j) (instHPow.hPow n.cast i.val)) (instHPow.hPow k.cast j.val)
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9f8f2149f6244d786fa2d0abae769fb5885e4da9a6f980dcd98dfdedc9dfea99`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `bd8e44de2b8f8d577e4ee9f3b2ffb202461eebd6324f041a2f505422a111cd66`

Type:

```lean
{n : Nat} → LocalDef020 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D026: `LocalDef026`

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

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `e45857733ce3798f3d60a8367e1ac10498ff41b2fa8efcd1445a0e775b8a30c9`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    Filter ι →
      (ι → Real) →
        LocalDef014 n →
          LocalDef014 n →
            LocalDef020 n →
              LocalDef020 n →
                (ι → LocalDef020 n) →
                  (ι → LocalDef020 n) →
                    (ι → LocalDef020 n) →
                      (ι → LocalDef020 n) → (ι → Real) → LocalDef028 → Type u_1
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `0433df59d966012b968702b4ffc0dcd8fdc1b3177eecb14ee31bad2fde29f36b`

Type:

```lean
Type
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `eda434f64be08a0d479423cd695893c35f43716004402939d12da0a364fa58e8`

Type:

```lean
(self : LocalDef028) →
  Fin (instHAdd.hAdd self.degreeN 1) → Fin (instHAdd.hAdd self.degreeK 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `df1d28debd8bd57641958e5b2f067565cdd35a656575ec77fff53a44cad5cf95`

Type:

```lean
LocalDef028 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7535abaa99860d41d600e1a9051ecb7967df3e56b9a83219b1c10ca2f6988dea`

Type:

```lean
LocalDef028 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D032: `LocalDef032`

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

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`

Type:

```lean
{n : Nat} → LocalDef014 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.frobeniusNormedRing.norm A
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `85b5f4df299401a78ff2042ddbaff615a4f2e4dd7ac6d5eeddc8091ccb86d714`

Type:

```lean
{n : Nat} → LocalDef014 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Function.Bijective (LocalDef035 A)
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `633fcb3583fab70e7665e594e28a11707a692d4c14a396ea9eeda2a3724f56b9`

Type:

```lean
{n : Nat} → LocalDef014 n → LocalDef020 n → LocalDef020 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b6efd2406b4d95a62ec33a870000fff88d929437b9b4152b36fbbe02063a3602`

Type:

```lean
{n : Nat} → LocalDef014 n → LocalDef020 n → LocalDef020 n → LocalDef020 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b x => instHSub.hSub b (LocalDef035 A x)
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `afe19ef6b610bd6de95ce6e9366187dc63c2d4914b7abf30c63e852f0f1f3000`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A Ainv : LocalDef014 n} →
          {b xExact : LocalDef020 n} →
            {xCurrent xNext residualHat correctionHat : ι → LocalDef020 n} →
              {uLow : ι → Real} →
                {poly : LocalDef028} →
                  (keyDimension : Nat) →
                    instLTNat.lt 0 keyDimension →
                      instLENat.le keyDimension n →
                        (basis : ι → LocalDef039 n keyDimension) →
                          (basisNext : ι → LocalDef039 n (instHAdd.hAdd keyDimension 1)) →
                            (hessenberg : ι → LocalDef039 (instHAdd.hAdd keyDimension 1) keyDimension) →
                              (arnoldiError : ι → LocalDef039 n keyDimension) →
                                (∀ (t : ι),
                                    Eq (LocalDef047 A (basis t))
                                      (instHAdd.hAdd (LocalDef045 (basisNext t) (hessenberg t))
                                        (arnoldiError t))) →
                                  (residualLow residualCastError : ι → LocalDef020 n) →
                                    (∀ (t : ι),
                                        Eq (residualLow t) (instHAdd.hAdd (residualHat t) (residualCastError t))) →
                                      (∀ (t : ι),
                                          Real.instLE.le (LocalDef025 (residualCastError t))
                                            (instHMul.hMul (uLow t) (LocalDef025 (residualHat t)))) →
                                        (arnoldiProduct arnoldiProductError :
                                            ι → LocalDef039 n keyDimension) →
                                          (∀ (t : ι),
                                              Eq (arnoldiProduct t)
                                                (instHAdd.hAdd (LocalDef047 A (basis t))
                                                  (arnoldiProductError t))) →
                                            (epsilonC epsilonB epsilonLS epsilonX : ι → Real) →
                                              (∀ (t : ι),
                                                  Real.instLE.le (LocalDef044 (arnoldiProductError t))
                                                    (instHMul.hMul (epsilonC t)
                                                      (LocalDef044
                                                        (LocalDef047 A (basis t))))) →
                                                (leastSquaresRhsError : ι → LocalDef020 n) →
                                                  (leastSquaresMatrixError :
                                                      ι → LocalDef039 n keyDimension) →
                                                    (leastSquaresY : ι → LocalDef020 keyDimension) →
                                                      (∀ (t : ι),
                                                          LocalDef041
                                                            (instHAdd.hAdd (arnoldiProduct t)
                                                              (leastSquaresMatrixError t))
                                                            (instHAdd.hAdd (residualLow t) (leastSquaresRhsError t))
                                                            (leastSquaresY t)) →
                                                        (∀ (t : ι),
                                                            Real.instLE.le
                                                              (LocalDef025 (leastSquaresRhsError t))
                                                              (instHMul.hMul (epsilonLS t)
                                                                (LocalDef025 (residualLow t)))) →
                                                          (∀ (t : ι),
                                                              Real.instLE.le
                                                                (LocalDef044
                                                                  (leastSquaresMatrixError t))
                                                                (instHMul.hMul (epsilonLS t)
                                                                  (LocalDef044 (arnoldiProduct t)))) →
                                                            (correctionFormationError : ι → LocalDef020 n) →
                                                              (∀ (t : ι),
                                                                  Eq (correctionHat t)
                                                                    (instHAdd.hAdd
                                                                      (LocalDef046 (basis t)
                                                                        (leastSquaresY t))
                                                                      (correctionFormationError t))) →
                                                                (∀ (t : ι),
                                                                    Real.instLE.le
                                                                      (LocalDef025
                                                                        (correctionFormationError t))
                                                                      (instHMul.hMul
                                                                        (instHMul.hMul (epsilonX t)
                                                                          (LocalDef044 (basis t)))
                                                                        (LocalDef025 (leastSquaresY t)))) →
                                                                  (∀ (t : ι),
                                                                      And (Real.instLE.le 0 (epsilonC t))
                                                                        (And (Real.instLE.le 0 (epsilonB t))
                                                                          (And (Real.instLE.le 0 (epsilonLS t))
                                                                            (Real.instLE.le 0 (epsilonX t))))) →
                                                                    And (Filter.Tendsto epsilonC l (nhds 0))
                                                                        (And (Filter.Tendsto epsilonB l (nhds 0))
                                                                          (And (Filter.Tendsto epsilonLS l (nhds 0))
                                                                            (Filter.Tendsto epsilonX l (nhds 0)))) →
                                                                      (basisLowerGain imageLowerGain : ι → Real) →
                                                                        (∀ (t : ι),
                                                                            LocalDef042 (basis t)
                                                                              (basisLowerGain t)) →
                                                                          (∀ (t : ι),
                                                                              LocalDef042
                                                                                (LocalDef047 A
                                                                                  (basis t))
                                                                                (imageLowerGain t)) →
                                                                            (∀ (t : ι),
                                                                                Real.instLT.lt
                                                                                  (instHMul.hMul (epsilonX t)
                                                                                    (LocalDef044
                                                                                      (basis t)))
                                                                                  (basisLowerGain t)) →
                                                                              (instLTNat.lt keyDimension n →
                                                                                  ∀ (t : ι) (phi : Real),
                                                                                    Real.instLT.lt 0 phi →
                                                                                      LocalDef043
                                                                                        (LocalDef040
                                                                                          (residualLow t) phi
                                                                                          (arnoldiProduct t))
                                                                                        (instHMul.hMul
                                                                                          (instHMul.hMul
                                                                                            (LocalDef023
                                                                                              poly n keyDimension)
                                                                                            (instHAdd.hAdd
                                                                                              (instHAdd.hAdd
                                                                                                (epsilonC t)
                                                                                                (epsilonB t))
                                                                                              (epsilonLS t)))
                                                                                          (LocalDef044
                                                                                            (LocalDef040
                                                                                              (residualLow t) phi
                                                                                              (arnoldiProduct t))))) →
                                                                                (∀ (t : ι),
                                                                                    Real.instLT.lt
                                                                                      (instHMul.hMul
                                                                                        (instHAdd.hAdd
                                                                                          (instHAdd.hAdd (epsilonC t)
                                                                                            (epsilonB t))
                                                                                          (epsilonLS t))
                                                                                        (LocalDef044
                                                                                          (arnoldiProduct t)))
                                                                                      (imageLowerGain t)) →
                                                                                  (localFactor : Real) →
                                                                                    Real.instLE.le 0 localFactor →
                                                                                      Real.instLE.le localFactor
                                                                                          (LocalDef023
                                                                                            poly n keyDimension) →
                                                                                        Real.instLE.le
                                                                                            (LocalDef023
                                                                                              poly n keyDimension)
                                                                                            (LocalDef023
                                                                                              poly n n) →
                                                                                          (backwardFactor
                                                                                              forwardFactor :
                                                                                              ι → Real) →
                                                                                            (∀ (t : ι),
                                                                                                And
                                                                                                  (Real.instLE.le 0
                                                                                                    (backwardFactor t))
                                                                                                  (Real.instLE.le 0
                                                                                                    (forwardFactor
                                                                                                      t))) →
                                                                                              (∀ (t : ι),
                                                                                                  Real.instLE.le
                                                                                                    (backwardFactor t)
                                                                                                    (instHMul.hMul
                                                                                                      (instHMul.hMul
                                                                                                        localFactor
                                                                                                        (uLow t))
                                                                                                      (LocalDef021
                                                                                                        A Ainv))) →
                                                                                                (∀ (t : ι),
                                                                                                    Real.instLE.le
                                                                                                      (forwardFactor t)
                                                                                                      (instHMul.hMul
                                                                                                        (instHMul.hMul
                                                                                                          localFactor
                                                                                                          (uLow t))
                                                                                                        (LocalDef021
                                                                                                          A Ainv))) →
                                                                                                  (LocalDef008
                                                                                                      l scale ⋯ fun t =>
                                                                                                      instHMul.hMul
                                                                                                        (backwardFactor
                                                                                                          t)
                                                                                                        (LocalDef006
                                                                                                          A b
                                                                                                          (xCurrent
                                                                                                            t))) →
                                                                                                    ⋯ → ⋯
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `a8c6eea74c2a2a0885d42f9c23e54ef3821e761dedc0f21c6e669d08797687ae`

Type:

```lean
(degreeN degreeK : Nat) →
  (coefficient : Fin (instHAdd.hAdd degreeN 1) → Fin (instHAdd.hAdd degreeK 1) → Real) →
    (∀ (i : Fin (instHAdd.hAdd degreeN 1)) (j : Fin (instHAdd.hAdd degreeK 1)), Real.instLE.le 0 (coefficient i j)) →
      LocalDef028
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ed6ed4c3dc41190752faa97194bb8058e9dd7deadfbd18631c282a8f04103d81`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b8a20ccd1a0141e32676a45d1777c354b7c37d97677afb2234a664e7158d3cea`

Type:

```lean
{n k : Nat} →
  LocalDef020 n → Real → LocalDef039 n k → LocalDef039 n (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b phi C i i_1 => Fin.cases (instHMul.hMul (b i) phi) (fun j => C i j) i_1
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `bdfc265c3df9de57c6f0acfa56fa518d59187a9636cb68597f1faf194c63a797`

Type:

```lean
{m k : Nat} → LocalDef039 m k → LocalDef020 m → LocalDef020 k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : LocalDef020 k),
    Real.instLE.le (LocalDef025 (instHSub.hSub b (LocalDef046 A y)))
      (LocalDef025 (instHSub.hSub b (LocalDef046 A z)))
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `aea1bd8a88cb85c24aad7b9fbf82abc6098fc02caa123478bbd558b3d3759768`

Type:

```lean
{m k : Nat} → LocalDef039 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigma =>
  ∀ (x : LocalDef020 k),
    Real.instLE.le (instHMul.hMul sigma (LocalDef025 x))
      (LocalDef025 (LocalDef046 A x))
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `552e2d22c81360084216ba06ab4ea330e4c6339472649bada4698b2510af7ab9`

Type:

```lean
{m k : Nat} → LocalDef039 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A delta =>
  Exists fun x =>
    And (Eq (LocalDef025 x) 1)
      (Real.instLE.le (LocalDef025 (LocalDef046 A x)) delta)
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a2ed232b7b5960b8a6f9c5907344e0b80314d5f88f6285f45b4409ed2a6d7203`

Type:

```lean
{m k : Nat} → LocalDef039 m k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `4c41f6ed6f135d516ff29af2935748dc7ecc22eba1d40003bd16ecd29aa82ef9`

Type:

```lean
{m k q : Nat} → LocalDef039 m k → LocalDef039 k q → LocalDef039 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6f698af222e83d101b281cbccf24e989a885c3a996fa1b73f33092817b45db0c`

Type:

```lean
{m k : Nat} → LocalDef039 m k → LocalDef020 k → LocalDef020 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `0053caf146fae0af9f54e65099d1a3e27476c2f20502180d10ba739f1bc05026`

Type:

```lean
{n k : Nat} → LocalDef014 n → LocalDef039 n k → LocalDef039 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
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

### D049: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

### D050: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

### D051: `HAdd.hAdd`

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

### D052: `HMul.hMul`

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

### D053: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D054: `OfNat.ofNat`

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

### D055: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D056: `Real.instAdd`

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

### D057: `Real.instMul`

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

### D061: `instOfNatNat`

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

### D062: `DivInvMonoid.toDiv`

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

### D063: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D064: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D065: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D066: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D067: `HDiv.hDiv`

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

### D068: `HSub.hSub`

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

### D069: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D070: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D071: `One.toOfNat1`

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

### D072: `Pi.instSub`

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

### D073: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D074: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D075: `Real.instDivInvMonoid`

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

### D076: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D077: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D078: `Real.instOne`

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

### D079: `Real.instSub`

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

### D080: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D081: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D082: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D083: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D084: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D085: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D086: `instHDiv`

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

### D087: `instHSub`

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

### D088: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```

### D089: `Asymptotics.IsBigO`

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

### D090: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D091: `Fin.fintype`

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

### D092: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D093: `Finset.sum`

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

### D094: `Finset.univ`

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

### D095: `HPow.hPow`

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

### D096: `Matrix`

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

### D097: `Monoid.toNatPow`

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

### D098: `Nat.cast`

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

### D099: `Ne`

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

### D100: `Pi.instAdd`

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

### D101: `Pi.instZero`

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

### D102: `Real.instAddCommMonoid`

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

### D103: `Real.instMonoid`

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

### D104: `Real.instNatCast`

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

### D105: `Real.norm`

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

### D106: `Real.sqrt`

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

### D107: `instHPow`

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

### D108: `instLTNat`

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

### D109: `Function.Bijective`

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

### D110: `Matrix.frobeniusNormedRing`

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

### D111: `Norm.norm`

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

### D112: `NormedRing.toNorm`

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

### D113: `Real.instRCLike`

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

### D114: `instDecidableEqFin`

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

### D115: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D116: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D117: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D118: `Matrix.frobeniusNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D119: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D120: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```
