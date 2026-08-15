# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (problem : LocalDef003 n) (u : ι → Real)
  (run : (t : ι) → LocalDef001 problem (u t)),
  Filter.Tendsto u l (nhds 0) →
    Ne (LocalDef009 problem) 0 →
      Ne (LocalDef005 problem) 0 →
        have conditionData := LocalDef004 problem;
        have conditionOne := LocalDef010 problem;
        And
          (Filter.Eventually
            (fun t =>
              Real.instLE.le (LocalDef011 (run t))
                (LocalDef006 n (u t) conditionData conditionOne))
            l)
          (And
            (Filter.Eventually
              (fun t =>
                Eq (LocalDef006 n (u t) conditionData conditionOne)
                  (instHAdd.hAdd
                    (instHMul.hMul (u t)
                      (LocalDef007 n conditionData conditionOne))
                    (LocalDef008 n conditionData conditionOne (u t))))
              l)
            (And
              (Asymptotics.IsBigO l
                (fun t => LocalDef008 n conditionData conditionOne (u t)) fun t =>
                instHPow.hPow (u t) 2)
              (LocalDef002 problem)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (problem : LocalDef003 n) (u : ι → Real)
  (run : (t : ι) → @LocalDef001 n problem (u t))
  (hu :
    @Filter.Tendsto.{u_1, 0} ι Real u l
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
  (hnumerator :
    @Ne.{1} Real (@LocalDef009 n problem)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hdenominator :
    @Ne.{1} Real (@LocalDef005 n problem)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  have conditionData : Real := @LocalDef004 n problem;
  have conditionOne : Real := @LocalDef010 n problem;
  And
    (@Filter.Eventually.{u_1} ι
      (fun (t : ι) =>
        @LE.le.{0} Real Real.instLE (@LocalDef011 n problem (u t) (run t))
          (LocalDef006 n (u t) conditionData conditionOne))
      l)
    (And
      (@Filter.Eventually.{u_1} ι
        (fun (t : ι) =>
          @Eq.{1} Real (LocalDef006 n (u t) conditionData conditionOne)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (u t)
                (LocalDef007 n conditionData conditionOne))
              (LocalDef008 n conditionData conditionOne (u t))))
        l)
      (And
        (@Asymptotics.IsBigO.{u_1, 0, 0} ι Real Real Real.norm Real.norm l
          (fun (t : ι) => LocalDef008 n conditionData conditionOne (u t))
          fun (t : ι) =>
          @HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (u t) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@LocalDef002 n problem)))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `666eff0c552eaa41efc67498c4edf0f8839563c13e1abfb5dfea6656a0a8c24d`

Type:

```lean
{n : Nat} → LocalDef003 n → Real → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7a090a5a54d57838e2584910b21483abedcc081311ab1e5b49bb21a33dbabef4`

Type:

```lean
{n : Nat} → LocalDef003 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  Exists fun weightDirection =>
    Exists fun numeratorDirection =>
      Exists fun denominatorDirection =>
        Exists fun quotientDirection =>
          Real.instLE.le
            (instHMul.hMul (1 / 3)
              (LocalDef007 n
                (LocalDef004 problem)
                (LocalDef010 problem)))
            (LocalDef029 problem weightDirection numeratorDirection
              denominatorDirection quotientDirection)
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `35357d85af3715973b294e5102dbf510af65d02e45c81b808ddf72074e5cb05d`

Type:

```lean
Nat → Type
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bfa54dcf32df4e12665011b29c1f009d3dd85d2deee77a732dc36c5e01740503`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  LocalDef020 (LocalDef023 problem.nodes problem.x) problem.data
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `20af743a089e87596f61a5d0f49467ed589a7da534c30f80eae9d3dbb8076881`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  LocalDef024 (LocalDef023 problem.nodes problem.x) fun x => 1
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3a713b15207571b4cd8740d21247ce0b20f1e2d8a790aad215b56bfa3360a624`

Type:

```lean
Nat → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n u conditionData conditionOne =>
  instHDiv.hDiv
    (instHAdd.hAdd (instHMul.hMul (LocalDef019 u (LocalDef025 n)) conditionData)
      (instHMul.hMul (LocalDef019 u (LocalDef021 n)) conditionOne))
    (instHSub.hSub 1 (instHMul.hMul (LocalDef019 u (LocalDef021 n)) conditionOne))
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3f36157fd85e31053441f8e370857dba9a5d40e722ccb34317bab0de2d546ad9`

Type:

```lean
Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n conditionData conditionOne =>
  instHAdd.hAdd (instHMul.hMul (LocalDef025 n).cast conditionData)
    (instHMul.hMul (LocalDef021 n).cast conditionOne)
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `85b88e92b181ddc825c0a8d341d82ebc924a490f407dfe951eff6e6e2888e179`

Type:

```lean
Nat → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n conditionData conditionOne u =>
  have p := (LocalDef025 n).cast;
  have q := (LocalDef021 n).cast;
  have A := instHMul.hMul p conditionData;
  have B := instHMul.hMul q conditionOne;
  instHDiv.hDiv
    (instHMul.hMul (instHPow.hPow u 2)
      (instHSub.hSub
        (instHAdd.hAdd (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul A p) (instHMul.hMul B q)) (instHMul.hMul A B))
          (instHPow.hPow B 2))
        (instHMul.hMul (instHMul.hMul (instHMul.hMul (instHAdd.hAdd A B) p) (instHAdd.hAdd q B)) u)))
    (instHMul.hMul (instHSub.hSub 1 (instHMul.hMul p u)) (instHSub.hSub 1 (instHMul.hMul (instHAdd.hAdd q B) u)))
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f4364eeeeaecd5008fe5c5211d14ecc27f05561e072f0884cc7b7aa3b9b0491f`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  LocalDef024 (LocalDef023 problem.nodes problem.x) problem.data
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bdb6a03acce863f4a4f238f7cf3780997c0f847abff239f4ec815bd75bd1ef20`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  LocalDef020 (LocalDef023 problem.nodes problem.x) fun x => 1
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `10536dd090a9e3979469e49551408e39a2e7702f21923bb19b32d12992fd4b58`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} → LocalDef001 problem u → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {problem} {u} run =>
  instHDiv.hDiv
    (abs (instHSub.hSub (LocalDef028 problem) (LocalDef027 run)))
    (abs (LocalDef028 problem))
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6227c9b76bfc248384bbd3c5c0245ade1a5882a87ecc81e6e80223babc9e8a35`

Type:

```lean
Nat → Type
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `f0ad33695ebe9f9a0bcba8c87c6335d3ffcc44e357e383a341bbd08ebe545945`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} →
      Real.instLE.le 0 u →
        (weightCounter :
            Fin (instHAdd.hAdd n 1) → LocalDef033 u (LocalDef030 n)) →
          (numeratorEvaluationCounter :
              Fin (instHAdd.hAdd n 1) →
                LocalDef033 u (LocalDef026 n)) →
            (denominatorEvaluationCounter :
                Fin (instHAdd.hAdd n 1) →
                  LocalDef033 u (LocalDef022 n)) →
              (quotientCounter : LocalDef033 u 1) →
                (numeratorCounter :
                    Fin (instHAdd.hAdd n 1) →
                      LocalDef033 u (LocalDef025 n)) →
                  (denominatorCounter :
                      Fin (instHAdd.hAdd n 1) →
                        LocalDef033 u (LocalDef021 n)) →
                    LocalDef031 u (LocalDef030 n) →
                      LocalDef031 u (LocalDef026 n) →
                        LocalDef031 u (LocalDef022 n) →
                          LocalDef031 u 1 →
                            LocalDef031 u (LocalDef025 n) →
                              LocalDef031 u (LocalDef021 n) →
                                (∀ (j : Fin (instHAdd.hAdd n 1)),
                                    Eq (numeratorCounter j).value
                                      (instHMul.hMul
                                        (instHMul.hMul (weightCounter j).value (numeratorEvaluationCounter j).value)
                                        quotientCounter.value)) →
                                  (∀ (j : Fin (instHAdd.hAdd n 1)),
                                      Eq (denominatorCounter j).value
                                        (instHMul.hMul (weightCounter j).value
                                          (denominatorEvaluationCounter j).value)) →
                                    LocalDef001 problem u
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e3c31e71d454391550e4a1bcad4e0aa6d0d506a09d74f6863fe045f25f393709`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `189ce22c6647e6944c1e396682188b66d64394516b067303c5e3f1b6e4b4522e`

Type:

```lean
{n : Nat} → LocalDef003 n → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `6c63e4fe49192698e9707414f274f2b839826771a95807a98875e3f4e4ce0eda`

Type:

```lean
{n : Nat} →
  (nodes : Fin (instHAdd.hAdd n 1) → Real) →
    (Fin (instHAdd.hAdd n 1) → Real) →
      (x : Real) →
        Function.Injective nodes →
          (∀ (j : Fin (instHAdd.hAdd n 1)), Ne x (nodes j)) → LocalDef003 n
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1e868de525c7bc339b98ff225c4c48e30e9f6c025faad4b68b6865cf62b76bd1`

Type:

```lean
{n : Nat} → LocalDef003 n → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `321cec77eb07fe689def20da69ef797885e75f9556a50de393f0552f5dbafdfd`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

Type:

```lean
Real → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d7fa6d0b4989adc94f4aad1f81cfa4b3701ddea99c39dd03e0dff65ff72bb46d`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ell f =>
  instHDiv.hDiv (Finset.univ.sum fun i => abs (instHMul.hMul (ell i) (f i)))
    (abs (LocalDef024 ell f))
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d7c5ab78aae6703b524b36c2a734643117b9a0a6b05ce4d491df790661f9e223`

Type:

```lean
Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => instHAdd.hAdd (instHMul.hMul 3 n) 2
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f400bb8acd7ce7d65925ab1acc34ffb4e6bfc54c1754027ab9da238979e85b73`

Type:

```lean
Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => instHAdd.hAdd n 2
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f7f897f42a6fcd7f20655a399bd26b59439f7a4dae04d2de8a28b16719cb6407`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Real → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} nodes x j => instHDiv.hDiv (LocalDef039 nodes j) (instHSub.hSub x (nodes j))
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `70562d0bc0d8c2ac0f383af2d951ff600b8a30ab3a85c099f9d4f449c22ebc0b`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ell f => Finset.univ.sum fun i => instHMul.hMul (ell i) (f i)
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5305bad2b7ea8152617e820052a0d742002d3453c36a26f24e131699afc3b5d7`

Type:

```lean
Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => instHAdd.hAdd (instHMul.hMul 3 n) 4
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fd986c9cc371ae10f5d9208ac8251b905de55dae435831414e59a59743f01a83`

Type:

```lean
Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => instHAdd.hAdd n 3
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `52fdc238b3dcf9401a9631936ec315dbf136ab18cc273ff803dca151395e22b2`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} → LocalDef001 problem u → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {problem} {u} run =>
  instHMul.hMul
    (instHDiv.hDiv
      (Finset.univ.sum fun j =>
        instHMul.hMul
          (instHMul.hMul
            (instHMul.hMul (LocalDef023 problem.nodes problem.x j)
              (run.weightCounter j).value)
            (problem.data j))
          (run.numeratorEvaluationCounter j).value)
      (Finset.univ.sum fun j =>
        instHMul.hMul
          (instHMul.hMul (LocalDef023 problem.nodes problem.x j)
            (run.weightCounter j).value)
          (run.denominatorEvaluationCounter j).value))
    run.quotientCounter.value
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fbbf433fb2265d60d14826f658dcb480046ee1d7d07e7b322110ccbb924e5890`

Type:

```lean
{n : Nat} → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem =>
  instHDiv.hDiv (LocalDef009 problem)
    (LocalDef005 problem)
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `16e61629de7c7e8e5678b3f59993d916ae6bbd145a4999b88c8f0df3303ab09d`

Type:

```lean
{n : Nat} →
  LocalDef003 n →
    (Fin (instHAdd.hAdd n 1) → LocalDef012 (LocalDef030 n)) →
      (Fin (instHAdd.hAdd n 1) →
          LocalDef012 (LocalDef026 n)) →
        (Fin (instHAdd.hAdd n 1) →
            LocalDef012 (LocalDef022 n)) →
          LocalDef012 1 → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem weightDirection numeratorDirection denominatorDirection quotientDirection =>
  have coeff := LocalDef023 problem.nodes problem.x;
  abs
    (instHAdd.hAdd
      (instHSub.hSub
        (instHDiv.hDiv
          (Finset.univ.sum fun j =>
            instHMul.hMul (instHMul.hMul (coeff j) (problem.data j))
              (instHAdd.hAdd (LocalDef040 (weightDirection j))
                (LocalDef040 (numeratorDirection j))))
          (LocalDef009 problem))
        (instHDiv.hDiv
          (Finset.univ.sum fun j =>
            instHMul.hMul (coeff j)
              (instHAdd.hAdd (LocalDef040 (weightDirection j))
                (LocalDef040 (denominatorDirection j))))
          (LocalDef005 problem)))
      (LocalDef040 quotientDirection))
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6ff638f2d56516e9ed68f48976a53616d658256e2aa23f8eaeae8cf765d6b86e`

Type:

```lean
Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => instHMul.hMul 2 n
```

### D031: `LocalDef031`

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

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1bd33bde4934a2ae4884514faa9f0e69fd46a85cceeb3fd9df8a2cd694d4c658`

Type:

```lean
{k : Nat} →
  (localDirection : Fin k → Real) →
    (∀ (i : Fin k), Real.instLE.le (abs (localDirection i)) 1) → LocalDef012 k
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `6b61470017b0887f6814bf4df5f5bd0289c4ddb3e1bda8927d080235d18c0a88`

Type:

```lean
Real → Nat → Type
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0c7a8f489db839b979811b1fe1bb26f0afc4fa6cc135396e5eff0002698e6cb3`

Type:

```lean
{u : Real} → {k : Nat} → LocalDef033 u k → Real
```

Definition body (one-level semantic boundary):

```lean
fun u k self => self.1
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3d8fd8a89fa7d5a70a121233fbe828d017206bf62ec6ab23c9d8002b0c531477`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} →
      LocalDef001 problem u →
        Fin (instHAdd.hAdd n 1) →
          LocalDef033 u (LocalDef022 n)
```

Definition body (one-level semantic boundary):

```lean
fun n problem u self => self.4
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c23e27fe3bf581c4add47336e9cc62e405ceeaca2efaac3c10a54d9425dc26d0`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} →
      LocalDef001 problem u →
        Fin (instHAdd.hAdd n 1) →
          LocalDef033 u (LocalDef026 n)
```

Definition body (one-level semantic boundary):

```lean
fun n problem u self => self.3
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `36dff695844c2fb0bc5dadfe77cfb865b7a8dc385ba2f5b6ad55aaed84b754cc`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} → LocalDef001 problem u → LocalDef033 u 1
```

Definition body (one-level semantic boundary):

```lean
fun n problem u self => self.5
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e4856658fae83e2366a4b9a63bd9201431a9e7f0d48183dcab9c02b441cc1d40`

Type:

```lean
{n : Nat} →
  {problem : LocalDef003 n} →
    {u : Real} →
      LocalDef001 problem u →
        Fin (instHAdd.hAdd n 1) → LocalDef033 u (LocalDef030 n)
```

Definition body (one-level semantic boundary):

```lean
fun n problem u self => self.2
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b304de61f236961dae3825dc78753b469784db32e3eac794a8bc7f9c5bbe516a`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} nodes j => Real.instInv.inv (Finset.univ.prod fun k => ite (Eq k j) 1 (instHSub.hSub (nodes j) (nodes k)))
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2424928b332af2204450828a6c9d9699a950523b8f16292db7b5f6bae7f60d58`

Type:

```lean
{k : Nat} → LocalDef012 k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {k} direction => Finset.univ.sum fun i => direction.localDirection i
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fca57948753231b5da58018bf2356083bc659fbf3dff40dddc6ae7c6695cbbf7`

Type:

```lean
{k : Nat} → LocalDef012 k → Fin k → Real
```

Definition body (one-level semantic boundary):

```lean
fun k self => self.1
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `44d124407806db79b36a4592543c0f40df2907398e106b344912b2fc24b0295b`

Type:

```lean
{u : Real} →
  {k : Nat} →
    (value : Real) →
      (localError : Fin k → Real) →
        (reciprocal : Fin k → Bool) →
          (∀ (i : Fin k), Real.instLE.le (abs (localError i)) u) →
            Eq value
                (Finset.univ.prod fun i =>
                  ite (Eq (reciprocal i) Bool.true) (Real.instInv.inv (instHAdd.hAdd 1 (localError i)))
                    (instHAdd.hAdd 1 (localError i))) →
              (LocalDef031 u k → Real.instLE.le (abs (instHSub.hSub value 1)) (LocalDef019 u k)) →
                LocalDef033 u k
```

### D043: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D044: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D045: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D046: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

### D047: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D048: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

### D049: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D050: `HAdd.hAdd`

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

### D051: `HMul.hMul`

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

### D052: `HPow.hPow`

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

### D053: `LE.le`

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

### D054: `Monoid.toNatPow`

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

### D056: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
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

### D058: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
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

### D061: `Real.instLE`

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

### D062: `Real.instMonoid`

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

### D063: `Real.instMul`

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

### D064: `Real.instZero`

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

### D065: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```

### D066: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D067: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
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

### D069: `instHAdd`

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

### D070: `instHMul`

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

### D071: `instHPow`

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

### D072: `instOfNatNat`

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

### D073: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
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

### D075: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D076: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D077: `HDiv.hDiv`

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

### D079: `Nat.cast`

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

### D080: `One.toOfNat1`

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

### D081: `Real.instAddGroup`

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

### D082: `Real.instDivInvMonoid`

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

### D083: `Real.instNatCast`

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

### D084: `Real.instOne`

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

### D085: `Real.instSub`

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

### D086: `Real.lattice`

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

### D087: `abs`

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

### D088: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D089: `instHDiv`

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

### D090: `instHSub`

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

### D091: `instOfNatAtLeastTwo`

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

### D092: `Fin.fintype`

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

### D095: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```

### D096: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D097: `Real.instAddCommMonoid`

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

### D098: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `15abc50804fa78aecc5a807f82f13a6b67bcdff9061558426471fc4b606841aa`

Type:

```lean
Mul Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul }
```

### D099: `Finset.prod`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `e364cffe1f2457eedceca9fe0617d7a66084963ffb6e6ed760d1f3fe74eee841`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [CommMonoid M] s f => (Multiset.map f s.val).prod
```

### D100: `Inv.inv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `c3aea3c6e2edd31a7b2cf071814315808ef7d84fd01d8c9b719313846ebca438`

Type:

```lean
{α : Type u} → [self : Inv α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Inv α] => self.1
```

### D101: `LT.lt`

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

### D102: `Real.instCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f537dc5e9be2b886066e25d0f560dc52fd1be771759ec3e7b40a5f5f3e6c6467`

Type:

```lean
CommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D103: `Real.instInv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `8996fd673a1e2289aaf761085a60a161bdafebda8cdd48d1efb3c89da1382980`

Type:

```lean
Inv Real
```

Definition body (one-level semantic boundary):

```lean
{ inv := Real.inv'✝ }
```

### D104: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D105: `instDecidableEqFin`

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

### D106: `ite`

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

### D107: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D108: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

### D109: `instDecidableEqBool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `dedf43b35e221c78c811d0b7268b7be703d67b744ad16b23df01af14b2aa5899`

Type:

```lean
DecidableEq Bool
```

Definition body (one-level semantic boundary):

```lean
Bool.decEq
```
