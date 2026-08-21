# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m n q p : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (execution : LocalDef004 m n q p ι l),
  And
    (LocalDef008 l (LocalDef017 execution.run)
      (LocalDef016 execution.run) fun t =>
      LocalDef018
        (LocalDef014 n p (LocalDef010 execution.run.model t)
          (LocalDef007 execution.run.model t)
          (LocalDef011 n execution.run.model t)
          (LocalDef009 execution.run.model t)
          (LocalDef006 execution.run.model t))
        execution.run.A execution.run.B)
    (∀ (t : ι),
      Eq
        (LocalDef014 n p (LocalDef010 execution.run.model t)
          (LocalDef007 execution.run.model t)
          (LocalDef011 n execution.run.model t)
          (LocalDef009 execution.run.model t)
          (LocalDef006 execution.run.model t))
        (instHAdd.hAdd
          (instHAdd.hAdd
            (LocalDef015 n p (LocalDef010 execution.run.model t)
              (LocalDef007 execution.run.model t))
            (LocalDef013 n p (LocalDef010 execution.run.model t)
              (LocalDef011 n execution.run.model t)
              (LocalDef009 execution.run.model t)))
          (LocalDef012 n p
            (LocalDef011 n execution.run.model t)
            (LocalDef006 execution.run.model t))))
```

## Fully explicit elaborated target type

```lean
∀ {m n q p : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (execution : LocalDef004.{u_1} m n q p ι l),
  And
    (@LocalDef008.{u_1} ι l
      (@LocalDef017.{u_1} m n q p ι
        (@LocalDef005.{u_1} m n q p ι l execution))
      (@LocalDef016.{u_1} m n q p ι
        (@LocalDef005.{u_1} m n q p ι l execution))
      fun (t : ι) =>
      @LocalDef018 m n q
        (LocalDef014 n p
          (@LocalDef010.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef007.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef011.{u_1} ι n
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef009.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef006.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t))
        (@LocalDef001.{u_1} m n q p ι
          (@LocalDef005.{u_1} m n q p ι l execution))
        (@LocalDef002.{u_1} m n q p ι
          (@LocalDef005.{u_1} m n q p ι l execution)))
    (∀ (t : ι),
      @Eq.{1} Real
        (LocalDef014 n p
          (@LocalDef010.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef007.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef011.{u_1} ι n
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef009.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t)
          (@LocalDef006.{u_1} ι
            (@LocalDef003.{u_1} m n q p ι
              (@LocalDef005.{u_1} m n q p ι l execution))
            t))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (LocalDef015 n p
              (@LocalDef010.{u_1} ι
                (@LocalDef003.{u_1} m n q p ι
                  (@LocalDef005.{u_1} m n q p ι l execution))
                t)
              (@LocalDef007.{u_1} ι
                (@LocalDef003.{u_1} m n q p ι
                  (@LocalDef005.{u_1} m n q p ι l execution))
                t))
            (LocalDef013 n p
              (@LocalDef010.{u_1} ι
                (@LocalDef003.{u_1} m n q p ι
                  (@LocalDef005.{u_1} m n q p ι l execution))
                t)
              (@LocalDef011.{u_1} ι n
                (@LocalDef003.{u_1} m n q p ι
                  (@LocalDef005.{u_1} m n q p ι l execution))
                t)
              (@LocalDef009.{u_1} ι
                (@LocalDef003.{u_1} m n q p ι
                  (@LocalDef005.{u_1} m n q p ι l execution))
                t)))
          (LocalDef012 n p
            (@LocalDef011.{u_1} ι n
              (@LocalDef003.{u_1} m n q p ι
                (@LocalDef005.{u_1} m n q p ι l execution))
              t)
            (@LocalDef006.{u_1} ι
              (@LocalDef003.{u_1} m n q p ι
                (@LocalDef005.{u_1} m n q p ι l execution))
              t))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9594cae7a57d44827ec93e7f76c28c0a1a8e6230a411eec2b095b16f7a2966e3`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.4
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9c67bfedcd197f366d508e5bd9df25a16a76d40081a3374f8a376548cba5ddb6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.5
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8be01d8ad1d537a6367b7523510f0e9470719882b08c7e39ddbf8c2f567be8e6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → LocalDef020 ι
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.3
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `416516a9510181b79d744eff2caab5d64f7243e54d03c62febd24c0db946ad05`

Type:

```lean
Nat → Nat → Nat → Nat → (ι : Type u_1) → Filter ι → Type u_1
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fed6503d9202666af3f4554377177f5cd361a42d30bb6bbd290b900528277d12`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → LocalDef004 m n q p ι l → LocalDef023 m n q p ι
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι l self => self.1
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4c3c15a2681fa86b178a756216726f84a6b209b2f9fbdf991f246cc135fcd2d2`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => LocalDef027 model.accumulationFormat t
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `90703ecd8044f6d933fb829dec2b80806bc4ff0e497a031e28b00d72cabcd19e`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => LocalDef028 model.accumulationFormat t
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1521ce8a7cd811a1f00f9d6fa76581378be240fcef6e441dd7723db094ab6e3f`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (LocalDef034 l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `65fb848ac68b350b4c5f345e1b63f3818de1dfd55b1441c386210576f85e7701`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => LocalDef027 model.inputFormat t
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c8ca83340edf9709c9e3394a10d383e421ce4db7c464585c7c881bc878956a32`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} model t => LocalDef028 model.inputFormat t
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8177b50be99c15b398f8f4378f9be576d43e18ba542f985b3c11aa1737057c8e`

Type:

```lean
{ι : Type u_1} → Nat → LocalDef020 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} n model t =>
  LocalDef033 n (LocalDef026 model.inputFormat t)
    (LocalDef026 model.accumulationFormat t)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5aeb2436e762793f876c56e261949985186ece9b87b7642526cca63726f5cbc8`

Type:

```lean
Nat → Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p theta Gmin =>
  instHMul.hMul
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 p.cast) (instHAdd.hAdd p.cast 1)) (instHPow.hPow n.cast 2))
      (instHPow.hPow (Real.instInv.inv theta) 2))
    Gmin
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e81b283d73a42696b3ad126f193ca40cb6314201f6a0894d43f37fb73d5a2f56`

Type:

```lean
Nat → Nat → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u theta gmin =>
  instHMul.hMul
    (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 n.cast) (instHPow.hPow u (instHSub.hSub p 1)))
      (Real.instInv.inv theta))
    gmin
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `caa0600e2ab6bac4a1950fef389ea5430e501684280b91c745f1ee261a9ba7c7`

Type:

```lean
Nat → Nat → Real → Real → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u U theta gmin Gmin =>
  instHAdd.hAdd
    (instHAdd.hAdd (LocalDef015 n p u U)
      (LocalDef013 n p u theta gmin))
    (LocalDef012 n p theta Gmin)
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2487e9b14eff0b27a720d879c028573ed442dba650abf6c1634f308d44e7e364`

Type:

```lean
Nat → Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u U =>
  instHAdd.hAdd (LocalDef032 p u) (LocalDef031 n p U)
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cc3dbc71a874f6b6ec77ae52e0346c81d20c3ea2892c754a4633ab82e4e6181d`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  LocalDef029
    (instHSub.hSub (run.computed t) (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `92d7b625d010a5e2f91f00abf58e263ee2c8991480c39169b02129316ec5f3f2`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHAdd.hAdd (instHPow.hPow (LocalDef010 run.model t) p)
        (instHMul.hMul
          (instHMul.hMul (instHPow.hPow (LocalDef010 run.model t) (instHSub.hSub p 1))
            (Real.instInv.inv (LocalDef011 n run.model t)))
          (LocalDef009 run.model t)))
      (LocalDef007 run.model t))
    (instHMul.hMul (instHPow.hPow (Real.instInv.inv (LocalDef011 n run.model t)) 2)
      (LocalDef006 run.model t))
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8b3df00dc379b26060ad35527c8889510927aa8aae6ac3b90b480d9ea8ecb0de`

Type:

```lean
{m n q : Nat} → Real → (Fin m → Fin n → Real) → (Fin n → Fin q → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q} coefficient A B =>
  instHMul.hMul (instHMul.hMul coefficient (LocalDef029 A)) (LocalDef029 B)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8816b1a67d28d646055c444bb08aa6cc7cb0918adb37ddbe0e4b64f19a1937b4`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e061b0ae3b92688463023faf203412bd4115dc0ed0667840f7767652f00b9019`

Type:

```lean
Type u_1 → Type u_1
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `019580b5dca9b3907a64545ee2b700984d557fbd9c0f2dafd17bf6484dfc7e63`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → LocalDef036 ι
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.2
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fdc85d76dfd8fdfe7bfc27ffd0f7e0b055310bbd4409c607e4b5b0b7d5b9272d`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → LocalDef036 ι
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.1
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f178a3d0f984cdaa9efc033435294822cc599bf33537fc8e7c0e07199286d2fc`

Type:

```lean
Nat → Nat → Nat → Nat → Type u_1 → Type u_1
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9b51e165c494e180ef797bc7a505ebfe42b1db813e25bc6ee4dbe6374540037a`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.16
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f9e19e81cf10969d8983d8f14f1d8fea0589fccb6adf3bb96b8f73f1fc2bed4`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : LocalDef023 m n q p ι) →
        LocalDef042 run → LocalDef004 m n q p ι l
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e247b0fabe551e796b6da7ea178c4d700c64dbf29a01abedbf0725f497a97ff1`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t => LocalDef044 (format.precision t) (format.maxExponent t)
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2c81bbdf95763d3fa04a1c4ccaa3cac2e1320e447cb84541092ab38dbd2b83e0`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t =>
  LocalDef045 (format.precision t) (format.minExponent t) (format.hasSubnormals t)
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9e812a87b4db8426019cf32b6a1ced30d8bceb7427e394157773672a06514e80`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} format t => LocalDef046 (format.precision t)
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `85f0c53817ee468470f6b18e6390691148158e3a270bf87d2feb43e175ec9e0a`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A =>
  have rowSum := fun i => Finset.univ.sum fun j => SeminormedAddGroup.toNNNorm.nnnorm (A i j);
  (Finset.univ.sup rowSum).toReal
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `2ce92de675040573a86bb56eb1810ec5f97d8bfda24fdbdb86d7ca409b945411`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f6f3cf93f5f3ae2f8f71ee9bb65c6b5bdb6b612575c6584b8ad6e0e9d7466b7a`

Type:

```lean
Nat → Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p U => instHMul.hMul (instHAdd.hAdd n.cast (instHPow.hPow p.cast 2)) U
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d95881c72218c764905e4c1450dd882eda6fa4a4c4a6840f2ec5044e3981f45a`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun p u => instHMul.hMul (instHAdd.hAdd p.cast 1) (instHPow.hPow u p)
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9f68c8a231e4cea47898d3834d4362c543f7e7455dc046f54bb660b2dff27910`

Type:

```lean
Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n fmax Fmax => Real.instMin.min fmax (instHDiv.hDiv Fmax n.cast).sqrt
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0e067e47238962db3263b46553181a9e7fd40da11726a292ab40026a81435288`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `8a85a65264d1eaf6bf92eb9238ef21e86787b07b20e078bcd23e3fd0e91d4fbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `f68a172410c9f21a3e85a3437dc6a91f7d8b7987bb2bc0e88a508c3382845171`

Type:

```lean
Type u_1 → Type u_1
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `390b0a085aaf97e51cd4cf35d7860d38ac05963d49604a5558ee81436c840d6a`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Bool
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.4
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3b81919890027c1e8a089b64312b036157e0406024d90701758eac7df5f53065`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Int
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.3
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d423cdf3493e923735f83da736f28a3fe9781ed8df32e051de3dc5ebf4263509`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Int
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.2
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `15283c4649b8a2eb8dbea073396ef2096b142fffdad25db29fc18bd95e90d37f`

Type:

```lean
{ι : Type u_1} → LocalDef036 ι → ι → Nat
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.1
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7546b5e58afb9aa467efb29e321d522aa2044aee6b5571587488bc68eaed388c`

Type:

```lean
{ι : Type u_1} →
  (inputFormat accumulationFormat : LocalDef036 ι) →
    (∀ (t : ι), instLENat.le (inputFormat.precision t) (accumulationFormat.precision t)) →
      (∀ (t : ι),
          And (Int.instLEInt.le (accumulationFormat.minExponent t) (inputFormat.minExponent t))
            (Int.instLEInt.le (inputFormat.maxExponent t) (accumulationFormat.maxExponent t))) →
        (inputRound inputDelta inputEta : ι → Real → Real) →
          (∀ (t : ι) (x : Real),
              Eq (inputRound t x) (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (inputDelta t x))) (inputEta t x))) →
            (∀ (t : ι) (x : Real),
                Real.instLE.le (abs (inputDelta t x)) (LocalDef028 inputFormat t)) →
              (∀ (t : ι) (x : Real),
                  Real.instLE.le (abs (inputEta t x)) (LocalDef027 inputFormat t)) →
                (∀ (t : ι) (x : Real), Eq (instHMul.hMul (inputEta t x) (inputDelta t x)) 0) →
                  (accumulationRound accumulationDelta accumulationEta : ι → Real → Real) →
                    (∀ (t : ι) (x : Real),
                        Eq (accumulationRound t x)
                          (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (accumulationDelta t x)))
                            (accumulationEta t x))) →
                      (∀ (t : ι) (x : Real),
                          Real.instLE.le (abs (accumulationDelta t x))
                            (LocalDef028 accumulationFormat t)) →
                        (∀ (t : ι) (x : Real),
                            Real.instLE.le (abs (accumulationEta t x))
                              (LocalDef027 accumulationFormat t)) →
                          (∀ (t : ι) (x : Real), Eq (instHMul.hMul (accumulationEta t x) (accumulationDelta t x)) 0) →
                            LocalDef020 ι
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85887da83eb47ab9a6773f4132be09426ddc4f08decdc172ba510784de9131ce`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef023 m n q p ι → Type u_1
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `f097b804cc549a67af75c82d98427f5897fa6da7f3ada1c1915d8516a0be1aaf`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    And (instLTNat.lt 0 m) (And (instLTNat.lt 0 n) (instLTNat.lt 0 q)) →
      instLTNat.lt 0 p →
        (model : LocalDef020 ι) →
          (A : LocalDef019 m n) →
            (B : LocalDef019 n q) →
              (rowScale : ι → Fin m → Real) →
                (columnScale : ι → Fin q → Real) →
                  (∀ (t : ι) (i : Fin m),
                      LocalDef052 (LocalDef011 n model t)
                        (LocalDef051 (A i)) (rowScale t i)) →
                    (∀ (t : ι) (j : Fin q),
                        LocalDef052 (LocalDef011 n model t)
                          (LocalDef051 fun i => B i j) (columnScale t j)) →
                      (∀ (t : ι) (i : Fin m) (j : Fin n),
                          Real.instLE.le (abs (LocalDef056 (rowScale t) A i j))
                            (LocalDef011 n model t)) →
                        (∀ (t : ι) (i : Fin n) (j : Fin q),
                            Real.instLE.le (abs (LocalDef055 B (columnScale t) i j))
                              (LocalDef011 n model t)) →
                          (Aword : ι → Fin p → LocalDef019 m n) →
                            (Bword : ι → Fin p → LocalDef019 n q) →
                              (∀ (t : ι) (i : Fin p) (row : Fin m) (col : Fin n),
                                  Eq (Aword t i row col)
                                    (model.inputRound t
                                      (instHDiv.hDiv
                                        (instHSub.hSub (LocalDef056 (rowScale t) A row col)
                                          ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                            instHMul.hMul
                                              (instHPow.hPow (LocalDef010 model t) k.val)
                                              (Aword t k row col)))
                                        (instHPow.hPow (LocalDef010 model t) i.val)))) →
                                (∀ (t : ι) (i : Fin p) (row : Fin n) (col : Fin q),
                                    Eq (Bword t i row col)
                                      (model.inputRound t
                                        (instHDiv.hDiv
                                          (instHSub.hSub (LocalDef055 B (columnScale t) row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (LocalDef010 model t) k.val)
                                                (Bword t k row col)))
                                          (instHPow.hPow (LocalDef010 model t) i.val)))) →
                                  (computed : ι → LocalDef019 m q) →
                                    (∀ (t : ι),
                                        Eq (computed t)
                                          (LocalDef058 (rowScale t) (columnScale t)
                                            (LocalDef054 (model.accumulationRound t)
                                              (LocalDef010 model t) (Aword t) (Bword t)))) →
                                      LocalDef023 m n q p ι
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e812122843a7693eb9da20df127bdfd0b036f7eb87b5291df77467d35da85027`

Type:

```lean
Nat → Int → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision maxExponent =>
  instHMul.hMul (instHPow.hPow 2 maxExponent)
    (instHSub.hSub 2 (instHMul.hMul 2 (LocalDef046 precision)))
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `98e39d9e9f622feb1800dc6ed026db533af44c2455719d25e42c991fb6e6b98f`

Type:

```lean
Nat → Int → Bool → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision minExponent hasSubnormals =>
  LocalDef057 (fun hasSubnormals => Real) hasSubnormals
    (fun _ => instHDiv.hDiv (LocalDef053 minExponent) 2) fun _ =>
    instHMul.hMul (LocalDef046 precision) (LocalDef053 minExponent)
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `374e1e67fe075ea077dd0ca7e1b7b13a7719c0f4c5d32224c3e123b307030749`

Type:

```lean
Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision => instHPow.hPow (Real.instInv.inv 2) precision
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `bfbe55aaba8cae1c8051b14d53b97fb80661056589ec88edfc2175227423ba98`

Type:

```lean
{ι : Type u_1} →
  (precision : ι → Nat) →
    (minExponent maxExponent : ι → Int) →
      (ι → Bool) →
        (∀ (t : ι), instLTNat.lt 0 (precision t)) →
          (∀ (t : ι), Int.instLEInt.le (minExponent t) (maxExponent t)) → LocalDef036 ι
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fad245ffc5c0bf3a444afa929cb5f38a2626fdc667cec06d4b2d3b8a8c6320a2`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.12
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `c05f813d78781714c9102a1b87725dd0a5f46a457ef122cd45049ea09beb2fae`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.5
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `68b2dd902c488fcefd9317577852aa6d458a77246a39d74b8c680201a1bd68c1`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : LocalDef023 m n q p ι} →
        (data : LocalDef059 run) →
          (∀ (t : ι),
              Real.instLE.le (LocalDef029 (LocalDef064 data t))
                (LocalDef018
                  (LocalDef032 p (LocalDef010 run.model t)) run.A
                  run.B)) →
            (∀ (t : ι),
                Real.instLE.le (LocalDef029 (LocalDef065 data t))
                  (LocalDef018
                    (LocalDef013 n p (LocalDef010 run.model t)
                      (LocalDef011 n run.model t)
                      (LocalDef009 run.model t))
                    run.A run.B)) →
              (∀ (t : ι),
                  Real.instLE.le (LocalDef029 (LocalDef060 data t))
                    (LocalDef018
                      (LocalDef031 n p (LocalDef007 run.model t))
                      run.A run.B)) →
                (∀ (t : ι),
                    Real.instLE.le (LocalDef029 (LocalDef061 data t))
                      (LocalDef018
                        (LocalDef012 n p
                          (LocalDef011 n run.model t)
                          (LocalDef006 run.model t))
                        run.A run.B)) →
                  (LocalDef034 l (LocalDef017 run) fun t =>
                      LocalDef029 (LocalDef063 run data t)) →
                    LocalDef042 run
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `87f59ddda7d28f2342745750052393a1a7f8e6da20099629ce901b53ae3a06a8`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sup fun i => (abs (x i)).toNNReal).toReal
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `fb4c39249333a2b6fcc41db880a13b76bb70b92044a24ec0042af3b1053ddfc8`

Type:

```lean
Real → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun theta vectorNorm lambda =>
  And (LocalDef066 lambda)
    (And (Real.instLT.lt 0 lambda)
      (Or (And (Eq vectorNorm 0) (Eq lambda 1))
        (And (Real.instLT.lt 0 vectorNorm)
          (And (Real.instLT.lt (instHDiv.hDiv theta (instHMul.hMul 2 vectorNorm)) lambda)
            (Real.instLE.le lambda (instHDiv.hDiv theta vectorNorm))))))
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `a1ea1d99687f61140e8592b6154c5c66bbde2de8d842aa90e456007cea8d43fd`

Type:

```lean
Int → Real
```

Definition body (one-level semantic boundary):

```lean
fun minExponent => instHPow.hPow 2 minExponent
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `54b336ce4868ee145633cb139fd883806f827fa26cfa6a2fe2b32d8d0c9685d3`

Type:

```lean
{m n q p : Nat} →
  (Real → Real) →
    Real → (Fin p → LocalDef019 m n) → (Fin p → LocalDef019 n q) → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} round u Aword Bword row col =>
  List.foldl
    (fun sum pair =>
      round
        (instHAdd.hAdd sum
          (instHMul.hMul (instHPow.hPow u (instHAdd.hAdd pair.fst.val pair.snd.val))
            (LocalDef062 round (Aword pair.fst row) fun k => Bword pair.snd k col))))
    0 (LocalDef067 p)
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `378c6beb84502e2b56ff224e26171be0f80b1263c8d574e611b959c865a7073f`

Type:

```lean
{n q : Nat} → LocalDef019 n q → (Fin q → Real) → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun {n q} B mu i j => instHMul.hMul (B i j) (mu j)
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `00f5599a51f7504fa6af21fe5f75dbc8584462339602b0cca6a3d151edb4518f`

Type:

```lean
{m n : Nat} → (Fin m → Real) → LocalDef019 m n → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n} lambda A i j => instHMul.hMul (lambda i) (A i j)
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `58f84c67586c398171db7adf3049e575348ae8be9cfe7a764f1cdbe2eb2944fa`

Type:

```lean
(motive : Bool → Sort u_1) →
  (hasSubnormals : Bool) → (Unit → motive Bool.false) → (Unit → motive Bool.true) → motive hasSubnormals
```

Definition body (one-level semantic boundary):

```lean
fun motive hasSubnormals h_1 h_2 => Bool.casesOn hasSubnormals (h_1 Unit.unit) (h_2 Unit.unit)
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f39885f324faf09cbe5e6c2bd4eae850670ec539979d0b37aaed2094bab7cc7b`

Type:

```lean
{m q : Nat} → (Fin m → Real) → (Fin q → Real) → LocalDef019 m q → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m q} lambda mu C i j =>
  instHMul.hMul (instHMul.hMul (Real.instInv.inv (lambda i)) (C i j)) (Real.instInv.inv (mu j))
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `5f3c858c4f89c05ccc0ed46c038e51f3ef417fb48f9424a25ece1ef566d7ed25`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → Type u_1
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f5aaa6aa0d03307189f851e6da09a8586ed614d024434ee292e7a15b3e84fb69`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t => data.accumulationRoundingError t
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d3a8c32a78d3b89a2ee6cd7f72a1f53f38a3f6ee9a05ab2ca61e1747892a887d`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t => data.accumulationUnderflowError t
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `85ce3b8c1ee59d62e0d9951b949ec2dc99ba00d4170e02662308816d384cbd6a`

Type:

```lean
{n : Nat} → (Real → Real) → (Fin n → Real) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} round x y =>
  List.foldl (fun sum product => round (instHAdd.hAdd sum product)) 0 (List.ofFn fun k => instHMul.hMul (x k) (y k))
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6f6b2dcf16831723a067aadc66a4b35fa717345a2ca0149a7c0ce72dee226aa1`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    (run : LocalDef023 m n q p ι) →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run data t =>
  instHSub.hSub
    (instHSub.hSub
      (instHSub.hSub
        (instHSub.hSub (instHSub.hSub (run.computed t) (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
          (LocalDef064 data t))
        (LocalDef065 data t))
      (LocalDef060 data t))
    (LocalDef061 data t)
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `31a7c0afe8475a9d0f0d38af1eabb4411434b0b9d3aacaecfe4b1e73d873384a`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t =>
  instHSub.hSub
    (instHSub.hSub
      (Matrix.neg.neg (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (data.AInputRoundingError t) run.B))
      (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A (data.BInputRoundingError t)))
    (LocalDef075 run t)
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `23680fa4dc54682210dfff756a0c9c80d438f1434c13b012471339d1344d0767`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t =>
  instHSub.hSub (Matrix.neg.neg (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (data.AInputUnderflowError t) run.B))
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A (data.BInputUnderflowError t))
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `cdbc02ca950134eb20d94e5488f66c176cc912c7aa24e523ded6bd5ee37e98e5`

Type:

```lean
Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun lambda => Exists fun exponent => Eq lambda (instHPow.hPow 2 exponent)
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `c8eb3bb88b390d5375a9471b422e3090d5bc32cb7df3a80bd86cf45656a76a86`

Type:

```lean
(p : Nat) → List (Prod (Fin p) (Fin p))
```

Definition body (one-level semantic boundary):

```lean
fun p =>
  (List.ofFn fun i =>
      List.filter (fun pair => Decidable.decide (instLTNat.lt (instHAdd.hAdd pair.fst.val pair.snd.val) p))
        (List.ofFn fun j => { fst := i, snd := j })).flatten
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `77508b759f619eaae6ea59e70225de84e49118a884b081fb84ab5cd0565e09fe`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.1
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `a61f4629a9dc3e36d4d9922d3cdf5d0d19939d2320fda0b4dd53009663de7db5`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.2
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `3148ea52a944bc6c708ad4f36c9ec9299dae022f4c35e5898f4301fa9602ad8f`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.3
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `986caad039e54caadbcb261d8d5e4a001f2fb4c1d3e06fee37afc7158dc6f13b`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.4
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `94bc4af35e652c5db0ece164b3de9a930f0c1c154d1df5f01966f14521f16fb9`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.5
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `8197ae91b9f748902f96dd3096d37d4e54cfc620084fff0475ef8d99a0155531`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      LocalDef059 run → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.6
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `6490dacf58d2a01412ef7b0d809ec154a7849d9759bb0edae521b71e0353f66e`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : LocalDef023 m n q p ι} →
      (AInputRoundingError AInputUnderflowError : ι → LocalDef019 m n) →
        (BInputRoundingError BInputUnderflowError : ι → LocalDef019 n q) →
          (accumulationRoundingError accumulationUnderflowError : ι → LocalDef019 m q) →
            (∀ (t : ι),
                Eq run.A
                  (instHAdd.hAdd (instHAdd.hAdd (LocalDef084 run t) (AInputRoundingError t))
                    (AInputUnderflowError t))) →
              (∀ (t : ι),
                  Eq run.B
                    (instHAdd.hAdd (instHAdd.hAdd (LocalDef085 run t) (BInputRoundingError t))
                      (BInputUnderflowError t))) →
                (∀ (t : ι),
                    Eq (LocalDef086 run t)
                      (instHSub.hSub
                        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (LocalDef084 run t)
                          (LocalDef085 run t))
                        (LocalDef075 run t))) →
                  (∀ (t : ι),
                      Eq (run.computed t)
                        (instHAdd.hAdd
                          (instHAdd.hAdd (LocalDef086 run t) (accumulationRoundingError t))
                          (accumulationUnderflowError t))) →
                    (∀ (t : ι), Eq (run.model.inputDelta t) 0 → Eq (AInputRoundingError t) 0) →
                      (∀ (t : ι), Eq (run.model.inputDelta t) 0 → Eq (BInputRoundingError t) 0) →
                        (∀ (t : ι), Eq (run.model.inputEta t) 0 → Eq (AInputUnderflowError t) 0) →
                          (∀ (t : ι), Eq (run.model.inputEta t) 0 → Eq (BInputUnderflowError t) 0) →
                            (∀ (t : ι), Eq (run.model.accumulationDelta t) 0 → Eq (accumulationRoundingError t) 0) →
                              (∀ (t : ι), Eq (run.model.accumulationEta t) 0 → Eq (accumulationUnderflowError t) 0) →
                                LocalDef059 run
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `4d9bd635c661a68662b265b35b679d489fee3096f3a567eef30ea971783dc6c6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  LocalDef058 (run.rowScale t) (run.columnScale t) fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLENat.le p (instHAdd.hAdd i.val j.val)) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (LocalDef010 run.model t) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword t i) (run.Bword t j) row col)
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `78f4fa8a808072352b394fd23b9f8e8213dc294f12981f044ac6ab34e63f868c`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.13
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c1017184d4654028a07a2d635b6c25c17aea82ef8011778d7ca8ece37cd6d2f0`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.14
```

### D078: `LocalDef078`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `f498dd6b9fa820e7e8575e8d39f782b61f9629b97c26b937f83145861b044bdf`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.6
```

### D079: `LocalDef079`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `42ff47cd7311e65a9520c6de941b31a10d25534aaeb2eefac65de17dea1dfb4f`

Type:

```lean
{ι : Type u_1} → LocalDef020 ι → ι → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun ι self => self.7
```

### D080: `LocalDef080`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `955e28b1a74a7b1d2337d62173bba50082092918c6f69114404a9197342b4e38`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Fin p → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.12
```

### D081: `LocalDef081`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `86205166fbe9973a011490dc58c14dfe34f43d0c59be47c8a5cdede35764b166`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Fin p → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.13
```

### D082: `LocalDef082`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `e943c5522e2181584d374eed5f1f68372ff9a03e63da8968753625d60a536c82`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Fin q → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.7
```

### D083: `LocalDef083`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c4ac152ad2707c77d2664ff4cbb7c828f10a598459c0d6cfb6f829e3448e3b42`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.6
```

### D084: `LocalDef084`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `a91a45911fa9d17d856c58ea58f8b198d7dee535b9496955317ce217830221ef`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → LocalDef019 m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t row col =>
  instHMul.hMul (Real.instInv.inv (run.rowScale t row))
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (LocalDef010 run.model t) i.val) (run.Aword t i row col))
```

### D085: `LocalDef085`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `83e23877a59369c44c679f56e678d6f959a9eab93e14bd4aded91115aff6b9b2`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → LocalDef019 n q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t row col =>
  instHMul.hMul
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (LocalDef010 run.model t) i.val) (run.Bword t i row col))
    (Real.instInv.inv (run.columnScale t col))
```

### D086: `LocalDef086`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `89d185a8a35e95ba036183b88c5f925f1714951f417cbeb61ee7b07a1ea15198`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → LocalDef023 m n q p ι → ι → LocalDef019 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  LocalDef058 (run.rowScale t) (run.columnScale t) fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLTNat.lt (instHAdd.hAdd i.val j.val) p) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (LocalDef010 run.model t) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword t i) (run.Bword t j) row col)
```

### D087: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D088: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D089: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

### D090: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

### D091: `HAdd.hAdd`

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

### D092: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D093: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D094: `Real.instAdd`

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

### D095: `instHAdd`

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

### D096: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D097: `Filter.Eventually`

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

### D098: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D099: `Fin.fintype`

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

### D100: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D101: `HPow.hPow`

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

### D102: `HSub.hSub`

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

### D103: `Inv.inv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c3aea3c6e2edd31a7b2cf071814315808ef7d84fd01d8c9b719313846ebca438`

Type:

```lean
{α : Type u} → [self : Inv α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Inv α] => self.1
```

### D104: `LE.le`

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

### D105: `Matrix`

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

### D106: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D107: `Matrix.sub`

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

### D108: `Monoid.toNatPow`

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

### D109: `Nat.cast`

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

### D110: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D111: `One.toOfNat1`

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

### D112: `Real.instAddCommMonoid`

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

### D113: `Real.instAddGroup`

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

### D114: `Real.instInv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8996fd673a1e2289aaf761085a60a161bdafebda8cdd48d1efb3c89da1382980`

Type:

```lean
Inv Real
```

Definition body (one-level semantic boundary):

```lean
{ inv := Real.inv'✝ }
```

### D115: `Real.instLE`

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

### D116: `Real.instMonoid`

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

### D117: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D118: `Real.instNatCast`

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

### D119: `Real.instOne`

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

### D120: `Real.instSub`

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

### D121: `Real.lattice`

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

### D122: `abs`

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

### D123: `instHMul`

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

### D124: `instHPow`

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

### D125: `instHSub`

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

### D126: `instOfNatAtLeastTwo`

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

### D127: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D128: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

Type:

```lean
Sub Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
```

### D129: `Asymptotics.IsBigO`

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

### D130: `ConditionallyCompleteLinearOrderBot.toOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.ConditionallyCompleteLattice.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8d4bfb1cedb616878ecbd86e2180bc7ca93b21716425a9954eeab125e930003f`

Type:

```lean
{α : Type u_5} → [self : ConditionallyCompleteLinearOrderBot α] → OrderBot α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : ConditionallyCompleteLinearOrderBot α] => self.2
```

### D131: `DivInvMonoid.toDiv`

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

### D132: `Finset.sum`

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

### D133: `Finset.sup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Lattice.Fold`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `dd4c14458f3cc53851b18c831b354790927e7783eeceddbd2bc8e0e17c3e5d98`

Type:

```lean
{α : Type u_2} → {β : Type u_3} → [inst : SemilatticeSup α] → [OrderBot α] → Finset β → (β → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [SemilatticeSup α] [inst_1 : OrderBot α] s f =>
  Finset.fold (fun x1 x2 => SemilatticeSup.toMax.max x1 x2) inst_1.bot f s
```

### D134: `Finset.univ`

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

### D135: `HDiv.hDiv`

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

### D136: `Min.min`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4781b8f14117c86f8d250ccd7a9bf20c2b8b6554a48ba0b45f9010ff26a72ea7`

Type:

```lean
{α : Type u} → [self : Min α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Min α] => self.1
```

### D137: `NNNorm.nnnorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d92a89505c36ed94d23caf93bebbba99b3bc81e96467197a528bee9e0eba28a5`

Type:

```lean
{E : Type u_8} → [self : NNNorm E] → E → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NNNorm E] => self.1
```

### D138: `NNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `490ebc1f72b3ced8506e1bcbd0016d4c351adf097644509fd1dd17a93c4e950f`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
Subtype fun r => Real.instLE.le 0 r
```

### D139: `NNReal.instConditionallyCompleteLinearOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a6df35137b7f52b464ab762b2393c5d6b5cba77a839712e58984b3a00414c3af`

Type:

```lean
ConditionallyCompleteLinearOrderBot NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.conditionallyCompleteLinearOrderBot 0
```

### D140: `NNReal.toReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b78a80825150cf81a49e8914dd12c5dfb7e284ed0e70b3449011ac3d3f49dc66`

Type:

```lean
NNReal → Real
```

Definition body (one-level semantic boundary):

```lean
Subtype.val
```

### D141: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D142: `NonAssocSemiring.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1674e66231d0f66dfe9fae191c7ae33207a78635bcf5490a9cfbb402d16f9bc0`

Type:

```lean
{α : Type u} → [self : NonAssocSemiring α] → NonUnitalNonAssocSemiring α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonAssocSemiring α] => self.1
```

### D143: `NonUnitalNonAssocSemiring.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fc6b0a41257a855dbb5b09cfe7e3150884caf2b0f898b30e688420784d3b6e76`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → AddCommMonoid α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocSemiring α] => self.1
```

### D144: `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing`

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

### D145: `NonUnitalSeminormedRing.toSeminormedAddCommGroup`

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

### D146: `NormedCommRing.toSeminormedCommRing`

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

### D147: `Real.instDivInvMonoid`

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

### D148: `Real.instMin`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d2cd90660c09f0530ecb3d8bd97eb9c8e1ed4fc9eebe2650e6a65a653c99fcb0`

Type:

```lean
Min Real
```

Definition body (one-level semantic boundary):

```lean
{ min := Real.inf✝ }
```

### D149: `Real.norm`

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

### D150: `Real.normedCommRing`

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

### D151: `Real.sqrt`

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

### D152: `SeminormedAddCommGroup.toSeminormedAddGroup`

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

### D153: `SeminormedAddGroup.toNNNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `00d678445c0040ace90f6c4fb7b4afa2098bf365a8f75ab815ec0e6e446166c9`

Type:

```lean
{E : Type u_5} → [SeminormedAddGroup E] → NNNorm E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : SeminormedAddGroup E] => { nnnorm := fun a => ⟨inst.norm a, ⋯⟩ }
```

### D154: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

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

### D155: `Semiring.toNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `33076e5ce1b65d0dacdacdea942f424abbe54f3ff639c158f37c0f533984f227`

Type:

```lean
{α : Type u} → [self : Semiring α] → NonAssocSemiring α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toNonUnitalNonAssocSemiring := self.toNonUnitalNonAssocSemiring, toOne := self.toOne, one_mul := ⋯, mul_one := ⋯,
    toNatCast := self.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯ }
```

### D156: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D157: `instHDiv`

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

### D158: `instSemilatticeSupNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2a6440af851e8806e3c58934c33bb1185e865186dfb38346ffc479f2e156fbfa`

Type:

```lean
SemilatticeSup NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.semilatticeSup
```

### D159: `instSemiringNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3e4e8247feefdb8229f2843910b9a5df0fb872cbeba12353f5c00b1549c1f2b5`

Type:

```lean
Semiring NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.semiring
```

### D160: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D161: `DivInvMonoid.toZPow`

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

### D162: `Fin.val`

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

### D163: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cc2bad5c5cc6aa2b196abe33b9083d127ab69155f1189766c3500bb83412c7df`

Type:

```lean
{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p [DecidablePred p] s => { val := Multiset.filter p s.val, nodup := ⋯ }
```

### D164: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

### D165: `Int.instLEInt`

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

### D166: `LT.lt`

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

### D167: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
```

### D168: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D169: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D170: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D171: `instLENat`

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

### D172: `instLTNat`

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

### D173: `Bool.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `98d460e4da0ec8a7ca3d02bf4c338e01aafaa4536c4a8f107307135e07b476c6`

Type:

```lean
{motive : Bool → Sort u} → (t : Bool) → motive Bool.false → motive Bool.true → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t false true => Bool.rec false true t
```

### D174: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

### D175: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

### D176: `List.foldl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `528cbed637e4ef546b621011d5cf13a5a950202dac919ee6cff2046010954d44`

Type:

```lean
{α : Type u} → {β : Type v} → (α → β → α) → α → List β → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f x x_1 =>
  List.brecOn (motive := fun x => α → α) x_1
    (fun x f_1 x_2 =>
      List.foldl.match_1 (fun x x_3 => List.below (motive := fun x => α → α) x_3 → α) x_2 x (fun a x => a)
        (fun a b l x => x.1 (f a b)) f_1)
    x
```

### D177: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

### D178: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D179: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `31dfcc70f250d68311839281cfb552859ef6a5cdd31e725091d6a2a2f7fb2165`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D180: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a70aebf9da319c4b02023421b33923182c4d5164c2087035016589b80ed1191a`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D181: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D182: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d5a5745fe197b17d74201a2db472f8ca23ff9fdb827ba67a427efe3c5468ae2e`

Type:

```lean
Real → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun r => ⟨Real.instMax.max r 0, ⋯⟩
```

### D183: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D184: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ff90c894e4369b89945915c4c814dd76d90e450369a804cfc4139fada64048b2`

Type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Definition body (one-level semantic boundary):

```lean
fun p [h : Decidable p] => Decidable.casesOn h (fun x => Bool.false) fun x => Bool.true
```

### D185: `List`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `ec06a72bb009eecaedd9dbf6a3349bbea0bbc480e0a21179f4e21b3e219b952d`

Type:

```lean
Type u → Type u
```

### D186: `List.filter`

- Role: `external-frontier`
- Owner module: `Init.Data.List.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `7975b53fb61d3f95cd66b99d3605c0ab38a30a1671157413ddc2342c3a8bd440`

Type:

```lean
{α : Type u} → (α → Bool) → List α → List α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p x =>
  List.brecOn x fun x f =>
    List.getLast?.match_1 (fun x => List.below x → List α) x (fun _ x => List.nil)
      (fun a as x => List.filter.match_1 (fun x => List α) (p a) (fun _ => List.cons a x.1) fun _ => x.1) f
```

### D187: `List.flatten`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `79a988f56f7521caffc6b2f64038b6b22e7bf19e9883f481a7670a16914e2da0`

Type:

```lean
{α : Type u_1} → List (List α) → List α
```

Definition body (one-level semantic boundary):

```lean
fun {α} x =>
  List.brecOn x fun x f =>
    List.flatten.match_1 (fun x => List.below x → List α) x (fun _ x => List.nil) (fun l L x => l.append x.1) f
```

### D188: `List.ofFn`

- Role: `external-frontier`
- Owner module: `Init.Data.List.OfFn`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `e54777dd091df49539c6c1473fd1928ad87f9e135ba5940e57702ecd3f83b095`

Type:

```lean
{α : Type u_1} → {n : Nat} → (Fin n → α) → List α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} f => Fin.foldr n (fun x1 x2 => List.cons (f x1) x2) List.nil
```

### D189: `Matrix.neg`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `1d4a0647aeb637effb2c6c25b5dbf60fa226065a3bcaf43028e168bc24a216b2`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Neg α] → Neg (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Neg α] => Pi.instNeg
```

### D190: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D191: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

### D192: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D193: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D194: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D195: `Nat.decLe`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `931f48339aefbc000a30f94b69a993dd27e00f38323c7b45743dc5d6ffe51c35`

Type:

```lean
(n m : Nat) → Decidable (instLENat.le n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => if h : Eq (n.ble m) Bool.true then Decidable.isTrue ⋯ else Decidable.isFalse ⋯
```

### D196: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```
