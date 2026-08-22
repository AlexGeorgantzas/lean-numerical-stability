# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m n q p : Nat} (semantics : LocalDef001),
  And
    (∀ (run : LocalDef002 m n q p) (a : LocalDef006 semantics run),
      LocalDef007 semantics (LocalDef020 run)
        (LocalDef013
          (LocalDef011 n p (LocalDef019 run.model)
            (LocalDef017 run.model) (LocalDef021 n run.model)
            (LocalDef018 run.model)
            (LocalDef016 run.model))
          run.A run.B))
    (And
      (∀ (run : LocalDef002 m n q p) (a : LocalDef006 semantics run),
        LocalDef007 semantics (LocalDef020 run)
          (instHAdd.hAdd
            (instHAdd.hAdd
              (LocalDef013
                (LocalDef012 n p (LocalDef019 run.model)
                  (LocalDef017 run.model))
                run.A run.B)
              (LocalDef013
                (LocalDef010 n p (LocalDef019 run.model)
                  (LocalDef021 n run.model)
                  (LocalDef018 run.model))
                run.A run.B))
            (LocalDef013
              (LocalDef008 n p (LocalDef021 n run.model)
                (LocalDef016 run.model))
              run.A run.B)))
      (∀ (run : LocalDef002 m n q p),
        And
          (Eq (LocalDef009 p (LocalDef019 run.model))
            (instHMul.hMul
              (instHMul.hMul (instHDiv.hDiv (instHAdd.hAdd p.cast 1) 2)
                (instHPow.hPow (LocalDef019 run.model) (instHSub.hSub p 1)))
              (LocalDef014 (LocalDef019 run.model))))
          (Eq
            (instHMul.hMul n.cast
              (LocalDef010 n p (LocalDef019 run.model)
                (LocalDef021 n run.model)
                (LocalDef018 run.model)))
            (instHMul.hMul (instHPow.hPow (LocalDef019 run.model) (instHSub.hSub p 1))
              (LocalDef015 n (LocalDef021 n run.model)
                (LocalDef018 run.model))))))
```

## Fully explicit elaborated target type

```lean
∀ {m n q p : Nat} (semantics : LocalDef001),
  And
    (∀ (run : LocalDef002 m n q p)
      (a : @LocalDef006 semantics m n q p run),
      LocalDef007 semantics (@LocalDef020 m n q p run)
        (@LocalDef013 m n q
          (LocalDef011 n p
            (LocalDef019 (@LocalDef005 m n q p run))
            (LocalDef017 (@LocalDef005 m n q p run))
            (LocalDef021 n (@LocalDef005 m n q p run))
            (LocalDef018 (@LocalDef005 m n q p run))
            (LocalDef016 (@LocalDef005 m n q p run)))
          (@LocalDef003 m n q p run) (@LocalDef004 m n q p run)))
    (And
      (∀ (run : LocalDef002 m n q p)
        (a : @LocalDef006 semantics m n q p run),
        LocalDef007 semantics (@LocalDef020 m n q p run)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@LocalDef013 m n q
                (LocalDef012 n p
                  (LocalDef019 (@LocalDef005 m n q p run))
                  (LocalDef017 (@LocalDef005 m n q p run)))
                (@LocalDef003 m n q p run) (@LocalDef004 m n q p run))
              (@LocalDef013 m n q
                (LocalDef010 n p
                  (LocalDef019 (@LocalDef005 m n q p run))
                  (LocalDef021 n (@LocalDef005 m n q p run))
                  (LocalDef018 (@LocalDef005 m n q p run)))
                (@LocalDef003 m n q p run) (@LocalDef004 m n q p run)))
            (@LocalDef013 m n q
              (LocalDef008 n p
                (LocalDef021 n (@LocalDef005 m n q p run))
                (LocalDef016 (@LocalDef005 m n q p run)))
              (@LocalDef003 m n q p run) (@LocalDef004 m n q p run))))
      (∀ (run : LocalDef002 m n q p),
        And
          (@Eq.{1} Real
            (LocalDef009 p
              (LocalDef019 (@LocalDef005 m n q p run)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast p)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                  (LocalDef019 (@LocalDef005 m n q p run))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (LocalDef014
                (LocalDef019 (@LocalDef005 m n q p run)))))
          (@Eq.{1} Real
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast n)
              (LocalDef010 n p
                (LocalDef019 (@LocalDef005 m n q p run))
                (LocalDef021 n (@LocalDef005 m n q p run))
                (LocalDef018 (@LocalDef005 m n q p run))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (LocalDef019 (@LocalDef005 m n q p run))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (LocalDef015 n
                (LocalDef021 n (@LocalDef005 m n q p run))
                (LocalDef018
                  (@LocalDef005 m n q p run)))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f2edb688bf24107f4483f8ca3f1a4c1ac22236239f0226d7fabb02affe19d395`

Type:

```lean
Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ba24be371c312a770cc2b9d6fd08a425e600865f5a9f40e91367d729d2a6f04d`

Type:

```lean
Nat → Nat → Nat → Nat → Type
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `468c1a38250f5e60d7883041a0cbef728dfedb248c87c34cca63c2033277fa24`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.4
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fed5b57c9fbe3546a82db9ae27bd3c26be244d7edb4852f05d169347aad35e5e`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.5
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1d0362498066d9e568122beb1d2a6d5af0732f3fd5dd4209d47c6d950f972e62`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef031
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.3
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `8ef8b26342c5a67d4f35c4ac66d27832a84297dcf2c71741a07e32cf87dc8b3b`

Type:

```lean
LocalDef001 → {m n q p : Nat} → LocalDef002 m n q p → Type
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fb2df0faeee47322d20b7cfbcb1484bf8c5ddf88de1becb7ebd3211db8b053bd`

Type:

```lean
LocalDef001 → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D008: `LocalDef008`

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

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d95881c72218c764905e4c1450dd882eda6fa4a4c4a6840f2ec5044e3981f45a`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun p u => instHMul.hMul (instHAdd.hAdd p.cast 1) (instHPow.hPow u p)
```

### D010: `LocalDef010`

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

### D011: `LocalDef011`

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
    (instHAdd.hAdd (LocalDef012 n p u U)
      (LocalDef010 n p u theta gmin))
    (LocalDef008 n p theta Gmin)
```

### D012: `LocalDef012`

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
  instHAdd.hAdd (LocalDef009 p u) (LocalDef038 n p U)
```

### D013: `LocalDef013`

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
  instHMul.hMul (instHMul.hMul coefficient (LocalDef035 A)) (LocalDef035 B)
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c60932f99879417bbf4517e3809066d375e41a167b91753ac7404ac9a619df3`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun u => instHMul.hMul 2 u
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d4d5db82952e69b8eba75f6811724b53957dd863e22ba7f23efe5369e4ed612e`

Type:

```lean
Nat → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n theta gmin =>
  instHMul.hMul (instHMul.hMul (instHMul.hMul 4 (instHPow.hPow n.cast 2)) (Real.instInv.inv theta)) gmin
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `be59dd8ef1d970cdf9b759f6bc31124ac4ee2464b0025c399e48a3512e04b761`

Type:

```lean
LocalDef031 → Real
```

Definition body (one-level semantic boundary):

```lean
fun model =>
  LocalDef041 model.accumulationFormat.precision model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1f2d201bc9ea329e579ca2571abbb2c506bc0fc8c168b258ceed88c1f7d26d2f`

Type:

```lean
LocalDef031 → Real
```

Definition body (one-level semantic boundary):

```lean
fun model => LocalDef042 model.accumulationFormat.precision
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3150ac4d77a8896c28b5d82da04e0c317811db9b9f0fb3d0b459e6b9c10df986`

Type:

```lean
LocalDef031 → Real
```

Definition body (one-level semantic boundary):

```lean
fun model =>
  LocalDef041 model.inputFormat.precision model.inputFormat.minExponent
    model.inputFormat.hasSubnormals
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `80ddb95b2d83a1884156016c43f22b53918369613f62170602658999d2457bac`

Type:

```lean
LocalDef031 → Real
```

Definition body (one-level semantic boundary):

```lean
fun model => LocalDef042 model.inputFormat.precision
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b552ced0f8096390c09f6d0f5081d946ed8484615c8d5203b392d9ece7e640ec`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  LocalDef035
    (instHSub.hSub run.computed (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5954e08cdcea5205c005bfb0dfd5fec31ca5598f313e185555f7586e60a4b286`

Type:

```lean
Nat → LocalDef031 → Real
```

Definition body (one-level semantic boundary):

```lean
fun n model =>
  LocalDef039 n (LocalDef037 model.inputFormat.precision model.inputFormat.maxExponent)
    (LocalDef037 model.accumulationFormat.precision model.accumulationFormat.maxExponent)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `dbf09d0197efd4fe3f1be1c3f41753166e84f54c3537c5d7364e0a21e1d9f270`

Type:

```lean
(secondOrder : Real → Prop) →
  secondOrder 0 →
    (∀ {x y : Real}, secondOrder x → secondOrder y → secondOrder (instHAdd.hAdd x y)) →
      (∀ {x : Real}, secondOrder x → secondOrder (abs x)) → LocalDef001
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `90968f60e8ad6d3748a0e2bfbd73b1389fd62502d40766d62f235ae7d5eb02e9`

Type:

```lean
LocalDef001 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D024: `LocalDef024`

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

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `12d262b8446cf7c6c47cb88687060cc62a00722a9508d327962a662efd9fa79e`

Type:

```lean
LocalDef043 → Bool
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3c88de1e2276413265f331b9b7d8c2e0e4e7b3d4c91dfe03084b3b00515ee6e7`

Type:

```lean
LocalDef043 → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `413ce9de7a00001e543ad2ad3103cdb39776dd2cd71dcee21c387e1520ef9a57`

Type:

```lean
LocalDef043 → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c756b1b4a4cf8e4c5892149c99b4ad6dafffb8b7aafaaaa18142341087a4c719`

Type:

```lean
LocalDef043 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2196fbb59e3bffa94526c4b8102e9dc3ef8f6f35b0e8ceaf79b3dbc1df72e541`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.20
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e102e7d20abfbe2da70a388f4912adaae5600d0741ad787277ae7769e746cb81`

Type:

```lean
{m n q p : Nat} →
  And (instLTNat.lt 0 m) (And (instLTNat.lt 0 n) (instLTNat.lt 0 q)) →
    instLTNat.lt 0 p →
      (model : LocalDef031) →
        (A : LocalDef024 m n) →
          (B : LocalDef024 n q) →
            (rowScale : Fin m → Real) →
              (columnScale : Fin q → Real) →
                (∀ (i : Fin m),
                    LocalDef050 (LocalDef021 n model)
                      (LocalDef049 (A i)) (rowScale i)) →
                  (∀ (j : Fin q),
                      LocalDef050 (LocalDef021 n model)
                        (LocalDef049 fun i => B i j) (columnScale j)) →
                    (∀ (i : Fin m) (j : Fin n),
                        Real.instLE.le (abs (LocalDef055 rowScale A i j))
                          (LocalDef021 n model)) →
                      (∀ (i : Fin n) (j : Fin q),
                          Real.instLE.le (abs (LocalDef054 B columnScale i j))
                            (LocalDef021 n model)) →
                        (Aword : Fin p → LocalDef024 m n) →
                          (Bword : Fin p → LocalDef024 n q) →
                            (∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                Eq (Aword i row col)
                                  (model.inputRound
                                    (instHDiv.hDiv
                                      (instHSub.hSub (LocalDef055 rowScale A row col)
                                        ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                          instHMul.hMul
                                            (instHPow.hPow (LocalDef019 model) k.val)
                                            (Aword k row col)))
                                      (instHPow.hPow (LocalDef019 model) i.val)))) →
                              (∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                  model.inputNoOverflow
                                    (instHDiv.hDiv
                                      (instHSub.hSub (LocalDef055 rowScale A row col)
                                        ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                          instHMul.hMul
                                            (instHPow.hPow (LocalDef019 model) k.val)
                                            (Aword k row col)))
                                      (instHPow.hPow (LocalDef019 model) i.val))) →
                                (∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                    Eq (Bword i row col)
                                      (model.inputRound
                                        (instHDiv.hDiv
                                          (instHSub.hSub (LocalDef054 B columnScale row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (LocalDef019 model) k.val)
                                                (Bword k row col)))
                                          (instHPow.hPow (LocalDef019 model) i.val)))) →
                                  (∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                      model.inputNoOverflow
                                        (instHDiv.hDiv
                                          (instHSub.hSub (LocalDef054 B columnScale row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (LocalDef019 model) k.val)
                                                (Bword k row col)))
                                          (instHPow.hPow (LocalDef019 model) i.val))) →
                                    (∀ (i j : Fin p),
                                        instLTNat.lt (instHAdd.hAdd i.val j.val) p →
                                          ∀ (row : Fin m) (col : Fin q),
                                            LocalDef061 model (Aword i row) fun k =>
                                              Bword j k col) →
                                      (∀ (row : Fin m) (col : Fin q),
                                          LocalDef053 model.accumulationNoOverflow
                                            model.accumulationRound 0
                                            (List.map
                                              (fun pair =>
                                                instHMul.hMul
                                                  (instHPow.hPow (LocalDef019 model)
                                                    (instHAdd.hAdd pair.fst.val pair.snd.val))
                                                  (LocalDef057 model
                                                    (Aword pair.fst row) fun k => Bword pair.snd k col))
                                              (LocalDef052 p))) →
                                        (computed : LocalDef024 m q) →
                                          Eq computed
                                              (LocalDef068 rowScale columnScale
                                                (LocalDef065 model
                                                  (LocalDef019 model) Aword Bword)) →
                                            LocalDef002 m n q p
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6926c389e89ca6de69ecf72b7cc3ec994fee507a58e514b84a256962788d624a`

Type:

```lean
Type
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9710afba4fc16094d33288533455f23ceb0965aa0c1da86015ff26e74464c33d`

Type:

```lean
LocalDef031 → LocalDef043
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a58d40257980f41d770cde074cf877dcc7ebc6731c42b3c939d5baea529f07de`

Type:

```lean
LocalDef031 → LocalDef043
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e1e4e0e04fecdf93a41d27d76443f5cfdcae65e0e4f365de5bfc15d2cc71b18f`

Type:

```lean
{semantics : LocalDef001} →
  {m n q p : Nat} →
    {run : LocalDef002 m n q p} →
      (AError : LocalDef024 m n) →
        (BError : LocalDef024 n q) →
          Eq run.A (instHAdd.hAdd (LocalDef056 run) AError) →
            Eq run.B (instHAdd.hAdd (LocalDef059 run) BError) →
              Real.instLE.le (LocalDef035 AError)
                  (instHMul.hMul (LocalDef066 run) (LocalDef035 run.A)) →
                Real.instLE.le (LocalDef035 BError)
                    (instHMul.hMul (LocalDef066 run) (LocalDef035 run.B)) →
                  Eq (LocalDef060 run)
                      (instHSub.hSub
                        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (LocalDef056 run)
                          (LocalDef059 run))
                        (LocalDef063 run)) →
                    (omittedRemainder : Real) →
                      semantics.secondOrder omittedRemainder →
                        Real.instLE.le (LocalDef035 (LocalDef063 run))
                            (instHAdd.hAdd
                              (LocalDef013
                                (LocalDef062 p
                                  (LocalDef019 run.model))
                                run.A run.B)
                              (abs omittedRemainder)) →
                          (accumulationRemainder : Real) →
                            semantics.secondOrder accumulationRemainder →
                              (underflowCount : Nat) →
                                Real.instLE.le underflowCount.cast
                                    (instHDiv.hDiv
                                      (instHMul.hMul (instHMul.hMul n.cast p.cast) (instHAdd.hAdd p.cast 1)) 2) →
                                  Real.instLE.le
                                      (LocalDef035 (LocalDef058 run))
                                      (instHAdd.hAdd
                                        (LocalDef013
                                          (LocalDef064 n p underflowCount
                                            (LocalDef017 run.model)
                                            (LocalDef021 n run.model)
                                            (LocalDef016 run.model))
                                          run.A run.B)
                                        (abs accumulationRemainder)) →
                                    semantics.secondOrder
                                        (instHMul.hMul
                                          (instHMul.hMul (instHPow.hPow (LocalDef066 run) 2)
                                            (LocalDef035 run.A))
                                          (LocalDef035 run.B)) →
                                      LocalDef006 semantics run
```

### D035: `LocalDef035`

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

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `2ce92de675040573a86bb56eb1810ec5f97d8bfda24fdbdb86d7ca409b945411`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e812122843a7693eb9da20df127bdfd0b036f7eb87b5291df77467d35da85027`

Type:

```lean
Nat → Int → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision maxExponent =>
  instHMul.hMul (instHPow.hPow 2 maxExponent)
    (instHSub.hSub 2 (instHMul.hMul 2 (LocalDef042 precision)))
```

### D038: `LocalDef038`

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

### D039: `LocalDef039`

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

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `8a85a65264d1eaf6bf92eb9238ef21e86787b07b20e078bcd23e3fd0e91d4fbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `98e39d9e9f622feb1800dc6ed026db533af44c2455719d25e42c991fb6e6b98f`

Type:

```lean
Nat → Int → Bool → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision minExponent hasSubnormals =>
  LocalDef067 (fun hasSubnormals => Real) hasSubnormals
    (fun _ => instHDiv.hDiv (LocalDef051 minExponent) 2) fun _ =>
    instHMul.hMul (LocalDef042 precision) (LocalDef051 minExponent)
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `374e1e67fe075ea077dd0ca7e1b7b13a7719c0f4c5d32224c3e123b307030749`

Type:

```lean
Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun precision => instHPow.hPow (Real.instInv.inv 2) precision
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d7413b73a7ad69b98dc5442ebbbdc88576a9ef3d0d454547165fca6c44972bc9`

Type:

```lean
Type
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `792791a0867cbfa46f9a7bcd3765f1203d4a225c1225c66e1176d42ea3b58e4b`

Type:

```lean
LocalDef031 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.18
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `30ce35c54c896a4931f5255243d743ec3e934999f96f263246c7f00444561ea7`

Type:

```lean
LocalDef031 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.15
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `55b414c88463908661427fe77d14587a93f88c903944710a5ba2422cde1f5bce`

Type:

```lean
LocalDef031 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `581ec48f5ff9f0fa3720a20c607b6d4aa2055ef843a6dc3aac38e32b201be5d4`

Type:

```lean
LocalDef031 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e28717a002a95568b89c776278fcaa0f6885dfbd6cd67f0dbf0a18e27e67f82d`

Type:

```lean
(inputFormat accumulationFormat : LocalDef043) →
  instLENat.le inputFormat.precision accumulationFormat.precision →
    And (Int.instLEInt.le accumulationFormat.minExponent inputFormat.minExponent)
        (Int.instLEInt.le inputFormat.maxExponent accumulationFormat.maxExponent) →
      (inputRound inputDelta inputEta : Real → Real) →
        (inputNoOverflow : Real → Prop) →
          (∀ {x : Real},
              inputNoOverflow x →
                Eq (inputRound x) (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (inputDelta x))) (inputEta x))) →
            (∀ {x : Real},
                inputNoOverflow x →
                  Real.instLE.le (abs (inputDelta x)) (LocalDef042 inputFormat.precision)) →
              (∀ {x : Real},
                  inputNoOverflow x →
                    Real.instLE.le (abs (inputEta x))
                      (LocalDef041 inputFormat.precision inputFormat.minExponent
                        inputFormat.hasSubnormals)) →
                (∀ {x : Real}, inputNoOverflow x → Eq (instHMul.hMul (inputEta x) (inputDelta x)) 0) →
                  (∀ {x : Real}, inputNoOverflow x → LocalDef077 inputFormat (inputRound x)) →
                    (∀ {x : Real},
                        inputNoOverflow x →
                          ∀ {y : Real},
                            LocalDef077 inputFormat y →
                              Real.instLE.le (abs (instHSub.hSub (inputRound x) x)) (abs (instHSub.hSub y x))) →
                      (accumulationRound accumulationDelta accumulationEta : Real → Real) →
                        (accumulationNoOverflow : Real → Prop) →
                          (∀ {x : Real},
                              accumulationNoOverflow x →
                                Eq (accumulationRound x)
                                  (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (accumulationDelta x)))
                                    (accumulationEta x))) →
                            (∀ {x : Real},
                                accumulationNoOverflow x →
                                  Real.instLE.le (abs (accumulationDelta x))
                                    (LocalDef042 accumulationFormat.precision)) →
                              (∀ {x : Real},
                                  accumulationNoOverflow x →
                                    Real.instLE.le (abs (accumulationEta x))
                                      (LocalDef041 accumulationFormat.precision
                                        accumulationFormat.minExponent accumulationFormat.hasSubnormals)) →
                                (∀ {x : Real},
                                    accumulationNoOverflow x →
                                      Eq (instHMul.hMul (accumulationEta x) (accumulationDelta x)) 0) →
                                  (∀ {x : Real},
                                      accumulationNoOverflow x →
                                        LocalDef077 accumulationFormat (accumulationRound x)) →
                                    (∀ {x : Real},
                                        accumulationNoOverflow x →
                                          ∀ {y : Real},
                                            LocalDef077 accumulationFormat y →
                                              Real.instLE.le (abs (instHSub.hSub (accumulationRound x) x))
                                                (abs (instHSub.hSub y x))) →
                                      LocalDef031
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `87f59ddda7d28f2342745750052393a1a7f8e6da20099629ce901b53ae3a06a8`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sup fun i => (abs (x i)).toNNReal).toReal
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `fb4c39249333a2b6fcc41db880a13b76bb70b92044a24ec0042af3b1053ddfc8`

Type:

```lean
Real → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun theta vectorNorm lambda =>
  And (LocalDef074 lambda)
    (And (Real.instLT.lt 0 lambda)
      (Or (And (Eq vectorNorm 0) (Eq lambda 1))
        (And (Real.instLT.lt 0 vectorNorm)
          (And (Real.instLT.lt (instHDiv.hDiv theta (instHMul.hMul 2 vectorNorm)) lambda)
            (Real.instLE.le lambda (instHDiv.hDiv theta vectorNorm))))))
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1ea1d99687f61140e8592b6154c5c66bbde2de8d842aa90e456007cea8d43fd`

Type:

```lean
Int → Real
```

Definition body (one-level semantic boundary):

```lean
fun minExponent => instHPow.hPow 2 minExponent
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ef4652e0c2e1640d530cf6710ae7278192d50051447ff1d9be584eb64523f8c6`

Type:

```lean
(Real → Prop) → (Real → Real) → Real → List Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun allowed round x x_1 =>
  List.brecOn (motive := fun x => Real → Prop) x_1
    (fun x f x_2 =>
      LocalDef076 (fun x x_3 => List.below (motive := fun x => Real → Prop) x_3 → Prop) x_2 x
        (fun x x_3 => True)
        (fun acc term terms x => And (allowed (instHAdd.hAdd acc term)) (x.1 (round (instHAdd.hAdd acc term)))) f)
    x
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `378c6beb84502e2b56ff224e26171be0f80b1263c8d574e611b959c865a7073f`

Type:

```lean
{n q : Nat} → LocalDef024 n q → (Fin q → Real) → LocalDef024 n q
```

Definition body (one-level semantic boundary):

```lean
fun {n q} B mu i j => instHMul.hMul (B i j) (mu j)
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `00f5599a51f7504fa6af21fe5f75dbc8584462339602b0cca6a3d151edb4518f`

Type:

```lean
{m n : Nat} → (Fin m → Real) → LocalDef024 m n → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n} lambda A i j => instHMul.hMul (lambda i) (A i j)
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0e0f486722ff384ea34107ffa26498e71af4645286429f5f234df17729d8b5a7`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run row col =>
  instHMul.hMul (Real.instInv.inv (run.rowScale row))
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (LocalDef019 run.model) i.val) (run.Aword i row col))
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7694ab016120f5516b7fce6f06868c55c1af80a1aa4bf4253858ce04d6223930`

Type:

```lean
{n : Nat} → LocalDef031 → (Fin n → Real) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} model x y =>
  LocalDef075 model.accumulationRound 0
    (List.ofFn fun k => model.accumulationRound (instHMul.hMul (x k) (y k)))
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1577b835eba37e370548479c898404775a0902ad0069a56f41aa9f3565d7bb2c`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run => instHSub.hSub run.computed (LocalDef060 run)
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2f8c2d65ade2544bc24af7ce29a4a2b5816ae2e9d8239fc50d0fc311eb8978b4`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 n q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run row col =>
  instHMul.hMul
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (LocalDef019 run.model) i.val) (run.Bword i row col))
    (Real.instInv.inv (run.columnScale col))
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `22f40f502167ac4b00ae6f40b7b33ed05dde5f4c44e0911d67dab0206a2f10c8`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  LocalDef068 run.rowScale run.columnScale fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLTNat.lt (instHAdd.hAdd i.val j.val) p) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (LocalDef019 run.model) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword i) (run.Bword j) row col)
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `826f363b00afc08e02a6843a96669eb3ec223a021fc6c250ed72b37cfb9f4988`

Type:

```lean
{n : Nat} → LocalDef031 → (Fin n → Real) → (Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} model x y =>
  And (∀ (k : Fin n), model.accumulationNoOverflow (instHMul.hMul (x k) (y k)))
    (LocalDef053 model.accumulationNoOverflow model.accumulationRound 0
      (List.ofFn fun k => model.accumulationRound (instHMul.hMul (x k) (y k))))
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f40c81263b16e163be93b5a74357ea09663500c87ccab8155f44bd89ac105369`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun p u => instHMul.hMul (instHSub.hSub p.cast 1) (instHPow.hPow u p)
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e63b52b6e9b34a52d7dcde8d4121a419422c18542572b9880eb02ece7269de59`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  LocalDef068 run.rowScale run.columnScale fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLENat.le p (instHAdd.hAdd i.val j.val)) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (LocalDef019 run.model) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword i) (run.Bword j) row col)
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eaff75a0cc696245109bca9bace81ab709304742ac9d8f6c1c95a60c2454824d`

Type:

```lean
Nat → Nat → Nat → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p r U theta Gmin =>
  instHAdd.hAdd (LocalDef038 n p U)
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 r.cast) n.cast) (instHPow.hPow (Real.instInv.inv theta) 2)) Gmin)
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ee70783f1d6e5a142a213041aa5270117b093930097e0a161da488219ad6b0de`

Type:

```lean
{m n q p : Nat} →
  LocalDef031 →
    Real → (Fin p → LocalDef024 m n) → (Fin p → LocalDef024 n q) → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} model u Aword Bword row col =>
  LocalDef075 model.accumulationRound 0
    (List.map
      (fun pair =>
        instHMul.hMul (instHPow.hPow u (instHAdd.hAdd pair.fst.val pair.snd.val))
          (LocalDef057 model (Aword pair.fst row) fun k => Bword pair.snd k col))
      (LocalDef052 p))
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `de625bb90558acf72843b146c44cb09d35d2e55aabac33910a5f6883282d633b`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  Real.instMax.max (instHPow.hPow (LocalDef019 run.model) p)
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 2 n.cast)
          (instHPow.hPow (LocalDef019 run.model) (instHSub.hSub p 1)))
        (Real.instInv.inv (LocalDef021 n run.model)))
      (LocalDef018 run.model))
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f39885f324faf09cbe5e6c2bd4eae850670ec539979d0b37aaed2094bab7cc7b`

Type:

```lean
{m q : Nat} → (Fin m → Real) → (Fin q → Real) → LocalDef024 m q → LocalDef024 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m q} lambda mu C i j =>
  instHMul.hMul (instHMul.hMul (Real.instInv.inv (lambda i)) (C i j)) (Real.instInv.inv (mu j))
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `327623ce0696f27f1520d6987cb953a91fd0d381eab547d1bd9d47de7b854468`

Type:

```lean
(precision : Nat) →
  (minExponent maxExponent : Int) →
    Bool → instLTNat.lt 0 precision → Int.instLEInt.le minExponent maxExponent → LocalDef043
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `704b5129a62de10dcd80ae4e388e2249991e1ae57e4948ec33d70fa76e89e3ca`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Fin p → LocalDef024 m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.12
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `50da6318ea901b4de20c795c1f3ba1b168b5199e129c492e05e8df03a5c0c8d1`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Fin p → LocalDef024 n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.13
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fb35b2c6920810782d711a24f2636b1017ea41f3b1bc5ff1f438608646c842eb`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Fin q → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.7
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cc1128f2d7fe9d22934381d2a1173b38d73cad49999866a08a1b3e937d618600`

Type:

```lean
{m n q p : Nat} → LocalDef002 m n q p → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.6
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cdbc02ca950134eb20d94e5488f66c176cc912c7aa24e523ded6bd5ee37e98e5`

Type:

```lean
Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun lambda => Exists fun exponent => Eq lambda (instHPow.hPow 2 exponent)
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b9ac3455dcf1dc9cf70fa61923440b2e2fe716dcf75ba3b524efa0a03bdae462`

Type:

```lean
(Real → Real) → Real → List Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun round x x_1 =>
  List.brecOn (motive := fun x => Real → Real) x_1
    (fun x f x_2 =>
      LocalDef076 (fun x x_3 => List.below (motive := fun x => Real → Real) x_3 → Real) x_2 x
        (fun acc x => acc) (fun acc term terms x => x.1 (round (instHAdd.hAdd acc term))) f)
    x
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `88e8fa9f2ed16f52b7ea53a3c38334c38387acfcf116f81b9b628eb5a947ab55`

Type:

```lean
(motive : Real → List Real → Sort u_1) →
  (x : Real) →
    (x_1 : List Real) →
      ((acc : Real) → motive acc List.nil) →
        ((acc term : Real) → (terms : List Real) → motive acc (List.cons term terms)) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 => List.casesOn x_1 (h_1 x) fun head tail => h_2 x head tail
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `15f338e77ee36f1975190ab90fa08bcc2dec8f8985f1febc2baa471abcca6d8b`

Type:

```lean
LocalDef043 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun format x =>
  Or (Eq x 0)
    (Exists fun sign =>
      And (Or (Eq sign 1) (Eq sign (-1)))
        (Exists fun significand =>
          Exists fun exponent =>
            And
              (Eq x
                (instHMul.hMul (instHMul.hMul sign significand.cast)
                  (instHPow.hPow 2 (instHSub.hSub exponent (instHSub.hSub format.precision 1).cast))))
              (Or
                (And (instLENat.le (instHPow.hPow 2 (instHSub.hSub format.precision 1)) significand)
                  (And (instLTNat.lt significand (instHPow.hPow 2 format.precision))
                    (And (Int.instLEInt.le format.minExponent exponent)
                      (Int.instLEInt.le exponent format.maxExponent))))
                (And (Eq format.hasSubnormals Bool.true)
                  (And (Eq exponent format.minExponent)
                    (And (instLTNat.lt 0 significand)
                      (instLTNat.lt significand (instHPow.hPow 2 (instHSub.hSub format.precision 1)))))))))
```

### D078: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D079: `DivInvMonoid.toDiv`

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

### D080: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D081: `HAdd.hAdd`

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

### D082: `HDiv.hDiv`

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

### D083: `HMul.hMul`

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

### D084: `HPow.hPow`

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

### D085: `HSub.hSub`

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

### D086: `Monoid.toNatPow`

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

### D087: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D088: `Nat.cast`

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

### D089: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D090: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D091: `OfNat.ofNat`

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

### D092: `One.toOfNat1`

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

### D095: `Real.instDivInvMonoid`

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

### D096: `Real.instMonoid`

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

### D097: `Real.instMul`

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

### D098: `Real.instNatCast`

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

### D099: `Real.instOne`

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

### D100: `instHAdd`

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

### D101: `instHDiv`

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

### D102: `instHMul`

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

### D103: `instHPow`

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

### D104: `instHSub`

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

### D105: `instOfNatAtLeastTwo`

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

### D106: `instOfNatNat`

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

### D107: `instSubNat`

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

### D108: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D109: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D110: `Fin.fintype`

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

### D111: `Inv.inv`

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

### D112: `LE.le`

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

### D113: `Matrix`

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

### D114: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

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

### D115: `Matrix.sub`

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

### D116: `Real.instAddCommMonoid`

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

### D117: `Real.instAddGroup`

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

### D118: `Real.instInv`

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

### D119: `Real.instLE`

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

### D123: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D124: `ConditionallyCompleteLinearOrderBot.toOrderBot`

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

### D125: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1e8b6758b3a3bf88b78eeff1bb4effb1dce39e6b9e38153dab79b664d58d89b5`

Type:

```lean
{M : Type u_2} → [DivInvMonoid M] → Pow M Int
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : DivInvMonoid M] => { pow := fun x n => inst.zpow n x }
```

### D126: `Fin.val`

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

### D127: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cc2bad5c5cc6aa2b196abe33b9083d127ab69155f1189766c3500bb83412c7df`

Type:

```lean
{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p [DecidablePred p] s => { val := Multiset.filter p s.val, nodup := ⋯ }
```

### D128: `Finset.sum`

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

### D129: `Finset.sup`

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

### D130: `Finset.univ`

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

### D131: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

### D132: `LT.lt`

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

### D133: `List.map`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `509306b13208ac7c4830c43f93dc873d045ae0ae6b1984beea3ee3ecf89cb205`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f x =>
  List.brecOn x fun x f_1 =>
    instDecidableEqList.match_1 (fun x => List.below x → List β) x (fun _ x => List.nil)
      (fun a as x => List.cons (f a) x.1) f_1
```

### D134: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D135: `Min.min`

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

### D136: `NNNorm.nnnorm`

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

### D137: `NNReal`

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

### D138: `NNReal.instConditionallyCompleteLinearOrderBot`

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

### D139: `NNReal.toReal`

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

### D140: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D141: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
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

### D147: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D148: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `31dfcc70f250d68311839281cfb552859ef6a5cdd31e725091d6a2a2f7fb2165`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D149: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a70aebf9da319c4b02023421b33923182c4d5164c2087035016589b80ed1191a`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D150: `Real.instMin`

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

### D151: `Real.instZero`

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

### D152: `Real.normedCommRing`

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

### D153: `Real.sqrt`

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

### D154: `SeminormedAddCommGroup.toSeminormedAddGroup`

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

### D155: `SeminormedAddGroup.toNNNorm`

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

### D156: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

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

### D157: `Semiring.toNonAssocSemiring`

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

### D158: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D159: `Zero.toOfNat0`

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

### D160: `instAddNat`

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

### D161: `instLTNat`

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

### D162: `instSemilatticeSupNNReal`

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

### D163: `instSemiringNNReal`

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

### D164: `Bool.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `98d460e4da0ec8a7ca3d02bf4c338e01aafaa4536c4a8f107307135e07b476c6`

Type:

```lean
{motive : Bool → Sort u} → (t : Bool) → motive Bool.false → motive Bool.true → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t false true => Bool.rec false true t
```

### D165: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

### D166: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

### D167: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ff90c894e4369b89945915c4c814dd76d90e450369a804cfc4139fada64048b2`

Type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Definition body (one-level semantic boundary):

```lean
fun p [h : Decidable p] => Decidable.casesOn h (fun x => Bool.false) fun x => Bool.true
```

### D168: `Int.instLEInt`

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

### D169: `List`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `ec06a72bb009eecaedd9dbf6a3349bbea0bbc480e0a21179f4e21b3e219b952d`

Type:

```lean
Type u → Type u
```

### D170: `List.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ee953aef3cdd9f3df3ef9486761906c6ea0dc0de50785a6d5c06dd73fd337b6a`

Type:

```lean
{α : Type u} → {motive : List α → Sort u_1} → List α → Sort (max (u + 1) u_1)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t => List.rec PUnit (fun head tail tail_ih => PProd (motive tail) tail_ih) t
```

### D171: `List.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `dc2fe7ac5b6c6e21a42444bdb2a571336ead421bcc514f9ad3cb9d7691262fb6`

Type:

```lean
{α : Type u} → {motive : List α → Sort u_1} → (t : List α) → ((t : List α) → List.below t → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t F_1 => (List.brecOn.go t F_1).1
```

### D172: `List.cons`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `d4f0bc0954b11abbe9f8e60dd8762e7797f488b1975b155440101828c4c1ea14`

Type:

```lean
{α : Type u} → α → List α → List α
```

### D173: `List.filter`

- Role: `external-frontier`
- Owner module: `Init.Data.List.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D174: `List.flatten`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D175: `List.nil`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `6fc023f8c03f1dc78130598a9c55a666564e22fa908127753ee95d45e602196f`

Type:

```lean
{α : Type u} → List α
```

### D176: `List.ofFn`

- Role: `external-frontier`
- Owner module: `Init.Data.List.OfFn`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `e54777dd091df49539c6c1473fd1928ad87f9e135ba5940e57702ecd3f83b095`

Type:

```lean
{α : Type u_1} → {n : Nat} → (Fin n → α) → List α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} f => Fin.foldr n (fun x1 x2 => List.cons (f x1) x2) List.nil
```

### D177: `Max.max`

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

### D178: `Nat.decLe`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `931f48339aefbc000a30f94b69a993dd27e00f38323c7b45743dc5d6ffe51c35`

Type:

```lean
(n m : Nat) → Decidable (instLENat.le n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => if h : Eq (n.ble m) Bool.true then Decidable.isTrue ⋯ else Decidable.isFalse ⋯
```

### D179: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

### D180: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

### D181: `Real.instLT`

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

### D182: `Real.instMax`

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

### D183: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d5a5745fe197b17d74201a2db472f8ca23ff9fdb827ba67a427efe3c5468ae2e`

Type:

```lean
Real → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun r => ⟨Real.instMax.max r 0, ⋯⟩
```

### D184: `True`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `151888ac453f6815e1022e38f8b589caefb03395ffd196a9f58c1de8920fa6e1`

Type:

```lean
Prop
```

### D185: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D186: `instLENat`

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

### D187: `Int.instSub`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `cdec027f4b1a52ca9841248e8efbabc901ed4e9b4220aa4074044d4c9537c68c`

Type:

```lean
Sub Int
```

Definition body (one-level semantic boundary):

```lean
{ sub := Int.sub }
```

### D188: `List.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `6d65021c92e6afd6b33fb172f3e220af64038e7d537976362e8538c7a690ea48`

Type:

```lean
{α : Type u} →
  {motive : List α → Sort u_1} →
    (t : List α) → motive List.nil → ((head : α) → (tail : List α) → motive (List.cons head tail)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t nil cons => List.rec nil (fun head tail tail_ih => cons head tail) t
```

### D189: `Nat.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `de0cbde8dd75c1a0c6d5d08b9cfa1cd5908aeb874409a1c880c9c9616deb1709`

Type:

```lean
Monoid Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D190: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D191: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D192: `instNatCastInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7fb46bceee4f1142c75008c8ac4be64c11c4bdbc7972ff89c0a5335ad80a2033`

Type:

```lean
NatCast Int
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => Int.ofNat n }
```
