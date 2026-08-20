# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m : Nat} {Ω : Type u_1} [inst : Fintype Ω] (run : LocalDef006 m Ω),
  Ne (LocalDef009 run.a) 0 →
    ∀ (lambda : Real),
      Real.instLT.lt 0 lambda →
        Real.instLT.lt lambda 1 →
          Real.instLE.le (instHSub.hSub 1 lambda)
            (LocalDef008 run.probability
              (setOf fun ω =>
                Real.instLE.le
                  (instHDiv.hDiv
                    (abs
                      (instHSub.hSub (LocalDef011 run.a fun k => run.delta k ω)
                        (LocalDef009 run.a)))
                    (abs (LocalDef009 run.a)))
                  (instHMul.hMul (LocalDef012 run.a)
                    (instHSub.hSub
                      (instHAdd.hAdd
                        (instHDiv.hDiv (LocalDef010 m (instHPow.hPow (LocalDef013 run.p) 2))
                            lambda).sqrt
                        (LocalDef010 m
                          (instHAdd.hAdd (LocalDef013 run.p)
                            (LocalDef013 (instHAdd.hAdd run.p run.r)))))
                      (LocalDef010 m (LocalDef013 run.p))))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} {Ω : Type u_1} [inst : Fintype.{u_1} Ω] (run : @LocalDef006.{u_1} m Ω inst)
  (hsum :
    @Ne.{1} Real
      (@LocalDef009
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@LocalDef001.{u_1} m Ω inst
          (@LocalDef007.{u_1} m Ω inst run)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (lambda : Real)
  (hlambda_pos :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lambda)
  (hlambda_lt_one :
    @LT.lt.{0} Real Real.instLT lambda (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
    (@LocalDef008.{u_1} Ω inst
      (@LocalDef004.{u_1} m Ω inst
        (@LocalDef007.{u_1} m Ω inst run))
      (@setOf.{u_1} Ω fun (ω : Ω) =>
        @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@LocalDef011 m
                  (@LocalDef001.{u_1} m Ω inst
                    (@LocalDef007.{u_1} m Ω inst run))
                  fun (k : Fin m) =>
                  @LocalDef002.{u_1} m Ω inst
                    (@LocalDef007.{u_1} m Ω inst run) k
                    ω)
                (@LocalDef009
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@LocalDef001.{u_1} m Ω inst
                    (@LocalDef007.{u_1} m Ω inst
                      run)))))
            (@abs.{0} Real Real.lattice Real.instAddGroup
              (@LocalDef009
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@LocalDef001.{u_1} m Ω inst
                  (@LocalDef007.{u_1} m Ω inst run)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@LocalDef012
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LocalDef001.{u_1} m Ω inst
                (@LocalDef007.{u_1} m Ω inst run)))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (LocalDef010 m
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                        (LocalDef013
                          (@LocalDef003.{u_1} m Ω inst
                            (@LocalDef007.{u_1} m Ω inst
                              run)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    lambda))
                (LocalDef010 m
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (LocalDef013
                      (@LocalDef003.{u_1} m Ω inst
                        (@LocalDef007.{u_1} m Ω inst
                          run)))
                    (LocalDef013
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@LocalDef003.{u_1} m Ω inst
                          (@LocalDef007.{u_1} m Ω inst
                            run))
                        (@LocalDef005.{u_1} m Ω inst
                          (@LocalDef007.{u_1} m Ω inst
                            run)))))))
              (LocalDef010 m
                (LocalDef013
                  (@LocalDef003.{u_1} m Ω inst
                    (@LocalDef007.{u_1} m Ω inst
                      run))))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e50cfccf69dab2200459c7b74d24519fdd75a6840c847029aeb9d20f5a6bca0e`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → LocalDef016 m Ω → Fin (instHAdd.hAdd m 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.6
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5e28f16149b568261491969bc0508e984b4bc02e17efe5111be77b1fc848e02f`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → LocalDef016 m Ω → Fin m → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.7
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4b1bd1650658fb1e16d1132aaeffd9eceb794491263e09494ae574b85b83e4e2`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → LocalDef016 m Ω → Nat
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.2
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b0371bd5bae152cc489cceecaa14f2f1e20aa725fa021fdd17c221532b1c48b8`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → LocalDef016 m Ω → LocalDef014 Ω
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.1
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1a1252dd1f75472f55596d2ab59186740870c583d8da51c043f12fb95ffe1038`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → LocalDef016 m Ω → Nat
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.3
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ea33f0b6b2fd7fc01fc69e58d8d53bc63bda63f6d20085fdbc47dc579a6752b5`

Type:

```lean
Nat → (Ω : Type u_1) → [Fintype Ω] → Type u_1
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c3e1129c61e5a7d4e702f8344ebc736eb24ebd78b00f380cee16e8012559459a`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → LocalDef006 m Ω → LocalDef016 m Ω
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.1
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ede349ac6e2be7773e1e3d332fa662acecc14a263f8143eec3791e9e016534b2`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → LocalDef014 Ω → Set Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [Fintype Ω] P E => Finset.univ.sum fun ω => ite (Set.instMembership.mem E ω) (P.prob ω) 0
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `848417c7f33279dafd13c76e57c16d106352e6d30f31556f926cf1df05292c9f`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a => Finset.univ.sum fun i => a i
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b618e3f80d471499c2e719ece1298451cd8b322884851dc6e31f84efc4bffba9`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun n u => instHSub.hSub (instHPow.hPow (instHAdd.hAdd 1 u) n) 1
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `db5a2e19747e9a6d254bee6309e21c422212116f4b169ea1a3f6280382091206`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta =>
  Fin.foldl m (fun acc k => instHMul.hMul (instHAdd.hAdd acc (a k.succ)) (instHAdd.hAdd 1 (delta k))) (a 0)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fc08de23529c01f8faa80a18a0d4ed5a7e469e253e5a60e2f2665e0187753fd9`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a => instHDiv.hDiv (Finset.univ.sum fun i => abs (a i)) (abs (LocalDef009 a))
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2e1b884518fe748bc9c633d226f6ce911dc8b29df0c965e62309ecbe8fe0c3fc`

Type:

```lean
Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun p => instHPow.hPow (1 / 2) (instHSub.hSub p 1)
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cdc6900d6b44706c8faf4d7e391274862067cb6d95b1131a47b2560a766d95d3`

Type:

```lean
(Ω : Type u_1) → [Fintype Ω] → Type u_1
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3636c9f4d2f36ba03c4caf5f0ddd2ad616a29ee70ad7e10bc918a28de663df17`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → LocalDef014 Ω → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun Ω [Fintype Ω] self => self.1
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ace3179ccf30cf04c14ebcee55d2b8f502cdfa9f8ce0fe0e41db599a443a794b`

Type:

```lean
Nat → (Ω : Type u_1) → [Fintype Ω] → Type u_1
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `8eaeba4b3c46e27e9f0989c7bf9a768134f51f2ddeb81363877189362adb617b`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] →
      (toP17LimitedPrecisionRecursiveSumRun : LocalDef016 m Ω) →
        (∀ (k : Fin m) (ω : Ω),
            Real.instLE.le (abs (LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω))
              (LocalDef013 toP17LimitedPrecisionRecursiveSumRun.p)) →
          (∀ (k : Fin m) (X : Ω → Real),
              LocalDef025
                  (fun j ω => LocalDef022 toP17LimitedPrecisionRecursiveSumRun j ω) k X →
                Eq
                  (LocalDef024 toP17LimitedPrecisionRecursiveSumRun.probability fun ω =>
                    instHMul.hMul (X ω) (LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω))
                  0) →
            (∀ (i j : Fin (instHAdd.hAdd m 1)),
                And
                  (Real.instLE.le 0
                    (LocalDef024 toP17LimitedPrecisionRecursiveSumRun.probability fun ω =>
                      instHMul.hMul
                        (instHSub.hSub
                          (LocalDef026
                            (fun k => LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω) i)
                          1)
                        (instHSub.hSub
                          (LocalDef026
                            (fun k => LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω) j)
                          1)))
                  (Real.instLE.le
                    (LocalDef024 toP17LimitedPrecisionRecursiveSumRun.probability fun ω =>
                      instHMul.hMul
                        (instHSub.hSub
                          (LocalDef026
                            (fun k => LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω) i)
                          1)
                        (instHSub.hSub
                          (LocalDef026
                            (fun k => LocalDef022 toP17LimitedPrecisionRecursiveSumRun k ω) j)
                          1))
                    (LocalDef010 m
                      (instHPow.hPow (LocalDef013 toP17LimitedPrecisionRecursiveSumRun.p) 2)))) →
              (∀ (i : Fin (instHAdd.hAdd m 1)) (ω : Ω),
                  Real.instLE.le (abs (LocalDef023 toP17LimitedPrecisionRecursiveSumRun i ω))
                    (instHSub.hSub
                      (LocalDef010 m
                        (instHAdd.hAdd (LocalDef013 toP17LimitedPrecisionRecursiveSumRun.p)
                          (LocalDef013
                            (instHAdd.hAdd toP17LimitedPrecisionRecursiveSumRun.p
                              toP17LimitedPrecisionRecursiveSumRun.r))))
                      (LocalDef010 m (LocalDef013 toP17LimitedPrecisionRecursiveSumRun.p)))) →
                LocalDef006 m Ω
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `18694e9c1d9246eac6354d260a132cdf303f1118117c94cb9e1e005712488d03`

Type:

```lean
∀ {m : Nat}, NeZero (instHAdd.hAdd m 1)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `6add6f3a805986e842859d18df685b1be0e6256f312fa0e9c6957e13f62d7365`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `fd0a240d1fc266d3cd085bc0f6cc5d37e8496bf562c971bd11b5f95e9e7b4d90`

Type:

```lean
{Ω : Type u_1} →
  [inst : Fintype Ω] →
    (prob : Ω → Real) →
      (∀ (ω : Ω), Real.instLE.le 0 (prob ω)) →
        Eq (Finset.univ.sum fun ω => prob ω) 1 → LocalDef014 Ω
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `93782331e6c436ef83cda017924420324703c857d1c60bc662f3f415eac6d837`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] →
      (probability : LocalDef014 Ω) →
        (p r : Nat) →
          instLTNat.lt 0 p →
            instLTNat.lt 0 r →
              (a : Fin (instHAdd.hAdd m 1) → Real) →
                (delta beta : Fin m → Ω → Real) →
                  (truncate : Real → Real) →
                    (∀ (k : Fin m) (ω : Ω), Real.instLE.le (abs (delta k ω)) (LocalDef013 p)) →
                      (∀ (k : Fin m) (ω : Ω), Real.instLE.le 0 (instHAdd.hAdd 1 (delta k ω))) →
                        (∀ (k : Fin m) (ω : Ω),
                            Real.instLE.le (abs (beta k ω)) (LocalDef013 (instHAdd.hAdd p r))) →
                          (∀ (k : Fin m) (ω : Ω),
                              Eq (truncate (LocalDef028 a (fun j => delta j ω) k))
                                (instHMul.hMul (LocalDef028 a (fun j => delta j ω) k)
                                  (instHAdd.hAdd 1 (beta k ω)))) →
                            (∀ (k : Fin m) (ω : Ω),
                                Eq (LocalDef028 a (fun j => delta j ω) k) 0 → Eq (delta k ω) 0) →
                              (∀ (k : Fin m) (ω : Ω),
                                  Eq (LocalDef028 a (fun j => delta j ω) k) 0 → Eq (beta k ω) 0) →
                                (∀ (k : Fin m), LocalDef025 delta k (beta k)) →
                                  (∀ (k : Fin m) (X : Ω → Real),
                                      LocalDef025 delta k X →
                                        Eq
                                          (LocalDef024 probability fun ω =>
                                            instHMul.hMul (X ω) (delta k ω))
                                          (LocalDef024 probability fun ω =>
                                            instHMul.hMul (X ω) (beta k ω))) →
                                    LocalDef016 m Ω
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `316c4f6e44c8ed5582c01614844e236b90c55af5ab4e9933ff3a24071d7606cd`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → LocalDef016 m Ω → Fin m → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {Ω} [Fintype Ω] run k ω => instHSub.hSub (run.delta k ω) (run.beta k ω)
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8bbb4b9b4b965c502ec328a8094a0ad916163eaa43712e4c054988ce086f857c`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → LocalDef016 m Ω → Fin (instHAdd.hAdd m 1) → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {Ω} [Fintype Ω] run i ω =>
  instHSub.hSub (LocalDef026 (fun k => run.delta k ω) i)
    (LocalDef026 (fun k => LocalDef022 run k ω) i)
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `11fae07829d61b57addb3f2e2be7e9036d8a1f8a8ef1b16838117ee6186916da`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → LocalDef014 Ω → (Ω → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [Fintype Ω] P X => Finset.univ.sum fun ω => instHMul.hMul (P.prob ω) (X ω)
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `abb40cf56e6f17c27b1223311cf80c7107d7c0f71e4293e9c61fc91ae0ce516f`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → (Fin m → Ω → Real) → Fin m → (Ω → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} {Ω} delta k X =>
  ∀ (ω₁ ω₂ : Ω), (∀ (j : Fin m), instLTNat.lt j.val k.val → Eq (delta j ω₁) (delta j ω₂)) → Eq (X ω₁) (X ω₂)
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `74253386f9d26c9c87c32ca56da022c25b92cc552290dc15a32ce476320d0f17`

Type:

```lean
{m : Nat} → (Fin m → Real) → Fin (instHAdd.hAdd m 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} error i =>
  Fin.cases (Finset.univ.prod fun k => instHAdd.hAdd 1 (error k)) (fun i => LocalDef029 m error i)
    i
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `4f80b9f3852b8b9ba3b0014fbd3a1256fafc6c5529d478b198a59550d7985d43`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → LocalDef016 m Ω → Fin m → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.8
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `dae4d26f8b0f7e7b45d38512bbd65f64aabda62baf6e10c4c8970649403c3921`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta k => instHAdd.hAdd (LocalDef030 a delta k) (a k.succ)
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `daa8aca583075e9898d125d3ed3fea416cb13de0fbdfbcdfc472cf4531f77a0e`

Type:

```lean
(m : Nat) → (Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Fin x → Real) x
    (fun x f x_2 =>
      LocalDef031
        (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Fin x → Real) x → Fin x → Real) x x_2
        (fun x x_3 i => i.elim0)
        (fun m delta x i =>
          Fin.lastCases (instHAdd.hAdd 1 (delta (Fin.last m)))
            (fun i => instHMul.hMul (x.1 (fun j => delta j.castSucc) i) (instHAdd.hAdd 1 (delta (Fin.last m)))) i)
        f)
    x_1
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b0cffd1b1978ca87c8b1ea80b35b4d982b7eba4c987f85d7d535854b2eec865a`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta k =>
  Fin.foldl k.val
    (fun acc j =>
      have q := ⟨j.val, ⋯⟩;
      instHMul.hMul (instHAdd.hAdd acc (a q.succ)) (instHAdd.hAdd 1 (delta q)))
    (a 0)
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `3b1377d5824c42477286e98c7fbf2fdc72b9e75f564a8487919c81a5d862d948`

Type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      ((x : Fin 0 → Real) → motive 0 x) →
        ((m : Nat) → (delta : Fin (instHAdd.hAdd m 1) → Real) → motive m.succ delta) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `6`
- Semantic SHA-256: `aed4abfdb1053e620927af170c3392a2edc788934a058c8727ae9f49dfacd8df`

Type:

```lean
∀ {m : Nat} (k : Fin m) (j : Fin k.val), instLTNat.lt j.val m
```

### D033: `DivInvMonoid.toDiv`

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

### D034: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D035: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

### D036: `HAdd.hAdd`

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

### D037: `HDiv.hDiv`

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

### D038: `HMul.hMul`

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

### D039: `HPow.hPow`

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

### D040: `HSub.hSub`

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

### D041: `LE.le`

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

### D042: `LT.lt`

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

### D043: `Monoid.toNatPow`

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

### D044: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D045: `Ne`

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

### D046: `OfNat.ofNat`

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

### D047: `One.toOfNat1`

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

### D048: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D049: `Real.instAdd`

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

### D051: `Real.instDivInvMonoid`

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

### D052: `Real.instLE`

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

### D053: `Real.instLT`

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

### D054: `Real.instMonoid`

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

### D055: `Real.instMul`

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

### D056: `Real.instOne`

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

### D057: `Real.instSub`

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

### D058: `Real.instZero`

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

### D059: `Real.lattice`

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

### D060: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D061: `Zero.toOfNat0`

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

### D062: `abs`

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

### D063: `instAddNat`

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

### D064: `instHAdd`

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

### D065: `instHDiv`

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

### D066: `instHMul`

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

### D067: `instHPow`

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

### D068: `instHSub`

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

### D069: `instOfNatNat`

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

### D070: `setOf`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cee4433aebd78c308ec85f62ccd30489c00ec9cc23a98f4d2139c17f840f4988`

Type:

```lean
{α : Type u} → (α → Prop) → Set α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p => p
```

### D071: `Classical.propDecidable`

- Role: `external-frontier`
- Owner module: `Init.Classical`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `823c02cb7dcdb8ce30edfb12a2496dda0849f0773c65f9e91e289fab27c36c46`

Type:

```lean
(a : Prop) → Decidable a
```

Definition body (one-level semantic boundary):

```lean
fun a => Classical.choice ⋯
```

### D072: `Fin.fintype`

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

### D073: `Fin.foldl`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Fold`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5ab599c7f2f67b41cf899570d42ffbfae3263cdad61b9afc24765cd587fdf181`

Type:

```lean
{α : Sort u_1} → (n : Nat) → (α → Fin n → α) → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} n f init => Fin.foldl.loop✝ n f init 0
```

### D074: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8f9c302902ae8c66b3f71728ffe02994a026b562f27b9df8d4f84793e455e26b`

Type:

```lean
{n : Nat} → [NeZero n] → {i : Nat} → OfNat (Fin n) i
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] {i} => { ofNat := Fin.ofNat n i }
```

### D075: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D076: `Finset.sum`

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

### D077: `Finset.univ`

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

### D078: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `941ea3346e809f919727c21bfcdeea342714a6b83f1cf871d648aa2cb14d6e9e`

Type:

```lean
{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} γ [self : Membership α γ] => self.1
```

### D079: `Real.instAddCommMonoid`

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

### D080: `Real.instNatCast`

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

### D081: `Set`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a6e551515032966c16e4f42e4548ff1854c2dce05ffe51e98b66943caecc78ec`

Type:

```lean
Type u → Type u
```

Definition body (one-level semantic boundary):

```lean
fun α => α → Prop
```

### D082: `Set.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5858be77d319c5a0e238602f16818ed6fb2e2b52a81ff7edb07bc219d652f201`

Type:

```lean
{α : Type u} → Membership α (Set α)
```

Definition body (one-level semantic boundary):

```lean
fun {α} => { mem := Set.Mem }
```

### D083: `instOfNatAtLeastTwo`

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

### D084: `instSubNat`

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

### D085: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D086: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D087: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D088: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D089: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

### D090: `Zero.ofOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d610ee8a0a2a61b7850d6032e696e6ae93221da787dff4096e98d4122502f26d`

Type:

```lean
{α : Type u_1} → [OfNat α 0] → Zero α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [OfNat α 0] => { zero := 0 }
```

### D091: `Fin.cases`

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

### D092: `Fin.val`

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

### D093: `Finset.prod`

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

### D094: `Real.instCommMonoid`

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

### D095: `instLTNat`

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

### D096: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D097: `Fin.elim0`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6798d9ecc71442697957111ff84f599d2e1aec9c65eb25a1dc04d6eaa6b3fb16`

Type:

```lean
{α : Sort u} → Fin 0 → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} x => Fin.elim0.match_1 (fun x => α) x fun val h => absurd h ⋯
```

### D098: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`

Type:

```lean
(n : Nat) → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun n => ⟨n, ⋯⟩
```

### D099: `Fin.lastCases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e2538d914643deb2acf9d1fbc61ba25e26d1301c9c57c67c00290261116b84c7`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive (Fin.last n) → ((i : Fin n) → motive i.castSucc) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} last cast i => Fin.reverseInduction last (fun i x => cast i) i
```

### D100: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D101: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D102: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D103: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D104: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D105: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```
