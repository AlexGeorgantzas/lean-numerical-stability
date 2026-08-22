# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {State : Type u_1} [inst : AddCommGroup State] [inst_1 : Module Real State] {s : Nat}
  (run : LocalDef001 State s),
  And
    (Eq (LocalDef005 run)
      (instHAdd.hAdd (LocalDef004 run) (LocalDef002 run)))
    (And (Eq (LocalDef002 run) (LocalDef003 run))
      (∀ {n : Nat} (observe : AddMonoidHom State (Fin n → Real)),
        Real.instLE.le
          (LocalDef006 (AddMonoidHom.instFunLike.coe observe (LocalDef005 run)))
          (instHAdd.hAdd
            (LocalDef006 (AddMonoidHom.instFunLike.coe observe (LocalDef004 run)))
            (LocalDef006
              (AddMonoidHom.instFunLike.coe observe (LocalDef002 run))))))
```

## Fully explicit elaborated target type

```lean
∀ {State : Type u_1} [inst : AddCommGroup.{u_1} State]
  [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] {s : Nat}
  (run : @LocalDef001.{u_1} State inst inst_1 s),
  And
    (@Eq.{u_1 + 1} State (@LocalDef005.{u_1} State inst inst_1 s run)
      (@HAdd.hAdd.{u_1, u_1, u_1} State State State
        (@instHAdd.{u_1} State
          (@AddCommMagma.toAdd.{u_1} State
            (@AddCommSemigroup.toAddCommMagma.{u_1} State
              (@AddCommMonoid.toAddCommSemigroup.{u_1} State (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
        (@LocalDef004.{u_1} State inst inst_1 s run)
        (@LocalDef002.{u_1} State inst inst_1 s run)))
    (And
      (@Eq.{u_1 + 1} State (@LocalDef002.{u_1} State inst inst_1 s run)
        (@LocalDef003.{u_1} State inst inst_1 s run))
      (∀ {n : Nat}
        (observe :
          @AddMonoidHom.{u_1, 0} State (Fin n → Real)
            (@AddZeroClass.toAddZero.{u_1} State
              (@AddMonoid.toAddZeroClass.{u_1} State
                (@SubNegMonoid.toAddMonoid.{u_1} State
                  (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
            (@AddZeroClass.toAddZero.{0} (Fin n → Real)
              (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid))),
        @LE.le.{0} Real Real.instLE
          (@LocalDef006 n
            (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
              (@AddMonoidHom.{u_1, 0} State (Fin n → Real)
                (@AddZeroClass.toAddZero.{u_1} State
                  (@AddMonoid.toAddZeroClass.{u_1} State
                    (@SubNegMonoid.toAddMonoid.{u_1} State
                      (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                  (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                    @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
              State (fun (x : State) => Fin n → Real)
              (@AddMonoidHom.instFunLike.{u_1, 0} State (Fin n → Real)
                (@AddZeroClass.toAddZero.{u_1} State
                  (@AddMonoid.toAddZeroClass.{u_1} State
                    (@SubNegMonoid.toAddMonoid.{u_1} State
                      (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                  (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                    @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
              observe (@LocalDef005.{u_1} State inst inst_1 s run)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@LocalDef006 n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
                (@AddMonoidHom.{u_1, 0} State (Fin n → Real)
                  (@AddZeroClass.toAddZero.{u_1} State
                    (@AddMonoid.toAddZeroClass.{u_1} State
                      (@SubNegMonoid.toAddMonoid.{u_1} State
                        (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                  (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                    (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                      @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
                State (fun (x : State) => Fin n → Real)
                (@AddMonoidHom.instFunLike.{u_1, 0} State (Fin n → Real)
                  (@AddZeroClass.toAddZero.{u_1} State
                    (@AddMonoid.toAddZeroClass.{u_1} State
                      (@SubNegMonoid.toAddMonoid.{u_1} State
                        (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                  (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                    (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                      @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
                observe (@LocalDef004.{u_1} State inst inst_1 s run)))
            (@LocalDef006 n
              (@DFunLike.coe.{u_1 + 1, u_1 + 1, 1}
                (@AddMonoidHom.{u_1, 0} State (Fin n → Real)
                  (@AddZeroClass.toAddZero.{u_1} State
                    (@AddMonoid.toAddZeroClass.{u_1} State
                      (@SubNegMonoid.toAddMonoid.{u_1} State
                        (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                  (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                    (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                      @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
                State (fun (x : State) => Fin n → Real)
                (@AddMonoidHom.instFunLike.{u_1, 0} State (Fin n → Real)
                  (@AddZeroClass.toAddZero.{u_1} State
                    (@AddMonoid.toAddZeroClass.{u_1} State
                      (@SubNegMonoid.toAddMonoid.{u_1} State
                        (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst)))))
                  (@AddZeroClass.toAddZero.{0} (Fin n → Real)
                    (@Pi.addZeroClass.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                      @AddMonoid.toAddZeroClass.{0} Real Real.instAddMonoid)))
                observe (@LocalDef002.{u_1} State inst inst_1 s run))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4c512f909553739d8245d47f3d97a108f4a069876d1feee55f76c3f6aa038014`

Type:

```lean
(State : Type u_1) → [inst : AddCommGroup State] → [Module Real State] → Nat → Type u_1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `09abeed8ae96fb7a31cd61d38eb7629f8ee3003852fe777d1cb3f38717f69557`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.schemeNext run.perturbedNext
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5cb49b90365b199977d3f1d7d28a767d875a28c8517e6624d4c5881438f2b313`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run =>
  instHSub.hSub
    (instHAdd.hAdd (instHSMul.hSMul run.step (LocalDef018 run.b fun j => run.F (run.schemeStages j)))
      (instHSMul.hSMul run.step (LocalDef018 run.bPerturbation fun j => run.F (run.schemeStages j))))
    (instHAdd.hAdd
      (instHSMul.hSMul run.step (LocalDef018 run.b fun j => run.F (run.perturbedStages j)))
      (instHSMul.hSMul run.step
        (LocalDef018 run.bPerturbation fun j => run.FEpsilon (run.perturbedStages j))))
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2fbb85c21e4fdaca5622a0ce43ab76cb8111863146ff8f1b1411a5ac72b633dc`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.referenceNext run.schemeNext
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `31f4bde6713404489f3abd1c777e5ef0dbe5228e7d7294baf02804ce19b3764e`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.referenceNext run.perturbedNext
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dae8ad1d4d081e7ea81ff6faab63aa8a3774e35268e6edada4a650886b35e5e6`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (LocalDef019 x).sqrt
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e42a2eeda3ea18fa7313f4ba335dc74ba57edd03fb85a03be332937a93d335fa`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.7
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5226c0a1e113fe0f09b44792dc7022c39f02b8dcf23a83f32b55322353fd05bc`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.8
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ceb7a6600e85f6a2bf2de9f45dadbed72a0ff514865dda9e440ac6a791dd18a1`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.13
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d12ea3a87a148169bb229f66ffb7174e2d8f098b6c8793c1444f7bf12384c72d`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.14
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `b1aa5279aeb049f8d8fcfbe1882be62cb98e3a458e01ee7586762d6a2a219147`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] →
      {s : Nat} →
        instLTNat.lt 0 s →
          (step epsilon : Real) →
            Ne epsilon 0 →
              (initial : State) →
                State →
                  (F FEpsilon tau : State → State) →
                    (∀ (y : State), Eq (instHSMul.hSMul epsilon (tau y)) (instHSub.hSub (F y) (FEpsilon y))) →
                      (a aPerturbation : Fin s → Fin s → Real) →
                        (b bPerturbation : Fin s → Real) →
                          (schemeStages perturbedStages : Fin s → State) →
                            (schemeNext perturbedNext : State) →
                              (∀ (i : Fin s),
                                  Eq (schemeStages i)
                                    (instHAdd.hAdd
                                      (instHAdd.hAdd initial
                                        (instHSMul.hSMul step
                                          (LocalDef018 (a i) fun j => F (schemeStages j))))
                                      (instHSMul.hSMul step
                                        (LocalDef018 (aPerturbation i) fun j =>
                                          F (schemeStages j))))) →
                                Eq schemeNext
                                    (instHAdd.hAdd
                                      (instHAdd.hAdd initial
                                        (instHSMul.hSMul step
                                          (LocalDef018 b fun j => F (schemeStages j))))
                                      (instHSMul.hSMul step
                                        (LocalDef018 bPerturbation fun j => F (schemeStages j)))) →
                                  (∀ (i : Fin s),
                                      Eq (perturbedStages i)
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd initial
                                            (instHSMul.hSMul step
                                              (LocalDef018 (a i) fun j => F (perturbedStages j))))
                                          (instHSMul.hSMul step
                                            (LocalDef018 (aPerturbation i) fun j =>
                                              FEpsilon (perturbedStages j))))) →
                                    Eq perturbedNext
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd initial
                                            (instHSMul.hSMul step
                                              (LocalDef018 b fun j => F (perturbedStages j))))
                                          (instHSMul.hSMul step
                                            (LocalDef018 bPerturbation fun j =>
                                              FEpsilon (perturbedStages j)))) →
                                      LocalDef001 State s
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a38f7923d0cb393f05b4a4c92a50688763c1db75b9c563c94ccb2652c64438ac`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.18
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bb7b9f0849d4538a32bc1fc5e0ad08bb98616dcd27574c48e94e48f1b98cff71`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → Fin s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.16
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fd4e081863cd62f76e9db2ceb9b145f276d0a4eedd7e4cda4ebd33f66ed7405a`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.6
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f5eca8d21dd1d785c492f5dd48f58f095a520f9b7626a3f86c66816c619b52ff`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.17
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f440014837d722699cf288a047c28d2293f27f040b0e31080dc50cf99e517a8f`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → Fin s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.15
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d0976a090c6dae82baef623c82ef56b8b42f5cc02c053a83e66c2a8093a76770`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → LocalDef001 State s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.2
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `74be2b397af53a5ddc8dce13bb3c6a3e28b0b28fee66c0a836eaabe5374b8515`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] → [Module Real State] → {s : Nat} → (Fin s → Real) → (Fin s → State) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} weights values =>
  Finset.univ.sum fun j => instHSMul.hSMul (weights j) (values j)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0e1e195ed4b6629871f131ca22275653ea718d87fb997f5d9f095659fd926caf`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Finset.univ.sum fun i => instHPow.hPow (x i) 2
```

### D020: `AddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `087ff419a44ee7e835bedcf1beda5a1fee5971b4ef4f17124a5a63cd2b0beb30`

Type:

```lean
Type u → Type u
```

### D021: `AddCommGroup.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f727c3f01db957bd004eab61d742db6d02c6f9b2cdad465fa6f0ac214e09ccfd`

Type:

```lean
{G : Type u} → [self : AddCommGroup G] → AddCommMonoid G
```

Definition body (one-level semantic boundary):

```lean
fun G self => { toAddMonoid := self.toAddMonoid, add_comm := ⋯ }
```

### D022: `AddCommGroup.toAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `7f49725cf4bc16610110860af8f38e6d0fe472c7c1af93721407bad8c7375729`

Type:

```lean
{G : Type u} → [self : AddCommGroup G] → AddGroup G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : AddCommGroup G] => self.1
```

### D023: `AddCommMagma.toAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `78a12fabc3611bc39705a2dcf3fa82ed1f226d804e888d57546b885fefae4453`

Type:

```lean
{G : Type u} → [self : AddCommMagma G] → Add G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : AddCommMagma G] => self.1
```

### D024: `AddCommMonoid.toAddCommSemigroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `dc7cae9f3611bf7a48fc6ba815db5cffeba3ac95ae33d26bec77b827bd041f26`

Type:

```lean
{M : Type u} → [self : AddCommMonoid M] → AddCommSemigroup M
```

Definition body (one-level semantic boundary):

```lean
fun M self => { toAddSemigroup := self.toAddSemigroup, add_comm := ⋯ }
```

### D025: `AddCommSemigroup.toAddCommMagma`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `78f90c6bc01ad86e28d84a9011670656947204c6d8963785407a1b8eb54844ab`

Type:

```lean
{G : Type u} → [self : AddCommSemigroup G] → AddCommMagma G
```

Definition body (one-level semantic boundary):

```lean
fun G self => { toAdd := self.toAdd, add_comm := ⋯ }
```

### D026: `AddGroup.toSubNegMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8c0fca6ee264d934b25c679f16be6b83bb2a2f7c58a8ac0afab0c146219e16a1`

Type:

```lean
{A : Type u} → [self : AddGroup A] → SubNegMonoid A
```

Definition body (one-level semantic boundary):

```lean
fun A [self : AddGroup A] => self.1
```

### D027: `AddMonoid.toAddZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4b5cfcaa0e3b1157089b486d5bfd51b9d15b881ea9cad302a6c8f701cae9ef1a`

Type:

```lean
{M : Type u} → [self : AddMonoid M] → AddZeroClass M
```

Definition body (one-level semantic boundary):

```lean
fun M self => { toZero := self.toZero, toAdd := self.toAdd, zero_add := ⋯, add_zero := ⋯ }
```

### D028: `AddMonoidHom`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Hom.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `668638fc002c25e710df6ea55af5fb6aa289555e39ee247661152121413ba784`

Type:

```lean
(M : Type u_10) → (N : Type u_11) → [AddZero M] → [AddZero N] → Type (max u_10 u_11)
```

### D029: `AddMonoidHom.instFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Hom.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e3f45d8cbc6fc68b229ca16d82c000cc8006a38e98a51ee75553b66587c3d1da`

Type:

```lean
{M : Type u_4} → {N : Type u_5} → [inst : AddZero M] → [inst_1 : AddZero N] → FunLike (AddMonoidHom M N) M N
```

Definition body (one-level semantic boundary):

```lean
fun {M} {N} [AddZero M] [AddZero N] => { coe := fun f => f.toFun, coe_injective' := ⋯ }
```

### D030: `AddZeroClass.toAddZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8f64c653a96443ff67b52a5edb3fc264d279905b936c7303e9dd2469af000213`

Type:

```lean
{M : Type u} → [self : AddZeroClass M] → AddZero M
```

Definition body (one-level semantic boundary):

```lean
fun M [self : AddZeroClass M] => self.1
```

### D031: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D032: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
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

### D035: `HAdd.hAdd`

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

### D036: `LE.le`

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

### D037: `Module`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Module.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `132ed119db2ae117b4c85e91594e4fcde0e02a8fde0fb2ee5c57a7a9263c219c`

Type:

```lean
(R : Type u) → (M : Type v) → [Semiring R] → [AddCommMonoid M] → Type (max u v)
```

### D038: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D039: `Pi.addZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Pi.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3e2a7263483c4a8bae8894cf02a6b4f4987b2feec12905a792078401d5831174`

Type:

```lean
{I : Type u} → {f : I → Type v₁} → [(i : I) → AddZeroClass (f i)] → AddZeroClass ((i : I) → f i)
```

Definition body (one-level semantic boundary):

```lean
fun {I} {f} [(i : I) → AddZeroClass (f i)] =>
  { toZero := Pi.instZero, toAdd := Pi.instAdd, zero_add := ⋯, add_zero := ⋯ }
```

### D040: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D041: `Real.instAdd`

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

### D042: `Real.instAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dd0576b764b9fe615b3e1956627dedcd7d8a7b4eb00270e7aa3297ea18a0dc05`

Type:

```lean
AddMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D043: `Real.instLE`

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

### D044: `Real.semiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c0106cafec59cbaa840a6e4c7ee72e629b4456feb6db98c6bf8c3085fcac475c`

Type:

```lean
Semiring Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D045: `SubNegMonoid.toAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9e6f6ef922e3c39bdc8dcf74fa873f2e393c916c08aa49739c9dcafb3f96877b`

Type:

```lean
{G : Type u} → [self : SubNegMonoid G] → AddMonoid G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : SubNegMonoid G] => self.1
```

### D046: `instHAdd`

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

### D047: `AddZero.toZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `aa06299f9d38f11e9dad40701d7541d8eba2a4ac673c643f4c5f5ce1369490cc`

Type:

```lean
{M : Type u_2} → [self : AddZero M] → Zero M
```

Definition body (one-level semantic boundary):

```lean
fun M [self : AddZero M] => self.1
```

### D048: `DistribMulAction.toDistribSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `17a3c7e66a4c2897891d468da70a58e73aa0b8e044ea0cc90d8d6e9e51c08f02`

Type:

```lean
{M : Type u_1} → {A : Type u_7} → [inst : Monoid M] → [inst_1 : AddMonoid A] → [DistribMulAction M A] → DistribSMul M A
```

Definition body (one-level semantic boundary):

```lean
fun {M} {A} [Monoid M] [AddMonoid A] [inst_2 : DistribMulAction M A] =>
  let __src := inst_2;
  { toSMul := __src.toSMul, smul_zero := ⋯, smul_add := ⋯ }
```

### D049: `DistribSMul.toSMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f640928ea31b161891006aaf9950d636ac5e1fbda413a7712f36546c938b3fdf`

Type:

```lean
{M : Type u_12} → {A : Type u_13} → {inst : AddZeroClass A} → [self : DistribSMul M A] → SMulZeroClass M A
```

Definition body (one-level semantic boundary):

```lean
fun M A {inst} [self : DistribSMul M A] => self.1
```

### D050: `HSMul.hSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f1757307432fadbd23925bbf0a318b8da57d17711478e1073a19ce64c21d55f4`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSMul α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSMul α β γ] => self.1
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

### D052: `Module.toDistribMulAction`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Module.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `88cb31241158a61c2eaae8459f700e8db39d9fca998e95d4fa73b87b68be8c60`

Type:

```lean
{R : Type u} →
  {M : Type v} → {inst : Semiring R} → {inst_1 : AddCommMonoid M} → [self : Module R M] → DistribMulAction R M
```

Definition body (one-level semantic boundary):

```lean
fun R M {inst} {inst_1} [self : Module R M] => self.1
```

### D053: `Real.instMonoid`

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

### D054: `Real.sqrt`

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

### D055: `SMulZeroClass.toSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a8cadadddb0c9fd4a7bcb7c57401fafb43a1f330afa35fdacacb6d0e82d0bcf6`

Type:

```lean
{M : Type u_12} → {A : Type u_13} → {inst : Zero A} → [self : SMulZeroClass M A] → SMul M A
```

Definition body (one-level semantic boundary):

```lean
fun M A {inst} [self : SMulZeroClass M A] => self.1
```

### D056: `SubNegMonoid.toSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f60885ee7a5e97dbc3d343ecb54849b15ae9ca7cc989f350d3b7fee2d2d0724b`

Type:

```lean
{G : Type u} → [self : SubNegMonoid G] → Sub G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : SubNegMonoid G] => self.3
```

### D057: `instHSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `04ea7c06812eccb8531b763b7aa28fd8f968befff069e74166ff1b406f7512e3`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [SMul α β] → HSMul α β β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : SMul α β] => { hSMul := inst.smul }
```

### D058: `instHSub`

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

### D059: `Fin.fintype`

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

### D060: `Finset.sum`

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

### D061: `Finset.univ`

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

### D062: `HPow.hPow`

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

### D063: `LT.lt`

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

### D064: `Monoid.toNatPow`

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

### D065: `Ne`

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

### D066: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D067: `Real.instAddCommMonoid`

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

### D068: `Real.instZero`

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

### D069: `Zero.toOfNat0`

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

### D070: `instHPow`

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

### D071: `instLTNat`

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

### D072: `instOfNatNat`

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
