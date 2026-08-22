# Declaration dossier for P18-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p18_t1_scheme_perturbation_error_split
    {State : Type*} [AddCommGroup State] [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) :
    p18TotalOneStepError run =
        p18SchemeOneStepError run + p18PerturbationOneStepError run ∧
      p18PerturbationOneStepError run =
        p18PerturbationOutputExpansion run ∧
      ∀ {n : ℕ} (observe : State →+ (Fin n → ℝ)),
        p18VecNorm2 (observe (p18TotalOneStepError run)) ≤
          p18VecNorm2 (observe (p18SchemeOneStepError run)) +
            p18VecNorm2 (observe (p18PerturbationOneStepError run))
```

## Elaborated target type

```lean
∀ {State : Type u_1} [inst : AddCommGroup State] [inst_1 : Module Real State] {s : Nat}
  (run : HighamBench.P18AdditiveRKOneStepRun State s),
  And
    (Eq (HighamBench.p18TotalOneStepError run)
      (instHAdd.hAdd (HighamBench.p18SchemeOneStepError run) (HighamBench.p18PerturbationOneStepError run)))
    (And (Eq (HighamBench.p18PerturbationOneStepError run) (HighamBench.p18PerturbationOutputExpansion run))
      (∀ {n : Nat} (observe : AddMonoidHom State (Fin n → Real)),
        Real.instLE.le
          (HighamBench.p18VecNorm2 (AddMonoidHom.instFunLike.coe observe (HighamBench.p18TotalOneStepError run)))
          (instHAdd.hAdd
            (HighamBench.p18VecNorm2 (AddMonoidHom.instFunLike.coe observe (HighamBench.p18SchemeOneStepError run)))
            (HighamBench.p18VecNorm2
              (AddMonoidHom.instFunLike.coe observe (HighamBench.p18PerturbationOneStepError run))))))
```

## Fully explicit elaborated target type

```lean
∀ {State : Type u_1} [inst : AddCommGroup.{u_1} State]
  [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] {s : Nat}
  (run : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s),
  And
    (@Eq.{u_1 + 1} State (@HighamBench.p18TotalOneStepError.{u_1} State inst inst_1 s run)
      (@HAdd.hAdd.{u_1, u_1, u_1} State State State
        (@instHAdd.{u_1} State
          (@AddCommMagma.toAdd.{u_1} State
            (@AddCommSemigroup.toAddCommMagma.{u_1} State
              (@AddCommMonoid.toAddCommSemigroup.{u_1} State (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
        (@HighamBench.p18SchemeOneStepError.{u_1} State inst inst_1 s run)
        (@HighamBench.p18PerturbationOneStepError.{u_1} State inst inst_1 s run)))
    (And
      (@Eq.{u_1 + 1} State (@HighamBench.p18PerturbationOneStepError.{u_1} State inst inst_1 s run)
        (@HighamBench.p18PerturbationOutputExpansion.{u_1} State inst inst_1 s run))
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
          (@HighamBench.p18VecNorm2 n
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
              observe (@HighamBench.p18TotalOneStepError.{u_1} State inst inst_1 s run)))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HighamBench.p18VecNorm2 n
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
                observe (@HighamBench.p18SchemeOneStepError.{u_1} State inst inst_1 s run)))
            (@HighamBench.p18VecNorm2 n
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
                observe (@HighamBench.p18PerturbationOneStepError.{u_1} State inst inst_1 s run))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P18Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P18Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P18AdditiveRKOneStepRun`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4c512f909553739d8245d47f3d97a108f4a069876d1feee55f76c3f6aa038014`

Type:

```lean
(State : Type u_1) → [inst : AddCommGroup State] → [Module Real State] → Nat → Type u_1
```

Fully explicit type:

```lean
(State : Type u_1) →
  [inst : AddCommGroup.{u_1} State] →
    [@Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] → (s : Nat) → Type u_1
```

### D002: `HighamBench.p18PerturbationOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `09abeed8ae96fb7a31cd61d38eb7629f8ee3003852fe777d1cb3f38717f69557`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (run : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.schemeNext run.perturbedNext
```

### D003: `HighamBench.p18PerturbationOutputExpansion`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5cb49b90365b199977d3f1d7d28a767d875a28c8517e6624d4c5881438f2b313`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (run : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run =>
  instHSub.hSub
    (instHAdd.hAdd (instHSMul.hSMul run.step (HighamBench.p18ModuleStageSum run.b fun j => run.F (run.schemeStages j)))
      (instHSMul.hSMul run.step (HighamBench.p18ModuleStageSum run.bPerturbation fun j => run.F (run.schemeStages j))))
    (instHAdd.hAdd
      (instHSMul.hSMul run.step (HighamBench.p18ModuleStageSum run.b fun j => run.F (run.perturbedStages j)))
      (instHSMul.hSMul run.step
        (HighamBench.p18ModuleStageSum run.bPerturbation fun j => run.FEpsilon (run.perturbedStages j))))
```

### D004: `HighamBench.p18SchemeOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2fbb85c21e4fdaca5622a0ce43ab76cb8111863146ff8f1b1411a5ac72b633dc`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (run : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.referenceNext run.schemeNext
```

### D005: `HighamBench.p18TotalOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `31f4bde6713404489f3abd1c777e5ef0dbe5228e7d7294baf02804ce19b3764e`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (run : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} run => instHSub.hSub run.referenceNext run.perturbedNext
```

### D006: `HighamBench.p18VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dae8ad1d4d081e7ea81ff6faab63aa8a3774e35268e6edada4a650886b35e5e6`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (HighamBench.p18VecNorm2Sq x).sqrt
```

### D007: `HighamBench.P18AdditiveRKOneStepRun.F`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e42a2eeda3ea18fa7313f4ba335dc74ba57edd03fb85a03be332937a93d335fa`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.7
```

### D008: `HighamBench.P18AdditiveRKOneStepRun.FEpsilon`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5226c0a1e113fe0f09b44792dc7022c39f02b8dcf23a83f32b55322353fd05bc`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.8
```

### D009: `HighamBench.P18AdditiveRKOneStepRun.b`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ceb7a6600e85f6a2bf2de9f45dadbed72a0ff514865dda9e440ac6a791dd18a1`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.13
```

### D010: `HighamBench.P18AdditiveRKOneStepRun.bPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d12ea3a87a148169bb229f66ffb7174e2d8f098b6c8793c1444f7bf12384c72d`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.14
```

### D011: `HighamBench.P18AdditiveRKOneStepRun.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
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
                                          (HighamBench.p18ModuleStageSum (a i) fun j => F (schemeStages j))))
                                      (instHSMul.hSMul step
                                        (HighamBench.p18ModuleStageSum (aPerturbation i) fun j =>
                                          F (schemeStages j))))) →
                                Eq schemeNext
                                    (instHAdd.hAdd
                                      (instHAdd.hAdd initial
                                        (instHSMul.hSMul step
                                          (HighamBench.p18ModuleStageSum b fun j => F (schemeStages j))))
                                      (instHSMul.hSMul step
                                        (HighamBench.p18ModuleStageSum bPerturbation fun j => F (schemeStages j)))) →
                                  (∀ (i : Fin s),
                                      Eq (perturbedStages i)
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd initial
                                            (instHSMul.hSMul step
                                              (HighamBench.p18ModuleStageSum (a i) fun j => F (perturbedStages j))))
                                          (instHSMul.hSMul step
                                            (HighamBench.p18ModuleStageSum (aPerturbation i) fun j =>
                                              FEpsilon (perturbedStages j))))) →
                                    Eq perturbedNext
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd initial
                                            (instHSMul.hSMul step
                                              (HighamBench.p18ModuleStageSum b fun j => F (perturbedStages j))))
                                          (instHSMul.hSMul step
                                            (HighamBench.p18ModuleStageSum bPerturbation fun j =>
                                              FEpsilon (perturbedStages j)))) →
                                      HighamBench.P18AdditiveRKOneStepRun State s
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} →
        (stage_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s) →
          (step epsilon : Real) →
            (epsilon_ne_zero :
                @Ne.{1} Real epsilon (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
              (initial referenceNext : State) →
                (F FEpsilon tau : State → State) →
                  (operator_perturbation :
                      ∀ (y : State),
                        @Eq.{u_1 + 1} State
                          (@HSMul.hSMul.{0, u_1, u_1} Real State State
                            (@instHSMul.{0, u_1} Real State
                              (@SMulZeroClass.toSMul.{0, u_1} Real State
                                (@AddZero.toZero.{u_1} State
                                  (@AddZeroClass.toAddZero.{u_1} State
                                    (@AddMonoid.toAddZeroClass.{u_1} State
                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                          (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                  (@AddMonoid.toAddZeroClass.{u_1} State
                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                        (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                  (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                        (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                    (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                      (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                            epsilon (tau y))
                          (@HSub.hSub.{u_1, u_1, u_1} State State State
                            (@instHSub.{u_1} State
                              (@SubNegMonoid.toSub.{u_1} State
                                (@AddGroup.toSubNegMonoid.{u_1} State (@AddCommGroup.toAddGroup.{u_1} State inst))))
                            (F y) (FEpsilon y))) →
                    (a aPerturbation : Fin s → Fin s → Real) →
                      (b bPerturbation : Fin s → Real) →
                        (schemeStages perturbedStages : Fin s → State) →
                          (schemeNext perturbedNext : State) →
                            (scheme_stage_equation :
                                ∀ (i : Fin s),
                                  @Eq.{u_1 + 1} State (schemeStages i)
                                    (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                      (@instHAdd.{u_1} State
                                        (@AddCommMagma.toAdd.{u_1} State
                                          (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                            (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                              (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                      (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                        (@instHAdd.{u_1} State
                                          (@AddCommMagma.toAdd.{u_1} State
                                            (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                              (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                        initial
                                        (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                          (@instHSMul.{0, u_1} Real State
                                            (@SMulZeroClass.toSMul.{0, u_1} Real State
                                              (@AddZero.toZero.{u_1} State
                                                (@AddZeroClass.toAddZero.{u_1} State
                                                  (@AddMonoid.toAddZeroClass.{u_1} State
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                              (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                (@AddMonoid.toAddZeroClass.{u_1} State
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                  (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                    (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                          step
                                          (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s (a i)
                                            fun (j : Fin s) => F (schemeStages j))))
                                      (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                        (@instHSMul.{0, u_1} Real State
                                          (@SMulZeroClass.toSMul.{0, u_1} Real State
                                            (@AddZero.toZero.{u_1} State
                                              (@AddZeroClass.toAddZero.{u_1} State
                                                (@AddMonoid.toAddZeroClass.{u_1} State
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                            (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                              (@AddMonoid.toAddZeroClass.{u_1} State
                                                (@SubNegMonoid.toAddMonoid.{u_1} State
                                                  (@AddGroup.toSubNegMonoid.{u_1} State
                                                    (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                              (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                (@SubNegMonoid.toAddMonoid.{u_1} State
                                                  (@AddGroup.toSubNegMonoid.{u_1} State
                                                    (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                  (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                        step
                                        (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s (aPerturbation i)
                                          fun (j : Fin s) => F (schemeStages j))))) →
                              (scheme_output_equation :
                                  @Eq.{u_1 + 1} State schemeNext
                                    (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                      (@instHAdd.{u_1} State
                                        (@AddCommMagma.toAdd.{u_1} State
                                          (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                            (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                              (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                      (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                        (@instHAdd.{u_1} State
                                          (@AddCommMagma.toAdd.{u_1} State
                                            (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                              (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                        initial
                                        (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                          (@instHSMul.{0, u_1} Real State
                                            (@SMulZeroClass.toSMul.{0, u_1} Real State
                                              (@AddZero.toZero.{u_1} State
                                                (@AddZeroClass.toAddZero.{u_1} State
                                                  (@AddMonoid.toAddZeroClass.{u_1} State
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                              (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                (@AddMonoid.toAddZeroClass.{u_1} State
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                  (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                    (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                          step
                                          (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s b fun (j : Fin s) =>
                                            F (schemeStages j))))
                                      (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                        (@instHSMul.{0, u_1} Real State
                                          (@SMulZeroClass.toSMul.{0, u_1} Real State
                                            (@AddZero.toZero.{u_1} State
                                              (@AddZeroClass.toAddZero.{u_1} State
                                                (@AddMonoid.toAddZeroClass.{u_1} State
                                                  (@SubNegMonoid.toAddMonoid.{u_1} State
                                                    (@AddGroup.toSubNegMonoid.{u_1} State
                                                      (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                            (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                              (@AddMonoid.toAddZeroClass.{u_1} State
                                                (@SubNegMonoid.toAddMonoid.{u_1} State
                                                  (@AddGroup.toSubNegMonoid.{u_1} State
                                                    (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                              (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                (@SubNegMonoid.toAddMonoid.{u_1} State
                                                  (@AddGroup.toSubNegMonoid.{u_1} State
                                                    (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                  (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                        step
                                        (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s bPerturbation
                                          fun (j : Fin s) => F (schemeStages j))))) →
                                (perturbed_stage_equation :
                                    ∀ (i : Fin s),
                                      @Eq.{u_1 + 1} State (perturbedStages i)
                                        (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                          (@instHAdd.{u_1} State
                                            (@AddCommMagma.toAdd.{u_1} State
                                              (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                                (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                  (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                          (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                            (@instHAdd.{u_1} State
                                              (@AddCommMagma.toAdd.{u_1} State
                                                (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                                  (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                    (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                            initial
                                            (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                              (@instHSMul.{0, u_1} Real State
                                                (@SMulZeroClass.toSMul.{0, u_1} Real State
                                                  (@AddZero.toZero.{u_1} State
                                                    (@AddZeroClass.toAddZero.{u_1} State
                                                      (@AddMonoid.toAddZeroClass.{u_1} State
                                                        (@SubNegMonoid.toAddMonoid.{u_1} State
                                                          (@AddGroup.toSubNegMonoid.{u_1} State
                                                            (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                                  (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                    (@AddMonoid.toAddZeroClass.{u_1} State
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                    (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                      (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                        (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                              step
                                              (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s (a i)
                                                fun (j : Fin s) => F (perturbedStages j))))
                                          (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                            (@instHSMul.{0, u_1} Real State
                                              (@SMulZeroClass.toSMul.{0, u_1} Real State
                                                (@AddZero.toZero.{u_1} State
                                                  (@AddZeroClass.toAddZero.{u_1} State
                                                    (@AddMonoid.toAddZeroClass.{u_1} State
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                                (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                  (@AddMonoid.toAddZeroClass.{u_1} State
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                  (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                    (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                      (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                            step
                                            (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s (aPerturbation i)
                                              fun (j : Fin s) => FEpsilon (perturbedStages j))))) →
                                  (perturbed_output_equation :
                                      @Eq.{u_1 + 1} State perturbedNext
                                        (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                          (@instHAdd.{u_1} State
                                            (@AddCommMagma.toAdd.{u_1} State
                                              (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                                (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                  (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                          (@HAdd.hAdd.{u_1, u_1, u_1} State State State
                                            (@instHAdd.{u_1} State
                                              (@AddCommMagma.toAdd.{u_1} State
                                                (@AddCommSemigroup.toAddCommMagma.{u_1} State
                                                  (@AddCommMonoid.toAddCommSemigroup.{u_1} State
                                                    (@AddCommGroup.toAddCommMonoid.{u_1} State inst)))))
                                            initial
                                            (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                              (@instHSMul.{0, u_1} Real State
                                                (@SMulZeroClass.toSMul.{0, u_1} Real State
                                                  (@AddZero.toZero.{u_1} State
                                                    (@AddZeroClass.toAddZero.{u_1} State
                                                      (@AddMonoid.toAddZeroClass.{u_1} State
                                                        (@SubNegMonoid.toAddMonoid.{u_1} State
                                                          (@AddGroup.toSubNegMonoid.{u_1} State
                                                            (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                                  (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                    (@AddMonoid.toAddZeroClass.{u_1} State
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                    (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                      (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                        (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                              step
                                              (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s b
                                                fun (j : Fin s) => F (perturbedStages j))))
                                          (@HSMul.hSMul.{0, u_1, u_1} Real State State
                                            (@instHSMul.{0, u_1} Real State
                                              (@SMulZeroClass.toSMul.{0, u_1} Real State
                                                (@AddZero.toZero.{u_1} State
                                                  (@AddZeroClass.toAddZero.{u_1} State
                                                    (@AddMonoid.toAddZeroClass.{u_1} State
                                                      (@SubNegMonoid.toAddMonoid.{u_1} State
                                                        (@AddGroup.toSubNegMonoid.{u_1} State
                                                          (@AddCommGroup.toAddGroup.{u_1} State inst))))))
                                                (@DistribSMul.toSMulZeroClass.{0, u_1} Real State
                                                  (@AddMonoid.toAddZeroClass.{u_1} State
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst))))
                                                  (@DistribMulAction.toDistribSMul.{0, u_1} Real State Real.instMonoid
                                                    (@SubNegMonoid.toAddMonoid.{u_1} State
                                                      (@AddGroup.toSubNegMonoid.{u_1} State
                                                        (@AddCommGroup.toAddGroup.{u_1} State inst)))
                                                    (@Module.toDistribMulAction.{0, u_1} Real State Real.semiring
                                                      (@AddCommGroup.toAddCommMonoid.{u_1} State inst) inst_1)))))
                                            step
                                            (@HighamBench.p18ModuleStageSum.{u_1} State inst inst_1 s bPerturbation
                                              fun (j : Fin s) => FEpsilon (perturbedStages j))))) →
                                    @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s
```

### D012: `HighamBench.P18AdditiveRKOneStepRun.perturbedNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a38f7923d0cb393f05b4a4c92a50688763c1db75b9c563c94ccb2652c64438ac`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.18
```

### D013: `HighamBench.P18AdditiveRKOneStepRun.perturbedStages`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bb7b9f0849d4538a32bc1fc5e0ad08bb98616dcd27574c48e94e48f1b98cff71`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.16
```

### D014: `HighamBench.P18AdditiveRKOneStepRun.referenceNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fd4e081863cd62f76e9db2ceb9b145f276d0a4eedd7e4cda4ebd33f66ed7405a`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.6
```

### D015: `HighamBench.P18AdditiveRKOneStepRun.schemeNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f5eca8d21dd1d785c492f5dd48f58f095a520f9b7626a3f86c66816c619b52ff`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.17
```

### D016: `HighamBench.P18AdditiveRKOneStepRun.schemeStages`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f440014837d722699cf288a047c28d2293f27f040b0e31080dc50cf99e517a8f`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → State
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.15
```

### D017: `HighamBench.P18AdditiveRKOneStepRun.step`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d0976a090c6dae82baef623c82ef56b8b42f5cc02c053a83e66c2a8093a76770`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.2
```

### D018: `HighamBench.p18ModuleStageSum`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `74be2b397af53a5ddc8dce13bb3c6a3e28b0b28fee66c0a836eaabe5374b8515`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] → [Module Real State] → {s : Nat} → (Fin s → Real) → (Fin s → State) → State
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [@Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (weights : Fin s → Real) → (values : Fin s → State) → State
```

Definition body (one-level semantic boundary):

```lean
fun {State} [AddCommGroup State] [Module Real State] {s} weights values =>
  Finset.univ.sum fun j => instHSMul.hSMul (weights j) (values j)
```

### D019: `HighamBench.p18VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0e1e195ed4b6629871f131ca22275653ea718d87fb997f5d9f095659fd926caf`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Real
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

Fully explicit type:

```lean
(G : Type u) → Type u
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

Fully explicit type:

```lean
{G : Type u} → [self : AddCommGroup.{u} G] → AddCommMonoid.{u} G
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

Fully explicit type:

```lean
{G : Type u} → [self : AddCommGroup.{u} G] → AddGroup.{u} G
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

Fully explicit type:

```lean
{G : Type u} → [self : AddCommMagma.{u} G] → Add.{u} G
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

Fully explicit type:

```lean
{M : Type u} → [self : AddCommMonoid.{u} M] → AddCommSemigroup.{u} M
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

Fully explicit type:

```lean
{G : Type u} → [self : AddCommSemigroup.{u} G] → AddCommMagma.{u} G
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

Fully explicit type:

```lean
{A : Type u} → [self : AddGroup.{u} A] → SubNegMonoid.{u} A
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

Fully explicit type:

```lean
{M : Type u} → [self : AddMonoid.{u} M] → AddZeroClass.{u} M
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

Fully explicit type:

```lean
(M : Type u_10) → (N : Type u_11) → [AddZero.{u_10} M] → [AddZero.{u_11} N] → Type (max u_10 u_11)
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

Fully explicit type:

```lean
{M : Type u_4} →
  {N : Type u_5} →
    [inst : AddZero.{u_4} M] →
      [inst_1 : AddZero.{u_5} N] →
        FunLike.{max (u_5 + 1) (u_4 + 1), u_4 + 1, u_5 + 1} (@AddMonoidHom.{u_4, u_5} M N inst inst_1) M N
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

Fully explicit type:

```lean
{M : Type u} → [self : AddZeroClass.{u} M] → AddZero.{u} M
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

Fully explicit type:

```lean
(a b : Prop) → Prop
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

Fully explicit type:

```lean
{F : Sort u_1} →
  {α : outParam.{u_2 + 1} (Sort u_2)} →
    {β : outParam.{max u_2 (u_3 + 1)} (α → Sort u_3)} → [self : DFunLike.{u_1, u_2, u_3} F α β] → F → (a : α) → β a
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

Fully explicit type:

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

Fully explicit type:

```lean
(n : Nat) → Type
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HAdd.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
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

Fully explicit type:

```lean
(R : Type u) → (M : Type v) → [Semiring.{u} R] → [AddCommMonoid.{v} M] → Type (max u v)
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

Fully explicit type:

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

Fully explicit type:

```lean
{I : Type u} → {f : I → Type v₁} → [(i : I) → AddZeroClass.{v₁} (f i)] → AddZeroClass.{max u v₁} ((i : I) → f i)
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

Fully explicit type:

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

Fully explicit type:

```lean
Add.{0} Real
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

Fully explicit type:

```lean
AddMonoid.{0} Real
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

Fully explicit type:

```lean
LE.{0} Real
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

Fully explicit type:

```lean
Semiring.{0} Real
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

Fully explicit type:

```lean
{G : Type u} → [self : SubNegMonoid.{u} G] → AddMonoid.{u} G
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

Fully explicit type:

```lean
{α : Type u_1} → [Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
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

Fully explicit type:

```lean
{M : Type u_2} → [self : AddZero.{u_2} M] → Zero.{u_2} M
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

Fully explicit type:

```lean
{M : Type u_1} →
  {A : Type u_7} →
    [inst : Monoid.{u_1} M] →
      [inst_1 : AddMonoid.{u_7} A] →
        [@DistribMulAction.{u_1, u_7} M A inst inst_1] →
          @DistribSMul.{u_1, u_7} M A (@AddMonoid.toAddZeroClass.{u_7} A inst_1)
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

Fully explicit type:

```lean
{M : Type u_12} →
  {A : Type u_13} →
    {inst : AddZeroClass.{u_13} A} →
      [self : @DistribSMul.{u_12, u_13} M A inst] →
        @SMulZeroClass.{u_12, u_13} M A (@AddZero.toZero.{u_13} A (@AddZeroClass.toAddZero.{u_13} A inst))
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSMul.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSub.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{R : Type u} →
  {M : Type v} →
    {inst : Semiring.{u} R} →
      {inst_1 : AddCommMonoid.{v} M} →
        [self : @Module.{u, v} R M inst inst_1] →
          @DistribMulAction.{u, v} R M (@MonoidWithZero.toMonoid.{u} R (@Semiring.toMonoidWithZero.{u} R inst))
            (@AddCommMonoid.toAddMonoid.{v} M inst_1)
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

Fully explicit type:

```lean
Monoid.{0} Real
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

Fully explicit type:

```lean
(x : Real) → Real
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

Fully explicit type:

```lean
{M : Type u_12} →
  {A : Type u_13} → {inst : Zero.{u_13} A} → [self : @SMulZeroClass.{u_12, u_13} M A inst] → SMul.{u_12, u_13} M A
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

Fully explicit type:

```lean
{G : Type u} → [self : SubNegMonoid.{u} G] → Sub.{u} G
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

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [SMul.{u_1, u_2} α β] → HSMul.{u_1, u_2, u_2} α β β
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

Fully explicit type:

```lean
{α : Type u_1} → [Sub.{u_1} α] → HSub.{u_1, u_1, u_1} α α α
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

Fully explicit type:

```lean
(n : Nat) → Fintype.{0} (Fin n)
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

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
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

Fully explicit type:

```lean
{α : Type u_1} → [Fintype.{u_1} α] → Finset.{u_1} α
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HPow.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → [self : LT.{u} α] → α → α → Prop
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

Fully explicit type:

```lean
{M : Type u_2} → [Monoid.{u_2} M] → Pow.{u_2, 0} M Nat
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

Fully explicit type:

```lean
{α : Sort u} → (a b : α) → Prop
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

Fully explicit type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat.{u} α x] → α
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

Fully explicit type:

```lean
AddCommMonoid.{0} Real
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

Fully explicit type:

```lean
Zero.{0} Real
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

Fully explicit type:

```lean
{α : Type u_1} → [Zero.{u_1} α] → OfNat.{u_1} α (nat_lit 0)
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

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow.{u_1, u_2} α β] → HPow.{u_1, u_2, u_1} α β α
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

Fully explicit type:

```lean
LT.{0} Nat
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

Fully explicit type:

```lean
(n : Nat) → OfNat.{0} Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```
