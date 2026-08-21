# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m : Nat} [inst : NeZero m] (plan : LocalDef002 m) (model : LocalDef006)
  (run : LocalDef004 plan model) (certificate : LocalDef005 run),
  Real.instLT.lt 0 (LocalDef012 (LocalDef010 run)) →
    And
      (Eq (LocalDef011 run)
        (LocalDef013 fun i => LocalDef014 run i))
      (Real.instLE.le
        (instHDiv.hDiv (LocalDef012 (LocalDef011 run))
          (LocalDef012 (LocalDef010 run)))
        (instHAdd.hAdd
          (instHMul.hMul model.epsilon (Finset.univ.sum fun i => LocalDef009 (plan.axis i) model.gamma))
          (instHMul.hMul
            (instHDiv.hDiv (LocalDef015 certificate)
              (LocalDef012 (LocalDef010 run)))
            (instHPow.hPow model.epsilon 2))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m]
  (plan : @LocalDef002 m inst) (model : LocalDef006)
  (run : @LocalDef004 m inst plan model)
  (certificate : @LocalDef005 m inst plan model run)
  (hexactOutput :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@LocalDef012 m (@LocalDef003 m inst plan)
        (@LocalDef010 m inst plan model run))),
  And
    (@Eq.{1} (@LocalDef001 m (@LocalDef003 m inst plan))
      (@LocalDef011 m inst plan model run)
      (@LocalDef013 m m (@LocalDef003 m inst plan) fun (i : Fin m) =>
        @LocalDef014 m inst plan model run i))
    (@LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@LocalDef012 m (@LocalDef003 m inst plan)
          (@LocalDef011 m inst plan model run))
        (@LocalDef012 m (@LocalDef003 m inst plan)
          (@LocalDef010 m inst plan model run)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (LocalDef007 model)
          (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
            fun (i : Fin m) =>
            LocalDef009 (@LocalDef003 m inst plan i)
              (LocalDef008 model)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@LocalDef015 m inst plan model run certificate)
            (@LocalDef012 m (@LocalDef003 m inst plan)
              (@LocalDef010 m inst plan model run)))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (LocalDef007 model)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3d6f4be9264bc317d6ba5fe339cae6bcac3948f80be85f9a1b4bf824f63f64c8`

Type:

```lean
{m : Nat} → (Fin m → LocalDef016) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => LocalDef019 axis → Complex
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `6caec117889378cc56f1650bf6acc121e3ffd3bdbc21c63caa467d85be7c38a6`

Type:

```lean
(m : Nat) → [NeZero m] → Type
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4cedab27fb9a7ea45524918cf9d3dc749b18afcc77faa1aa97c083f24123e330`

Type:

```lean
{m : Nat} → [inst : NeZero m] → LocalDef002 m → Fin m → LocalDef016
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] self => self.1
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `25bf55ce9fbb308560bfbbaeca0f8dff49951a46dc28f9b34edc457626ee779e`

Type:

```lean
{m : Nat} → [inst : NeZero m] → LocalDef002 m → LocalDef006 → Type
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `6e9d106fd523c52042fde8e02b5d28579741aa0a98ac331125bdc9e916f3e359`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} → LocalDef004 plan model → Type
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ae2ce171d4af084f887909ba7d091242f615341789671c72cf38636309bf3c6f`

Type:

```lean
Type
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `afcd2bd12fb818dddebe74e72bfdb4939ca7e7ec5eace06ba903d8bb16522de0`

Type:

```lean
LocalDef006 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3d920d708ae4d25f186c74885d8c6fa22ca6b3a16c98ff3446234ae6f769f2d7`

Type:

```lean
LocalDef006 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `de6e13ca65dad8a782439ed81b73b7d104a439c638689a4920c07d6beaef61a4`

Type:

```lean
LocalDef016 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun axis γ => LocalDef030 axis.plan γ
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `788671334f01292de700d7ad52094076a486d92506af3e8b1eec9233832157e0`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run => LocalDef028 plan.axis m run.input
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c6295fc04054d2db5c0e2e1dac7e3a3ce7bfc7cc6ca7ee781fa6be3ef1ed8ab2`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run =>
  LocalDef034 (LocalDef032 run) (LocalDef010 run)
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4e880f7b2ea35580d060d1ae5723b3de6188d6cc159ca572b35345a4ac4977ce`

Type:

```lean
{m : Nat} → {axis : Fin m → LocalDef016} → LocalDef001 axis → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => instHDiv.hDiv (LocalDef033 x) (LocalDef031 axis).cast.sqrt
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c64c543d2175f5bfd9b9ef82d0c66f9b452e3bac8acd2ed327950b5fe9aa353`

Type:

```lean
{r m : Nat} →
  {axis : Fin m → LocalDef016} → (Fin r → LocalDef001 axis) → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {r m} {axis} term index => Finset.univ.sum fun i => term i index
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7801796a789f19ee1f775af05c688a6f966d1619db640ddee1bda1689b26ba2f`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → Fin m → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i => LocalDef028 plan.axis i.val (run.localError i)
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5cf4d08046a6670a4a8614b759f35d94cc4cd10124da744b9f50e029cb7416f9`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        {run : LocalDef004 plan model} → LocalDef005 run → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} {run} certificate =>
  Finset.univ.sum fun i =>
    instHAdd.hAdd
      (instHMul.hMul (LocalDef035 plan.axis i.val ⋯).cast.sqrt
        (certificate.localSecondOrderCoeff i))
      (instHMul.hMul (LocalDef009 (plan.axis i) model.gamma) (certificate.intermediateFirstOrderCoeff i))
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `b01f3804019ae6052e79bffe5b89c712343a38871fe2d7a130854526cfaf0c60`

Type:

```lean
Type
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b2f626978178d68b0837a0e0951d0d96f475c8666a5d85b70ce90e51a762a1d6`

Type:

```lean
LocalDef016 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5937cc1e42973faaf5c451e01a14738efadaa4745063fa129395e3185c23d71a`

Type:

```lean
(self : LocalDef016) → LocalDef039 self.order
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `530be8ed3c4c64f79ec1bb9c6013196dae46df7b0a095551f41275e333fc63ec`

Type:

```lean
{m : Nat} → (Fin m → LocalDef016) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => (i : Fin m) → ZMod (axis i).order
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `99623946eff23746f76cfaef266c4841d8670f064c5fbeb113546f91b09a42ae`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    (axis : Fin m → LocalDef016) →
      (∀ (k : Nat) (hk : instLENat.le k m) (x : LocalDef001 axis),
          Eq (LocalDef012 (LocalDef028 axis k x))
            (instHMul.hMul (LocalDef035 axis k hk).cast.sqrt (LocalDef012 x))) →
        LocalDef002 m
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3b946112d0abe20e495f583ea69db42cf3bc9b81af14163292fb98a0b8a8bb79`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.1
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cdd46b53687e6f5496f271a73a1e8dc68e00e7de21b77c7c8843ee0cef372e44`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → Fin m → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.3
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `91276a9dc92013ef4c863251ad13cca879fe4a85de9972124c972d0fc870ed79`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        (input : LocalDef001 plan.axis) →
          (computedState : Fin (instHAdd.hAdd m 1) → LocalDef001 plan.axis) →
            (localError : Fin m → LocalDef001 plan.axis) →
              Eq (computedState (Fin.last m)) input →
                (∀ (i : Fin m),
                    Eq (computedState i.castSucc)
                      (LocalDef053
                        (LocalDef048 plan.axis i (computedState i.succ)) (localError i))) →
                  Or
                      (Eq (LocalDef012 fun index => model.flInput (input index))
                        (LocalDef012 input))
                      (Exists fun inputFirstOrderCoeff =>
                        And (Real.instLE.le 0 inputFirstOrderCoeff)
                          (Real.instLE.le
                            (abs
                              (instHSub.hSub (LocalDef012 fun index => model.flInput (input index))
                                (LocalDef012 input)))
                            (instHMul.hMul inputFirstOrderCoeff model.epsilon))) →
                    Eq
                        (LocalDef034 (computedState 0)
                          (LocalDef028 plan.axis m input))
                        (LocalDef013 fun i =>
                          LocalDef028 plan.axis i.val (localError i)) →
                      LocalDef004 plan model
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `758362e33ce8b3fa5167f41197e83892b823a5079d7b4037e0f1236af702b298`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        {run : LocalDef004 plan model} →
          LocalDef005 run → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model run self => self.2
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5154d56f947bdf1eb6c8e3d596e424f5107288619fbbe1e995044101133c4fe6`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        {run : LocalDef004 plan model} →
          LocalDef005 run → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model run self => self.1
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `fdb7b47bbb09e0e5a4a3da42ad969cc754b22d1a7d53a6c3259a3246ac167c05`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        {run : LocalDef004 plan model} →
          (localSecondOrderCoeff intermediateFirstOrderCoeff : Fin m → Real) →
            (∀ (i : Fin m), Real.instLE.le 0 (localSecondOrderCoeff i)) →
              (∀ (i : Fin m), Real.instLE.le 0 (intermediateFirstOrderCoeff i)) →
                (∀ (i : Fin m),
                    Real.instLE.le (LocalDef012 (run.localError i))
                      (instHAdd.hAdd
                        (instHMul.hMul
                          (instHMul.hMul (instHMul.hMul model.epsilon (plan.axis i).order.cast.sqrt)
                            (LocalDef009 (plan.axis i) model.gamma))
                          (LocalDef012 (run.computedState i.succ)))
                        (instHMul.hMul (localSecondOrderCoeff i) (instHPow.hPow model.epsilon 2)))) →
                  (∀ (i : Fin m),
                      Real.instLE.le
                        (abs
                          (instHSub.hSub (LocalDef054 run i)
                            (LocalDef012 (LocalDef010 run))))
                        (instHMul.hMul (intermediateFirstOrderCoeff i) model.epsilon)) →
                    LocalDef005 run
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a2fd03b83e990147bebc92f2f807ff55eb76eb4dfbad186b76177bf62a61b60c`

Type:

```lean
(epsilon : Real) →
  Real.instLT.lt 0 epsilon →
    (gamma : Real) →
      Real.instLE.le 0 gamma →
        (flAdd flMul : Real → Real → Real) →
          (flSin flCos : Real → Real) →
            (Complex → Complex) →
              (∀ (a b : Real),
                  Exists fun θa =>
                    Exists fun θb =>
                      And (Real.instLE.le (abs θa) 1)
                        (And (Real.instLE.le (abs θb) 1)
                          (Eq (flAdd a b)
                            (instHAdd.hAdd (instHMul.hMul a (instHAdd.hAdd 1 (instHMul.hMul θa epsilon)))
                              (instHMul.hMul b (instHAdd.hAdd 1 (instHMul.hMul θb epsilon))))))) →
                (∀ (a b : Real),
                    Exists fun θ =>
                      And (Real.instLE.le (abs θ) 1)
                        (Eq (flMul a b)
                          (instHMul.hMul (instHMul.hMul a b) (instHAdd.hAdd 1 (instHMul.hMul θ epsilon))))) →
                  (∀ (a : Real),
                      Exists fun θ =>
                        And (Real.instLE.le (abs θ) 1)
                          (Eq (flSin a) (instHAdd.hAdd (Real.sin a) (instHMul.hMul (instHMul.hMul gamma θ) epsilon)))) →
                    (∀ (a : Real),
                        Exists fun θ =>
                          And (Real.instLE.le (abs θ) 1)
                            (Eq (flCos a)
                              (instHAdd.hAdd (Real.cos a) (instHMul.hMul (instHMul.hMul gamma θ) epsilon)))) →
                      LocalDef006
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b60f5ac019da1a3fd0ad923663ba7725552f79df3122d17c9b49ba4cc7fcf8c6`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef016) → Nat → LocalDef001 axis → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis x x_1 =>
  Nat.brecOn (motive := fun x => LocalDef001 axis → LocalDef001 axis) x
    (fun x f x_2 =>
      LocalDef047 axis
        (fun x x_3 =>
          Nat.below (motive := fun x => LocalDef001 axis → LocalDef001 axis) x →
            LocalDef001 axis)
        x x_2 (fun x x_3 => x) (fun i x x_3 => x_3.1 (LocalDef049 axis i x)) f)
    x_1
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `0f523dfa8fce0306ad4ba6f24b9c0346707db8e977ae0359ddd737ae4ac439aa`

Type:

```lean
∀ (axis : LocalDef016), NeZero axis.order
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `39bf931dc3e3c89fffaac8dff2c8d1d574287321eac447358e4a138c2b2e107e`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef039 n → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] plan γ =>
  instHAdd.hAdd (Finset.univ.sum fun i => LocalDef045 (plan.stage i).radix γ)
    (instHMul.hMul (instHSub.hSub plan.stageCount.cast 1) (instHAdd.hAdd 3 (instHMul.hMul 2 γ)))
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f2bf500a32533b731c58835c3f2fd9b22791b8d1420519850ad8522483da123d`

Type:

```lean
{m : Nat} → (Fin m → LocalDef016) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => Finset.univ.prod fun i => (axis i).order
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `be5fb8dfd2ed7e36db0d6afef6e875ce6bf0833ef02fb8a0434d34e0dd9f09a0`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run => run.computedState 0
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48236fad3382391914c5ff2f99d22cf425126bc757c4bbb8df1f90d28441d6a3`

Type:

```lean
{m : Nat} → {axis : Fin m → LocalDef016} → LocalDef001 axis → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => (PiLp.instNorm 2 fun x => Complex).norm { ofLp := x }
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3588b22bd63b6deec686a8935609888e8d92cb706e1794df440a0bf009b8604c`

Type:

```lean
{m : Nat} →
  {axis : Fin m → LocalDef016} →
    LocalDef001 axis → LocalDef001 axis → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x y index => instHSub.hSub (x index) (y index)
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a8fc38ff86b1b7bb48bc46e007123f661a796350c162003949ef31cc0a46fb00`

Type:

```lean
{m : Nat} → (Fin m → LocalDef016) → (k : Nat) → instLENat.le k m → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis k hk => Finset.univ.prod fun i => (axis (Fin.castLE hk i)).order
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `7638f0074825588b95a01498f0bb790ba39fd3189aec1bf96d302a093539cbd6`

Type:

```lean
∀ {m : Nat} (i : Fin m), instLENat.le i.val m
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `547809138f43cbaeb14dccba2cbd5b7a1a8e5e54ae5f635c217465c4654ff8e6`

Type:

```lean
(order : Nat) → (order_pos : instLTNat.lt 0 order) → LocalDef039 order → LocalDef016
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `11774d93f7d50a85aaf1a0a58afaddd2dd6b444cc5b48feecf1245e2876260eb`

Type:

```lean
∀ (self : LocalDef016), instLTNat.lt 0 self.order
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `8739482232d09489751c0a99db6a592be16ec50b24cf15ca3549aa089cc302cc`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ad56707f6a036114ec955d6b4ba9db86948c41400db74cd3b75d3d50717c33f1`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : LocalDef039 n) → Fin self.stageCount → LocalDef056 n
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.3
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `30921e98fa49eb94c73e56f2920669028bd7b13d1850716d80a2c796a715bb63`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef039 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `98246913018dc94a73395f1a8d9214f1cadb52c7030efdffdf28c4675bf9b56c`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `44c5459194d67168e8f0ac702a587aa83a2792a62fa5fe040198232d3bd652df`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} →
        LocalDef004 plan model → Fin (instHAdd.hAdd m 1) → LocalDef001 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.2
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `88461bf36f5d05f146587259086005272493e2b2632ee79ecb87ed470d76ed00`

Type:

```lean
LocalDef006 → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5f3504ac34a66a2d03bdab5ce4c356652a582c0b0cc9df3782e7c688f5b1a7d4`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun q γ =>
  ite (Eq q 2) (Real.sqrt 2) (ite (Eq q 4) 5 (instHMul.hMul (instHMul.hMul 2 q.cast.sqrt) (instHAdd.hAdd q.cast γ)))
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `f0d67c1f9aa937523ea334530fdcb9c54b0f8b36c58585f5368070a9577a9b30`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c160441d465cff79d8dc33e47d8de7179e40b4e4a715d4eaa089592791d1ab86`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef016) →
    (motive : Nat → LocalDef001 axis → Sort u_1) →
      (x : Nat) →
        (x_1 : LocalDef001 axis) →
          ((x : LocalDef001 axis) → motive 0 x) →
            ((i : Nat) → (x : LocalDef001 axis) → motive i.succ x) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3865f89f3e61cec86d2429803182f07bae31f9a19e30869bcdd010ed7f0b1467`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef016) → Fin m → LocalDef001 axis → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x index =>
  Finset.univ.sum fun j =>
    instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j (index i))) (x (Function.update index i j))
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6fc94bf3cebd6e3fabb89114ae63f2c4cfea2b593cecb67539f4a023709259e6`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef016) → Nat → LocalDef001 axis → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x => if hi : instLTNat.lt i m then LocalDef048 axis ⟨i, hi⟩ x else x
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `424d4812dc24ce5eebc2180fb1e04ea19aa51b9e55f6e5fc7bb423449fbfa114`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `674642470c470d06369345d70cb60942b316a75271b8635035c1b3030f14aa88`

Type:

```lean
∀ {m : Nat}, NeZero (instHAdd.hAdd m 1)
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d8bcafd62485c48aeb55b793b7c8c1538a318f4dbb89ce40a33eee63bc1a310e`

Type:

```lean
{m : Nat} → (axis : Fin m → LocalDef016) → Fintype (LocalDef019 axis)
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => inferInstance
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06d3f7851b61c80cef1171dccb27d472c83299aa1c38d2370624f0476d0f82fe`

Type:

```lean
{m : Nat} →
  {axis : Fin m → LocalDef016} →
    LocalDef001 axis → LocalDef001 axis → LocalDef001 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x y index => instHAdd.hAdd (x index) (y index)
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d9ac9e3ccd67cecaeab468c2be4beb79e0a69071a709f64100564518dd7291af`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef006} → LocalDef004 plan model → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  instHMul.hMul
    (instHMul.hMul (LocalDef035 plan.axis i.val ⋯).cast.sqrt (plan.axis i).order.cast.sqrt)
    (LocalDef012 (run.computedState i.succ))
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `224e3078b523d47eed4831ee496bf17a1d02b41fa0763d192246fcf22e2ee077`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (stageCount : Nat) →
      instLTNat.lt 0 stageCount →
        (stage : Fin stageCount → LocalDef056 n) →
          Eq (Finset.univ.prod fun i => (stage i).radix) n →
            (∀ (i : Fin stageCount),
                Eq (stage i).useTwiddle (Decidable.decide (instLTNat.lt (instHAdd.hAdd i.val 1) stageCount))) →
              (finalPermutation : Equiv (ZMod n) (ZMod n)) →
                LocalDef059 →
                  (∀ (x : ZMod n → Complex),
                      Eq (LocalDef065 finalPermutation (LocalDef062 stage x))
                        (LocalDef064 x)) →
                    Function.Surjective LocalDef064 →
                      (∀ (x : ZMod n → Complex),
                          Eq (LocalDef063 (LocalDef064 x))
                            (instHMul.hMul n.cast.sqrt (LocalDef063 x))) →
                        LocalDef039 n
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `97d9a0204d9304fae64c630fbd0563515344315fcdaec62c9e01341d19d5d52f`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `6fa74342f2d0b17a3ab9c3ded60e69ed185dc96f25e08cf01b0caca9b320f9a3`

Type:

```lean
(instHAdd.hAdd 4 1).AtLeastTwo
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `4b263ddd592e44637da6651c4be6ac2c7108305dccac0fcd37dbd547fa6b81c0`

Type:

```lean
∀ {m : Nat} (axis : Fin m → LocalDef016) (a : Fin m), NeZero (axis a).order
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `544b103df55e1b98d9b887d3b2d7c2cc664d2c26c1091e7aca4c4a8033ff8871`

Type:

```lean
Type
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `dcbff9d3438eae3b7802ac75cebdf2d4e715b88a5a5cb20f2c1c776119da2c31`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (radix : Nat) →
      Ne radix 0 →
        (blockCount : Nat) →
          Ne blockCount 0 →
            Eq (instHMul.hMul blockCount radix) n →
              Equiv (Prod (Fin blockCount) (ZMod radix)) (ZMod n) →
                Equiv (ZMod n) (ZMod n) → Bool → (ZMod n → ZMod n) → LocalDef056 n
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c9356ca2f52f0ec465420000f3867bc88b0192e7d791b2c028311a392d0ac69e`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → Bool
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.8
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6d1f89ec8780f8922da1b485245770d1366f3d55fbcea211c6be4de5132b638a`

Type:

```lean
{m n : Nat} → [inst : NeZero n] → (Fin m → LocalDef056 n) → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {m n} [NeZero n] stages x =>
  List.foldl (fun state stage => LocalDef069 stage state) x (List.ofFn stages)
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e2fc051f61fd90017931a86caf3ee831d484f55642763e9fba8c246d20220965`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => instHDiv.hDiv (LocalDef068 x) n.cast.sqrt
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e0c7199f0110602d33ed3aff3bd7a23cc1bf8bca0283972a54195512c519270c`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x k =>
  Finset.univ.sum fun j => instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j k)) (x j)
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5ed965dd03cc5016ab1b31e813a65f6c3565bf677ccb3b546de7e476adf28bc6`

Type:

```lean
{n : Nat} → Equiv (ZMod n) (ZMod n) → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} permutation x i => x (EquivLike.toFunLike.coe permutation i)
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `69e59fb4d683aea32786965a2fdadb98b19098f8c3bca20deaaf5f5edb125cf0`

Type:

```lean
LocalDef059
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `16d2014d9a2e84da81906b156a4f366a69aece557a34545c32bfb249d7457f42`

Type:

```lean
LocalDef059
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `dac663255b034b5dbbdb343457939be9dbbc50d68a1544b39f5567d1393fd306`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => (LocalDef074 x).sqrt
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `52f9e50ce9db2fa11f7db33f9492e55308a51a9d3bed484c7c7e660e87604af7`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x =>
  have permuted := fun i => x (EquivLike.toFunLike.coe stage.permutation i);
  have blocked := fun i =>
    have bi := EquivLike.toFunLike.coe stage.reindex.symm i;
    Finset.univ.sum fun j =>
      instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j bi.snd))
        (permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := j }));
  fun i =>
  ite (Eq stage.useTwiddle Bool.true)
    (instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (stage.twiddleExponent i)) (blocked i)) (blocked i)
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `0937910c9974bbc2e70ae36f7e93eb0631c166e136798bd95b2ff09cc0f0999d`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.3
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `b9f504d3f725fed8dad757d214d7c4c47cf61c082cdb013b946e7a30aabf55a6`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → Equiv (ZMod n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.7
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `374121ed62e4a39bd302ffbfa17a3d3e9359e4a3d9ac669a2dab912de210ebef`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : LocalDef056 n) → Equiv (Prod (Fin self.blockCount) (ZMod self.radix)) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.6
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `db98c941769582a85cce2f46995205dcf3183f1c6e723f8e405bf03932644209`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef056 n → ZMod n → ZMod n
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.9
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `bd70ea90c5242fc190eff58133ee8b749d712c4305a4737bde63afb0370210a4`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => Finset.univ.sum fun i => instHPow.hPow (Complex.instNorm.norm (x i)) 2
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `7`
- Semantic SHA-256: `f48b056ebd17901d63a6bf3cfa537dcc4dedf4bb58478a8045fbc9ad7cd6ed71`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : LocalDef056 n), NeZero stage.radix
```

### D076: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D077: `DivInvMonoid.toDiv`

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

### D078: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D079: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D080: `Fin.fintype`

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

### D081: `Finset.sum`

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

### D082: `Finset.univ`

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

### D083: `HAdd.hAdd`

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

### D084: `HDiv.hDiv`

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

### D085: `HMul.hMul`

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

### D086: `HPow.hPow`

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

### D087: `LE.le`

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

### D088: `LT.lt`

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

### D089: `Monoid.toNatPow`

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

### D090: `MulZeroClass.toZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a3f3ff8a43fb45098d9029196fe0a081ace6a8cc0c485317c7c17e719ec29c60`

Type:

```lean
{M₀ : Type u} → [self : MulZeroClass M₀] → Zero M₀
```

Definition body (one-level semantic boundary):

```lean
fun M₀ [self : MulZeroClass M₀] => self.2
```

### D091: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D092: `Nat.instMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Nat`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4c01f1e84ffddbe4a96559f1586583d0f7f5960c7ff89d25625db97dd017d56c`

Type:

```lean
MulZeroClass Nat
```

Definition body (one-level semantic boundary):

```lean
{ toMul := instMulNat, toZero := Nat.instAddMonoid.toAddZeroClass.toZero, zero_mul := Nat.zero_mul,
  mul_zero := Nat.mul_zero }
```

### D093: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

### D094: `OfNat.ofNat`

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

### D095: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D096: `Real.instAdd`

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

### D097: `Real.instAddCommMonoid`

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

### D098: `Real.instDivInvMonoid`

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

### D099: `Real.instLE`

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

### D100: `Real.instLT`

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

### D101: `Real.instMonoid`

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

### D102: `Real.instMul`

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

### D103: `Real.instZero`

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

### D104: `Zero.toOfNat0`

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

### D105: `instHAdd`

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

### D106: `instHDiv`

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

### D107: `instHMul`

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

### D108: `instHPow`

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

### D109: `instOfNatNat`

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

### D110: `Complex`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `06f5db8f409d6076be5ab5a3405277f735e30c46762deb074e76e94ef07eb934`

Type:

```lean
Type
```

### D111: `Complex.instNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Norm`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `016e82ad35ade5300cbdb12e36381b7f24f7d80411c91afa9ee359975ee96bd9`

Type:

```lean
NormedAddCommGroup Complex
```

Definition body (one-level semantic boundary):

```lean
{ toFun := Complex.instNorm.norm, map_zero' := Complex.norm_map_zero'✝, add_le' := Complex.norm_add_le'✝,
    neg' := Complex.norm_neg'✝,
    eq_zero_of_map_eq_zero' := Complex.instNormedAddCommGroup._proof_1 }.toNormedAddCommGroup
```

### D112: `Complex.instNormedField`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `08caf8897c319d3b5d8e17da052a9444ceb5f7bcaf585d54f79028085ec6333f`

Type:

```lean
NormedField Complex
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Complex.instNorm, toField := Complex.instField,
  toMetricSpace := Complex.instNormedAddCommGroup.toMetricSpace, dist_eq := Complex.instNormedField._proof_1,
  norm_mul := Complex.norm_mul }
```

### D113: `ENormedAddCommMonoid.toESeminormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `7d58c19063063d627291b91068fa4bf2bf5ff88679897376ac465b9f52e93642`

Type:

```lean
{E : Type u_8} → {inst : TopologicalSpace E} → [self : ENormedAddCommMonoid E] → ESeminormedAddCommMonoid E
```

Definition body (one-level semantic boundary):

```lean
fun E {inst} [self : ENormedAddCommMonoid E] => self.1
```

### D114: `ESeminormedAddCommMonoid.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `38db724db757c42f8e8affdaa0b60310db98b78e8ba320c452775788f7191220`

Type:

```lean
{E : Type u_8} → [inst : TopologicalSpace E] → [self : ESeminormedAddCommMonoid E] → AddCommMonoid E
```

Definition body (one-level semantic boundary):

```lean
fun E [TopologicalSpace E] self => { toAddMonoid := self.toAddMonoid, add_comm := ⋯ }
```

### D115: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D116: `Nat.cast`

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

### D117: `NormedAddCommGroup.toENormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Continuity`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `eac639a9ae15f19554f668c9811538a135f4f05df04330bd8145b300efe57cfb`

Type:

```lean
{E : Type u_4} → [inst : NormedAddCommGroup E] → ENormedAddCommMonoid E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : NormedAddCommGroup E] =>
  let __spread.0 := NormedAddGroup.toENormedAddMonoid;
  have __spread.1 := inst;
  { toESeminormedAddMonoid := __spread.0.toESeminormedAddMonoid, add_comm := ⋯, enorm_eq_zero := ⋯ }
```

### D118: `NormedCommRing.toSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D119: `NormedField.toNormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Field.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4aa3dba57859ca72552799005279a2b5a65b8c083980070fbbff11fd1de56dec`

Type:

```lean
{α : Type u_2} → [NormedField α] → NormedCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : NormedField α] =>
  let __src := inst;
  { toNorm := __src.toNorm, toRing := __src.toRing, toMetricSpace := __src.toMetricSpace, dist_eq := ⋯,
    norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D120: `PseudoMetricSpace.toUniformSpace`

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

### D121: `Real.instNatCast`

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

### D122: `Real.sqrt`

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

### D123: `SeminormedCommRing.toSeminormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e3cbc92d1d5e37d9eaeb1d595c83a78f7af7e3a8d249a700fa3676ab4e0c3d60`

Type:

```lean
{α : Type u_5} → [self : SeminormedCommRing α] → SeminormedRing α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedCommRing α] => self.1
```

### D124: `SeminormedRing.toPseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e6ea9296e8643d5ae7cf334c065c9d6ebe4a95de22d3b0708a585db80e17322a`

Type:

```lean
{α : Type u_5} → [self : SeminormedRing α] → PseudoMetricSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedRing α] => self.3
```

### D125: `UniformSpace.toTopologicalSpace`

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

### D126: `AddCommMonoidWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `07f48d3cfc3c7c30b6298df8531409d9844ab8c7e0ba94dea2a3fd29879320af`

Type:

```lean
{R : Type u_2} → [self : AddCommMonoidWithOne R] → AddMonoidWithOne R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddCommMonoidWithOne R] => self.1
```

### D127: `AddMonoidWithOne.toNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6b956e88ee642e7533983b76ff8087f4537eea04f025165ce1fa45dc80e795a2`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → NatCast R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.1
```

### D128: `Complex.instNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Norm`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1cfad456b65aa5b5a2b02b8a83a1499ef6fccab64640c73c839132b51fed64cc`

Type:

```lean
Norm Complex
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun z => (MonoidWithZeroHom.funLike.coe Complex.normSq z).sqrt }
```

### D129: `Complex.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `26cc7a92ad47bfd4a81e9b47e27ff96a00a409cbd8b04b21b458f7c67849aa8d`

Type:

```lean
Sub Complex
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun z w => { re := instHSub.hSub z.re w.re, im := instHSub.hSub z.im w.im } }
```

### D130: `ENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5b8f4d61311ebccecf6a54ceca44191d394e0108c8596129a77f03c15a7e457f`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
WithTop NNReal
```

### D131: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D132: `Fin.castLE`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `741eedcc1330cedb8ff0a69095d6df1438c40a8c734f1526dc385e45bb9ae135`

Type:

```lean
{n m : Nat} → instLENat.le n m → Fin n → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} h i => ⟨i.val, ⋯⟩
```

### D133: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D134: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8f9c302902ae8c66b3f71728ffe02994a026b562f27b9df8d4f84793e455e26b`

Type:

```lean
{n : Nat} → [NeZero n] → {i : Nat} → OfNat (Fin n) i
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] {i} => { ofNat := Fin.ofNat n i }
```

### D135: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`

Type:

```lean
(n : Nat) → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun n => ⟨n, ⋯⟩
```

### D136: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D137: `Finset.prod`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e364cffe1f2457eedceca9fe0617d7a66084963ffb6e6ed760d1f3fe74eee841`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [CommMonoid M] s f => (Multiset.map f s.val).prod
```

### D138: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D139: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D140: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D141: `Nat.instCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d946a6ce034e0404ae6836f267c26c67248cfd19fa68c2f7b9e321695d4f7c86`

Type:

```lean
CommMonoid Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul, mul_assoc := Nat.mul_assoc, one := Nat.zero.succ, one_mul := Nat.one_mul, mul_one := Nat.mul_one,
  npow := fun m n => instHPow.hPow n m, npow_zero := Nat.pow_zero, npow_succ := Nat.instCommMonoid._proof_1,
  mul_comm := Nat.mul_comm }
```

### D142: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D143: `Nat.ne_of_gt`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `efc85b6e2ba577017c57d5b88a2d6f39eaa33310359c247b44f3ff338427ac62`

Type:

```lean
∀ {a b : Nat}, instLTNat.lt b a → Ne a b
```

### D144: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D145: `NeZero.mk`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e2e32989d835a09f096b510efd93c48c325d5131f0dc0608e4b63d8e6448d9ad`

Type:

```lean
∀ {R : Type u_1} [inst : Zero R] {n : R}, Ne n 0 → NeZero n
```

### D146: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D147: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D148: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

### D149: `PiLp.instNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.PiLp`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f24beda1ba0ca545fc281a05cd134dcc3c729e2eabbfac59f4340d15384ca425`

Type:

```lean
(p : ENNReal) → {ι : Type u_2} → (β : ι → Type u_4) → [Fintype ι] → [(i : ι) → Norm (β i)] → Norm (PiLp p β)
```

Definition body (one-level semantic boundary):

```lean
fun p {ι} β [Fintype ι] [inst_1 : (i : ι) → Norm (β i)] =>
  {
    norm := fun f =>
      ite (Eq p 0) ⋯.toFinset.card.cast
        (ite (Eq p instTopENNReal.top) (iSup fun i => (inst_1 i).norm (f.ofLp i))
          (instHPow.hPow (Finset.univ.sum fun i => instHPow.hPow ((inst_1 i).norm (f.ofLp i)) p.toReal)
            (instHDiv.hDiv 1 p.toReal))) }
```

### D150: `Real.cos`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1377d30c9decd42f763baf8cb45f365ee121aec3ccf9f371c298d2926eba5a53`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => (Complex.cos (Complex.ofReal x)).re
```

### D151: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D152: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D153: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D154: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D155: `Real.sin`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7937a67d5952a981d1a70df574b1d79c6e87542f5d15a2b0fe35a8fe8d31811f`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => (Complex.sin (Complex.ofReal x)).re
```

### D156: `WithLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `beeca7e7d011bf353b991ee4fb3bf57a00fca40fd553001d24ad8181bda346e3`

Type:

```lean
ENNReal → Type u_1 → Type u_1
```

### D157: `WithLp.toLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `293799c52cddc04402243afb567ab5aa26e35f2b7064cbec3d87dc7fba0ba006`

Type:

```lean
(p : ENNReal) → {V : Type u_1} → V → WithLp p V
```

### D158: `ZMod`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `16bf0604575e2049c78de15301315a487d981f9b4918a56c63dc9410569ff212`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun x => ZMod.match_1 (fun x => Type) x (fun _ => Int) fun n => Fin (instHAdd.hAdd n 1)
```

### D159: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D160: `instAddCommMonoidWithOneENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `31d9551885e3007e5d1368365622cfd7638ea41cc6d885234041621de873f55c`

Type:

```lean
AddCommMonoidWithOne ENNReal
```

Definition body (one-level semantic boundary):

```lean
WithTop.addCommMonoidWithOne
```

### D161: `instAddNat`

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

### D162: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D163: `instLENat`

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

### D164: `instNeZeroNatHAdd_1`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `4cf1e3f35432e064f333472fa6363b628df31521c110222df9633f8b8ba8cd25`

Type:

```lean
∀ {n m : Nat} [h : NeZero m], NeZero (instHAdd.hAdd n m)
```

### D165: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D166: `AddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `4f50638d97f5d425f8c05152b76b46854b453bc1d6f50f0e215f12ac557f8270`

Type:

```lean
(A : Type u_1) → [AddMonoid A] → (M : Type u_2) → [Monoid M] → Type (max u_1 u_2)
```

### D167: `AddChar.instFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `83e85a9db1d0e5ecf4333397f4d7bc036d1237ee1458184cbc4f34ac900b688e`

Type:

```lean
{A : Type u_1} → {M : Type u_3} → [inst : AddMonoid A] → [inst_1 : Monoid M] → FunLike (AddChar A M) A M
```

Definition body (one-level semantic boundary):

```lean
fun {A} {M} [AddMonoid A] [Monoid M] => { coe := AddChar.toFun, coe_injective' := ⋯ }
```

### D168: `AddGroupWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Int.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ab901b5dbbaa698c61da5b353ee51145e713b8971414a6fdb991cde02b5cb677`

Type:

```lean
{R : Type u} → [self : AddGroupWithOne R] → AddMonoidWithOne R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddGroupWithOne R] => self.2
```

### D169: `AddMonoidWithOne.toAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `4fa12ffa6a6fee7c2d3050177e382f5c7883895f706698d037c6b045bef31105`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → AddMonoid R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.2
```

### D170: `CommRing.toNonUnitalCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `1c9ac43c2f2e02a3e345036ace32d209b04abe0516407e31bcb54ee4c7201d0d`

Type:

```lean
{α : Type u} → [s : CommRing α] → NonUnitalCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [s : CommRing α] =>
  { toAddMonoid := s.toAddMonoid, toNeg := s.toNeg, toSub := s.toSub, sub_eq_add_neg := ⋯, zsmul := s.zsmul,
    zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯, toMul := s.toMul,
    left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, mul_comm := ⋯ }
```

### D171: `CommRing.toRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `c018410d7cd7a0cf748bc89452a2d03cd223cfa1f0ad262b865497873fcc8648`

Type:

```lean
{α : Type u} → [self : CommRing α] → Ring α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : CommRing α] => self.1
```

### D172: `Complex.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `dd8fdb776f3b7e3d1d0374b238287ec761577d2b078497d976639abf335d4179`

Type:

```lean
Add Complex
```

Definition body (one-level semantic boundary):

```lean
{ add := fun z w => { re := instHAdd.hAdd z.re w.re, im := instHAdd.hAdd z.im w.im } }
```

### D173: `Complex.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `3907754dc21e8763597dbf54bef08573c003d8f4d8def69e55d2b222d3fe9015`

Type:

```lean
Mul Complex
```

Definition body (one-level semantic boundary):

```lean
{
  mul := fun z w =>
    { re := instHSub.hSub (instHMul.hMul z.re w.re) (instHMul.hMul z.im w.im),
      im := instHAdd.hAdd (instHMul.hMul z.re w.im) (instHMul.hMul z.im w.re) } }
```

### D174: `Complex.instSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `008d132dd980a88182937c2214239a242f0e05220ab73a658ec569ddc4ad3f3e`

Type:

```lean
Semiring Complex
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D175: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D176: `Distrib.toMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `1d05ddf657021fb5615c5054f46b4863aec4ca856ca48fbb75add25e1f0fe06f`

Type:

```lean
{R : Type u_1} → [self : Distrib R] → Mul R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : Distrib R] => self.1
```

### D177: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D178: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

### D179: `Function.update`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `092e6c4864b94365603f748d7cf0dd798223b04b127d4c37969b0c09cac29193`

Type:

```lean
{α : Sort u} → {β : α → Sort v} → [DecidableEq α] → ((a : α) → β a) → (a' : α) → β a' → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] f a' v a => if h : Eq a a' then Eq.ndrec v ⋯ else f a
```

### D180: `MonoidWithZero.toMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `c0f91ccdc0415c148969849b7a83ce67d87cf4c402704186fa19f6313928d90f`

Type:

```lean
{M₀ : Type u} → [self : MonoidWithZero M₀] → Monoid M₀
```

Definition body (one-level semantic boundary):

```lean
fun M₀ [self : MonoidWithZero M₀] => self.1
```

### D181: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D182: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D183: `Nat.decLt`

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

### D184: `NonUnitalCommRing.toNonUnitalNonAssocCommRing`

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

### D185: `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing`

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

### D186: `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`

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

### D187: `NonUnitalNonAssocSemiring.toDistrib`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `5b49ec28e539eea6192ab07a9aee6da537ed1b5e017f2b9ef44d3a0ae51d79c6`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → Distrib α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toMul := self.toMul, toAdd := self.toAdd, left_distrib := ⋯, right_distrib := ⋯ }
```

### D188: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D189: `Pi.instFintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Pi`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `38af89fa29e8604e3102e2493be25045731e11c8f462c08498d78926b091d1fa`

Type:

```lean
{α : Type u_3} →
  {β : α → Type u_4} → [DecidableEq α] → [Fintype α] → [(a : α) → Fintype (β a)] → Fintype ((a : α) → β a)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] [Fintype α] [(a : α) → Fintype (β a)] =>
  { elems := Fintype.piFinset fun x => Finset.univ, complete := ⋯ }
```

### D190: `Ring.toAddGroupWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `d15833ebecad60e5e3b68aad85ba35db45194f877d115020c7add9b4f99d6aaf`

Type:

```lean
{R : Type u} → [self : Ring R] → AddGroupWithOne R
```

Definition body (one-level semantic boundary):

```lean
fun R self =>
  { toIntCast := self.toIntCast, toNatCast := self.toNatCast, toAddMonoid := self.toAddMonoid, toOne := self.toOne,
    natCast_zero := ⋯, natCast_succ := ⋯, toNeg := self.toNeg, toSub := self.toSub, sub_eq_add_neg := ⋯,
    zsmul := self.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, intCast_ofNat := ⋯,
    intCast_negSucc := ⋯ }
```

### D191: `Semiring.toMonoidWithZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `bf0d463c55fbfcd762eb28ad6f1672fe482a72dfed67d13a797c09f1f0431e64`

Type:

```lean
{α : Type u} → [self : Semiring α] → MonoidWithZero α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toMul := self.toMul, mul_assoc := ⋯, toOne := self.toOne, one_mul := ⋯, mul_one := ⋯, npow := self.npow,
    npow_zero := ⋯, npow_succ := ⋯, toZero := self.toZero, zero_mul := ⋯, mul_zero := ⋯ }
```

### D192: `ZMod.commRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `15f1fcdfc5a4734b26869ae51723622c35f340d748486c74b75b03d93ed217af`

Type:

```lean
(n : Nat) → CommRing (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n =>
  { add := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instAdd.add fun n => Fin.instAdd.add,
    add_assoc := ⋯, zero := Nat.casesOn n 0 fun n => 0, zero_add := ⋯, add_zero := ⋯,
    nsmul :=
      Nat.casesOn (motive := fun x => Nat → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).nsmul fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).nsmul,
    nsmul_zero := ⋯, nsmul_succ := ⋯, add_comm := ⋯,
    mul := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instMul.mul fun n => Fin.instMul.mul,
    left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    one := Nat.casesOn n 1 fun n => 1, one_mul := ⋯, mul_one := ⋯,
    natCast := Nat.casesOn (motive := fun x => Nat → ZMod x) n Nat.cast fun n => Nat.cast, natCast_zero := ⋯,
    natCast_succ := ⋯,
    npow :=
      Nat.casesOn (motive := fun x => Nat → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).npow fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).npow,
    npow_zero := ⋯, npow_succ := ⋯,
    neg := Nat.casesOn (motive := fun x => ZMod x → ZMod x) n Int.instNegInt.neg fun n => (Fin.neg n.succ).neg,
    sub := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instSub.sub fun n => Fin.instSub.sub,
    sub_eq_add_neg := ⋯,
    zsmul :=
      Nat.casesOn (motive := fun x => Int → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).zsmul fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).zsmul,
    zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    intCast := Nat.casesOn (motive := fun x => Int → ZMod x) n (fun x => x) fun n => Int.cast, intCast_ofNat := ⋯,
    intCast_negSucc := ⋯, mul_comm := ⋯ }
```

### D193: `ZMod.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b61a1a310a01eaff03d99e3a9cee83c616fb078b27baacf352225f96ff75d7d7`

Type:

```lean
(n : Nat) → [NeZero n] → Fintype (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  ZMod.fintype.match_1 (fun x x_2 => Fintype (ZMod x)) x x_1 (fun h => ⋯.elim) fun n x =>
    Fin.fintype (instHAdd.hAdd n 1)
```

### D194: `ZMod.stdAddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d8823a1e47eaa4d04423dedbc65db89ecb2a2b5484d0ac20a437a96d1f98677a`

Type:

```lean
{N : Nat} → [NeZero N] → AddChar (ZMod N) Complex
```

Definition body (one-level semantic boundary):

```lean
fun {N} [NeZero N] => Circle.coeHom.compAddChar ZMod.toCircle
```

### D195: `Zero.ofOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d610ee8a0a2a61b7850d6032e696e6ae93221da787dff4096e98d4122502f26d`

Type:

```lean
{α : Type u_1} → [OfNat α 0] → Zero α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [OfNat α 0] => { zero := 0 }
```

### D196: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `a2551097d29bac847f3c59e8213b5882afd4a95e9247c2382e8bce33011974b5`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (c → α) → (Not c → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h e t
```

### D197: `inferInstance`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `a035e8579f88a0c5ce0a542c50396cd8f34aa652df8abeec2eb80c43a343b97b`

Type:

```lean
{α : Sort u} → [i : α] → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [i : α] => i
```

### D198: `instDecidableEqFin`

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

### D199: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

Type:

```lean
DecidableEq Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D200: `instLTNat`

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

### D201: `ite`

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

### D202: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D203: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ff90c894e4369b89945915c4c814dd76d90e450369a804cfc4139fada64048b2`

Type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Definition body (one-level semantic boundary):

```lean
fun p [h : Decidable p] => Decidable.casesOn h (fun x => Bool.false) fun x => Bool.true
```

### D204: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

### D205: `Function.Surjective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `445be13b68e9dc4df2e669e26d66cfeb452be0838a57a48f28fe13bacbab89c0`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ (b : β), Exists fun a => Eq (f a) b
```

### D206: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D207: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D208: `List.foldl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D209: `List.ofFn`

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

### D210: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D211: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D212: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `15abc50804fa78aecc5a807f82f13a6b67bcdff9061558426471fc4b606841aa`

Type:

```lean
Mul Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul }
```

### D213: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

### D214: `Equiv.symm`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `57ee9c638939cfeecafbbd4c55de44dd6a442327ab164c9ed3cd729233289347`

Type:

```lean
{α : Sort u} → {β : Sort v} → Equiv α β → Equiv β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} e => { toFun := e.invFun, invFun := e.toFun, left_inv := ⋯, right_inv := ⋯ }
```

### D215: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `31dfcc70f250d68311839281cfb552859ef6a5cdd31e725091d6a2a2f7fb2165`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D216: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

### D217: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `a70aebf9da319c4b02023421b33923182c4d5164c2087035016589b80ed1191a`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D218: `instDecidableEqBool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `dedf43b35e221c78c811d0b7268b7be703d67b744ad16b23df01af14b2aa5899`

Type:

```lean
DecidableEq Bool
```

Definition body (one-level semantic boundary):

```lean
Bool.decEq
```
