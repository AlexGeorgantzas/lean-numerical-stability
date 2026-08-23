# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m : Nat} [inst : NeZero m] (plan : LocalDef002 m) (γ : Real)
  (family : LocalDef001 plan γ)
  (axisBounds : LocalDef005 family),
  Real.instLT.lt 0 (LocalDef009 (LocalDef007 family)) →
    Exists fun secondOrderCoeff =>
      And (Real.instLE.le 0 secondOrderCoeff)
        (Exists fun radius =>
          And (Real.instLT.lt 0 radius)
            (∀ (ε : LocalDef004),
              Real.instLE.le ε.val radius →
                Real.instLE.le
                  (instHDiv.hDiv (LocalDef009 (LocalDef008 family ε))
                    (LocalDef009 (LocalDef007 family)))
                  (instHAdd.hAdd (instHMul.hMul ε.val (Finset.univ.sum fun i => LocalDef006 (plan.axis i) γ))
                    (instHMul.hMul secondOrderCoeff (instHPow.hPow ε.val 2)))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m]
  (plan : @LocalDef002 m inst) (γ : Real)
  (family : @LocalDef001 m inst plan γ)
  (axisBounds : @LocalDef005 m inst plan γ family)
  (hexactOutput :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@LocalDef009 m (@LocalDef003 m inst plan)
        (@LocalDef007 m inst plan γ family))),
  @Exists.{1} Real fun (secondOrderCoeff : Real) =>
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        secondOrderCoeff)
      (@Exists.{1} Real fun (radius : Real) =>
        And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            radius)
          (∀ (ε : LocalDef004),
            @LE.le.{0} Real Real.instLE
                (@Subtype.val.{1} Real
                  (fun (ε : Real) =>
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                  ε)
                radius →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@LocalDef009 m (@LocalDef003 m inst plan)
                    (@LocalDef008 m inst plan γ family ε))
                  (@LocalDef009 m (@LocalDef003 m inst plan)
                    (@LocalDef007 m inst plan γ family)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Subtype.val.{1} Real
                      (fun (ε : Real) =>
                        @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                      ε)
                    (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
                      fun (i : Fin m) =>
                      LocalDef006 (@LocalDef003 m inst plan i) γ))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) secondOrderCoeff
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@Subtype.val.{1} Real
                        (fun (ε : Real) =>
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                        ε)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `d05d5686c6b18c0c59b6d9f4ad503f21b4637b5c6696b1994b99f70f69de41c3`

Type:

```lean
{m : Nat} → [inst : NeZero m] → LocalDef002 m → Real → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `58bab8e315f44effb185c1d33c722eff095b555eb7ca8dd500dbb46d9ef6e139`

Type:

```lean
(m : Nat) → [NeZero m] → Type
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4f110c9cf1b68a953de7ce0fe7079241b2b00d4c3d894621f816d6d6fee42e66`

Type:

```lean
{m : Nat} → [inst : NeZero m] → LocalDef002 m → Fin m → LocalDef014
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] self => self.1
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `beaffc17a0637e2134854464050914551f29b26c09b92cbdd3d2ca9db575822a`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
Subtype fun ε => Real.instLT.lt 0 ε
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `0c60dcd3f7eeab991738509407a3367e7ac62c71c3aa922c9cb7acfb2c85ad9e`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} → LocalDef001 plan γ → Type
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ae8163a8ca36c47b293ac8b68040f731a151b3d64a7bba3a80d5e2ac046c01c`

Type:

```lean
LocalDef014 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun axis γ => LocalDef022 axis.plan γ
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2b55efdad40a9e14c40a09c8158e5be74b52559641acc5f8623ed7307fad0aca`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} → LocalDef001 plan γ → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {γ} family => LocalDef020 plan.axis m family.input
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3dcad2f55a16277e4401b13dbee598cdd3ad233513b81c7912cdd179e2107b23`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} →
        LocalDef001 plan γ →
          LocalDef004 → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {γ} family ε =>
  LocalDef026 (LocalDef024 (family.run ε))
    (LocalDef007 family)
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6eee10965db8466a35204629cd892a83cd68269afa7c165c04ad4c86d9e5e9e7`

Type:

```lean
{m : Nat} → {axis : Fin m → LocalDef014} → LocalDef017 axis → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => instHDiv.hDiv (LocalDef025 x) (LocalDef023 axis).cast.sqrt
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0aa258366ee6c13873f937e207223fa0b65ab3c5953b507ef0b3e0331b6c8b4c`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} → LocalDef001 plan γ → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.2
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `423bb3c4e8aefb13eda1e6ba24d2d5389d1d853aeb42b6fad273b5e4a97a9b47`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} →
        Real.instLE.le 0 γ →
          (input : LocalDef017 plan.axis) →
            (model : LocalDef004 → LocalDef037) →
              (∀ (ε : LocalDef004), Eq (model ε).epsilon ε.val) →
                (∀ (ε : LocalDef004), Eq (model ε).gamma γ) →
                  (run : (ε : LocalDef004) → LocalDef034 plan (model ε)) →
                    (∀ (ε : LocalDef004), Eq (run ε).input input) →
                      LocalDef001 plan γ
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b897022e460d5361f9607e799acbda7145c14300bc49abdb25ddcc70417b781c`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} →
        LocalDef001 plan γ →
          LocalDef004 → LocalDef037
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.3
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `93471286ff34c2ec5a540995ec567cd6b8fd9ed10e5f24d7319aa7bc677835d8`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} →
        (self : LocalDef001 plan γ) →
          (ε : LocalDef004) → LocalDef034 plan (self.model ε)
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.6
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ac66534455188396047a24b2dc5dec1df9477b2eb3f74be4e03fbe9e759b3c4f`

Type:

```lean
Type
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9a844cefb047ec694462340588b90aa4a1eb84beb0b1a5a1e9e1ee8b02595e02`

Type:

```lean
LocalDef014 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b3432d3a4dcdb8a08c47c7f6290a10957c5d2a7ba05a5b33a6d76d36eb99c63b`

Type:

```lean
(self : LocalDef014) → LocalDef029 self.order
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2f9ce4011814cb13d57a3f5520aeb8e5b4c5e9c6ca44b6da84ece99e718e1ac0`

Type:

```lean
{m : Nat} → (Fin m → LocalDef014) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => LocalDef033 axis → Complex
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `3ed2bbd90ecca022b810ebf3044f9769f3c6330fda82583fab6398a84353607b`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    (axis : Fin m → LocalDef014) →
      (∀ (k : Nat) (hk : instLENat.le k m) (x : LocalDef017 axis),
          Eq (LocalDef009 (LocalDef020 axis k x))
            (instHMul.hMul (LocalDef047 axis k hk).cast.sqrt (LocalDef009 x))) →
        LocalDef002 m
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `58cf28bc10bdf6961ba67f2133e5ff898982872d1214b6871dbb3dfeae8c4822`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {γ : Real} →
        {family : LocalDef001 plan γ} →
          (localSecondOrderCoeff : Fin m → Real) →
            (∀ (i : Fin m), Real.instLE.le 0 (localSecondOrderCoeff i)) →
              (radius : Real) →
                Real.instLT.lt 0 radius →
                  (∀ (ε : LocalDef004),
                      Real.instLE.le ε.val radius →
                        ∀ (i : Fin m),
                          Real.instLE.le (LocalDef009 (LocalDef048 (family.run ε) i))
                            (instHAdd.hAdd
                              (instHMul.hMul (instHMul.hMul ε.val (LocalDef006 (plan.axis i) γ))
                                (LocalDef049 (family.run ε) i))
                              (instHMul.hMul (localSecondOrderCoeff i) (instHPow.hPow ε.val 2)))) →
                    LocalDef005 family
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd827baff3bc1c82b878f4ab9412f49737659b6ba14c6339c01d09b26ae23f56`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef014) → Nat → LocalDef017 axis → LocalDef017 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis x x_1 =>
  Nat.brecOn (motive := fun x => LocalDef017 axis → LocalDef017 axis) x
    (fun x f x_2 =>
      LocalDef042 axis
        (fun x x_3 =>
          Nat.below (motive := fun x => LocalDef017 axis → LocalDef017 axis) x →
            LocalDef017 axis)
        x x_2 (fun x x_3 => x) (fun i x x_3 => x_3.1 (LocalDef043 axis i x)) f)
    x_1
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `edf8eb530e4de69022d7e6aba03bd4f4a8892d564b0a25aea87576d7ce058e2b`

Type:

```lean
∀ (axis : LocalDef014), NeZero axis.order
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd675c229b9fa903ef8bc454abb7ca04d584da2f71399f32f0893ab66e78aeb4`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef029 n → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] plan γ =>
  instHAdd.hAdd (Finset.univ.sum fun i => LocalDef040 (plan.stage i).radix γ)
    (instHMul.hMul (instHSub.hSub plan.stageCount.cast 1) (instHAdd.hAdd 3 (instHMul.hMul 2 γ)))
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c6f5ee16e064cc48c4b30549e7081a27fc5cb52dfaf0efe4b55c47f65cbd2916`

Type:

```lean
{m : Nat} → (Fin m → LocalDef014) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => Finset.univ.prod fun i => (axis i).order
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f5a5a454db23d56a07eb881bbafbff8dd4ac1648d00e40ed0a8179233ff78543`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        LocalDef034 plan model → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run => run.computedState 0
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a2959c76d4fcecf46d1d1c3d6b3cf0f954d9bd8c73d5cb3f35b4ef1173797a5d`

Type:

```lean
{m : Nat} → {axis : Fin m → LocalDef014} → LocalDef017 axis → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => (PiLp.instNorm 2 fun x => Complex).norm { ofLp := x }
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `17a2e90cf50d4a2223edb4a0ac0dac08bc748ae303ecd2570d356d2a134085d6`

Type:

```lean
{m : Nat} →
  {axis : Fin m → LocalDef014} →
    LocalDef017 axis → LocalDef017 axis → LocalDef017 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x y index => instHSub.hSub (x index) (y index)
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e6932f525aaf103773642eaa6ac58f458c33c4a28215567401e60c1a14d1e63f`

Type:

```lean
(order : Nat) → (order_pos : instLTNat.lt 0 order) → LocalDef029 order → LocalDef014
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `cd325b50a3f2d950540c358bf3d3fe994ea81ae59412face1a635bd048549ad1`

Type:

```lean
∀ (self : LocalDef014), instLTNat.lt 0 self.order
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `773b59c0343db6824933ffd9eaca8956809e69ed57df9d1df00ca0a512fd9cf9`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `26bdd691cae4e7dccd873b3d4e2f8e6acc0d579b4b693a56cda8b84cf81f647a`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : LocalDef029 n) → Fin self.stageCount → LocalDef051 n
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.3
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `30ab40fa47995b63b1565b7425deadb31034b8e5eb50c4ce28fcbf1f41a4724b`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef029 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `468911f06d3c718429ca65245988f62b98377f7d7648153228b930bbe9358eef`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d973f8a39a59e78c19aa706841d53c945249d626875d1297c105d303dad1fb68`

Type:

```lean
{m : Nat} → (Fin m → LocalDef014) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => (i : Fin m) → ZMod (axis i).order
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `876c6afa53aa36168b61e5b894e88a15ff2c6961bf2a6d30155b0102ec51263a`

Type:

```lean
{m : Nat} → [inst : NeZero m] → LocalDef002 m → LocalDef037 → Type
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c3374523bbfbc42ab75c69ecd351f84e9abfde35fe203c838a1b06708d10c243`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        LocalDef034 plan model → Fin (instHAdd.hAdd m 1) → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.2
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f55929524fb5c391c159443dbdb100a8bdbe998fe0ad5b0ed4c51d3335adb68a`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        LocalDef034 plan model → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.1
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `c7339f4ea02dd9cfdae11d3d03937bb79376d62f6d50b4bd3b3a857c02fe2728`

Type:

```lean
Type
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `710e3ebacedae5bde70ccdf11768df1bab629b60ff87cf70e8ab4f5e14f3d687`

Type:

```lean
LocalDef037 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `338fc4d07b6457fb813e32f105b95cb112e42125bdf72f24736d6b0e4956d063`

Type:

```lean
LocalDef037 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c606d19a89a02456d06023ca3fdcae9710ad57298e71db6ef1dcda9da539074d`

Type:

```lean
Nat → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun q γ =>
  ite (Eq q 2) (Real.sqrt 2) (ite (Eq q 4) 5 (instHMul.hMul (instHMul.hMul 2 q.cast.sqrt) (instHAdd.hAdd q.cast γ)))
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `dfed3ec56d4bb1b4d13cb4e24bd15dcacdbd2f1f8f2e4c150658454e768ae9a9`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `236ac002bf53dca67fe09fbec8832569ac4c1b3a6ea4221a7ad4f57b906fb6ec`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef014) →
    (motive : Nat → LocalDef017 axis → Sort u_1) →
      (x : Nat) →
        (x_1 : LocalDef017 axis) →
          ((x : LocalDef017 axis) → motive 0 x) →
            ((i : Nat) → (x : LocalDef017 axis) → motive i.succ x) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7ebe006704510fd5a6e39f79fbc1455373aa630b151bffe2b2ffa099992c53fe`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef014) → Nat → LocalDef017 axis → LocalDef017 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x => if hi : instLTNat.lt i m then LocalDef056 axis ⟨i, hi⟩ x else x
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `adfe6af1174d8fcac0c7a06078c0cdb374594faed75a449c3fa4a00bc0242be0`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `aeb0224e18190851754ceb4dad01f755e356b698ee50f14799402dbe28c3c13a`

Type:

```lean
∀ {m : Nat}, NeZero (instHAdd.hAdd m 1)
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4d533a705d545f677469b8b56e5c398d8c65bbf78bdc6a5625f087fe003f10f3`

Type:

```lean
{m : Nat} → (axis : Fin m → LocalDef014) → Fintype (LocalDef033 axis)
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => inferInstance
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9f8907da618e1cfdb879834cb3fd959ccea5f7a359a6389b068f26476ef4387f`

Type:

```lean
{m : Nat} → (Fin m → LocalDef014) → (k : Nat) → instLENat.le k m → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis k hk => Finset.univ.prod fun i => (axis (Fin.castLE hk i)).order
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a4d7c6586c8dfee1f8ecfd638208c4f41357952c9ee5bdda04404e3a7917df45`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        LocalDef034 plan model → Fin m → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  LocalDef020 plan.axis i.val (LocalDef055 run i)
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a67da1427a25e222d9393e4671544366a435b5467b20170e98f7ca088968035e`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} → LocalDef034 plan model → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  LocalDef009
    (LocalDef020 plan.axis (instHAdd.hAdd i.val 1) (run.computedState i.succ))
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `34e16979d88f342f79a1e32d13ffce39b5eefa5cc935f4bdf81abe3a748c8518`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (stageCount : Nat) →
      instLTNat.lt 0 stageCount →
        (stage : Fin stageCount → LocalDef051 n) →
          Eq (Finset.univ.prod fun i => (stage i).radix) n →
            (∀ (i : Fin stageCount),
                Eq (stage i).useTwiddle (Decidable.decide (instLTNat.lt (instHAdd.hAdd i.val 1) stageCount))) →
              (finalPermutation : Equiv (ZMod n) (ZMod n)) →
                LocalDef058 →
                  (∀ (x : ZMod n → Complex),
                      Eq (LocalDef067 finalPermutation (LocalDef062 stage x))
                        (LocalDef065 x)) →
                    (∀ (i : Fin stageCount) (x : ZMod n → Complex),
                        Eq (LocalDef063 (LocalDef066 (stage i) x))
                          (instHMul.hMul (stage i).radix.cast.sqrt (LocalDef063 x))) →
                      Function.Surjective LocalDef065 →
                        (∀ (x : ZMod n → Complex),
                            Eq (LocalDef064 (LocalDef065 x))
                              (instHMul.hMul n.cast.sqrt (LocalDef064 x))) →
                          LocalDef029 n
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `7db4d24a4acc7ed2a675a4b7ac6333f725f46008050b8ecb78e389911139f171`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e094f0859a1c82456fe5b679b9118e3d903f96148581f63caf87c12add36db72`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        (input : LocalDef017 plan.axis) →
          (computedState : Fin (instHAdd.hAdd m 1) → LocalDef017 plan.axis) →
            (∀ (index : LocalDef033 plan.axis), Eq (model.flInput (input index)) (input index)) →
              Eq (computedState (Fin.last m)) input →
                (∀ (i : Fin m),
                    Eq (computedState i.castSucc)
                      (LocalDef068 plan.axis i model (computedState i.succ))) →
                  LocalDef034 plan model
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `fbf9703bb59c24f543db5a49c4099b6bc0829fd4dc51d251836ecd542f4e9c43`

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
                      LocalDef037
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `a49a053354e6010807fe6ee370374aca279d3828d50cd5f5908d72c6f4ed06a3`

Type:

```lean
(instHAdd.hAdd 4 1).AtLeastTwo
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `9e9e6e9c6255b7f6f4d482b4b5daf2d90579b5786356f5d6d81322fd38e56422`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : LocalDef002 m} →
      {model : LocalDef037} →
        LocalDef034 plan model → Fin m → LocalDef017 plan.axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  LocalDef026 (run.computedState i.castSucc)
    (LocalDef056 plan.axis i (run.computedState i.succ))
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7ba3c0d95e5c24277ec95ceb2d7eeb781484864eed4c154d5a12b2f1fa8b7e25`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef014) → Fin m → LocalDef017 axis → LocalDef017 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x index =>
  Finset.univ.sum fun j =>
    instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j (index i))) (x (Function.update index i j))
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `ab841cfc9afa94a9c33b1bfd5aea2a395b3d437752e6903c3c10f5411ef6a8ec`

Type:

```lean
∀ {m : Nat} (axis : Fin m → LocalDef014) (a : Fin m), NeZero (axis a).order
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `00d481946537c4fea333af6b2e5b65d071fbe7e907bbbee20d147b733b0b9f50`

Type:

```lean
Type
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `9132ee0d9cb2aa39e88d4af0cc60ba538983d2e5aefa2c4715bd5f834ce48b55`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (radix : Nat) →
      instLENat.le 2 radix →
        Ne radix 0 →
          (blockCount : Nat) →
            Ne blockCount 0 →
              Eq (instHMul.hMul blockCount radix) n →
                Equiv (Prod (Fin blockCount) (ZMod radix)) (ZMod n) →
                  Equiv (ZMod n) (ZMod n) → Bool → (ZMod n → ZMod n) → LocalDef051 n
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1c5c0019e9f1cde8c7ac36370ddc8cdebbeef1a81a642ea476ab75b2cfd3855c`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → Bool
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.9
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `9a5ebbb64249a44b7a954dbf328f49cd90bbb1f589b9891fda13f6d5dc8bbda5`

Type:

```lean
LocalDef037 → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `765c400b21cdd5ebd4eda63b0bf2cd66d4559673516080c4beec6ca1884ea150`

Type:

```lean
{m n : Nat} → [inst : NeZero n] → (Fin m → LocalDef051 n) → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {m n} [NeZero n] stages x =>
  List.foldl (fun state stage => LocalDef066 stage state) x (List.ofFn stages)
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1b98349bc6407b2f00f761222365b650c3157ff135156ae9582fc23f948737bb`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => (LocalDef071 x).sqrt
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ab12e4415ded7a43ca3c2aba733bb60da55eca72620cd80c899857c0786bafd2`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => instHDiv.hDiv (LocalDef063 x) n.cast.sqrt
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `88d78104400162e8766a0713158d8cf258316a0f69c768050657e6632bddd684`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x k =>
  Finset.univ.sum fun j => instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j k)) (x j)
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `451e74e88f204ff5856b21932954b13f649b07b4827c68d7994a1ad116c87c27`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x => LocalDef073 stage (LocalDef072 stage x)
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `96b069ab581638e91c1d2748efd443ee2a1f60418baa3c54d1b78e70f25550f7`

Type:

```lean
{n : Nat} → Equiv (ZMod n) (ZMod n) → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} permutation x i => x (EquivLike.toFunLike.coe permutation i)
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `8d3e965aacbd8bb2f53ab4a12873c4523b9afb736ab1786c98a1cf30ba8d4a7e`

Type:

```lean
{m : Nat} →
  (axis : Fin m → LocalDef014) →
    Fin m → LocalDef037 → LocalDef017 axis → LocalDef017 axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i model x index =>
  LocalDef074 (axis i).plan model (fun j => x (Function.update index i j)) (index i)
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `10e785826afb9f3b9b06f0132254cc389950ae6ad8ab4d338c258968f45e6420`

Type:

```lean
LocalDef058
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `ba5af2995f3bde82b73a181429dc05616b98163594ca8b5f61325d8b159e86ff`

Type:

```lean
LocalDef058
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `d588903d42ed5e62a89abc9383bb26b4dda08d79d6524663ff72c7d012ba072f`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => Finset.univ.sum fun i => instHPow.hPow (Complex.instNorm.norm (x i)) 2
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ff5733b14f40eec996881be82ff09fea976cd958c7cb474a0cea8c8c6b1a8931`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x =>
  have permuted := fun i => x (EquivLike.toFunLike.coe stage.permutation i);
  fun i =>
  have bi := EquivLike.toFunLike.coe stage.reindex.symm i;
  Finset.univ.sum fun j =>
    instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j bi.snd))
      (permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := j }))
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `74e893bbbec094924bb26744b622fd11831b889d775381fddb4055302329d855`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x i =>
  ite (Eq stage.useTwiddle Bool.true)
    (instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (stage.twiddleExponent i)) (x i)) (x i)
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9b7d3ed0d2368b6ce3d657f70e4e8152625997f2f49617ef723841f6e22bc970`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    LocalDef029 n → LocalDef037 → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] plan model x =>
  LocalDef067 plan.finalPermutation (LocalDef080 model plan.stage x)
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `d1331890684f080fcbb319c8fe62402503a57488940282cabe28c1c237f81342`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef029 n → Equiv (ZMod n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.6
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `545e215ef4fcce115250d537eaa2cb06c5cb57dc5bd5b39d6f1cbe9a48630828`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.4
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `965e6f08ad6f204c13157a8fe9e1a155901194e09609769a0f659421aa651e78`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → Equiv (ZMod n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.8
```

### D078: `LocalDef078`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `dec33918992898801b2323263f5c4a02b324c3fcb105fec185c31497783e37bf`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : LocalDef051 n) → Equiv (Prod (Fin self.blockCount) (ZMod self.radix)) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.7
```

### D079: `LocalDef079`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `caf272fc6b71ebb3ae0eeb0ce6ab014ea8e189e658f1ebee865503f36400857f`

Type:

```lean
{n : Nat} → [inst : NeZero n] → LocalDef051 n → ZMod n → ZMod n
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.10
```

### D080: `LocalDef080`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `61063d112f3c995286b019086986dcf63210bf1f5744acb8a92227c26e9fc09e`

Type:

```lean
{r n : Nat} →
  [inst : NeZero n] →
    LocalDef037 → (Fin r → LocalDef051 n) → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {r n} [NeZero n] model stages x =>
  List.foldl (fun state stage => LocalDef082 model stage state) x (List.ofFn stages)
```

### D081: `LocalDef081`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `7`
- Semantic SHA-256: `66982eaeb447cbce750fce4807c54ab59c13e01413ca8d08d2bf34da2ff6771f`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : LocalDef051 n), NeZero stage.radix
```

### D082: `LocalDef082`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `b4de5bf2de2ad2cbb3d8cfee33f114fd36d13ea12e460ba2195b402663249c1d`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    LocalDef037 → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x =>
  LocalDef084 model stage (LocalDef083 model stage x)
```

### D083: `LocalDef083`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `3ec7290166ef53afdd08348156e26cd0cc09e178e2d1d2e5f6867d2e4285f21a`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    LocalDef037 → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x =>
  have permuted := fun i => x (EquivLike.toFunLike.coe stage.permutation i);
  fun i =>
  have bi := EquivLike.toFunLike.coe stage.reindex.symm i;
  if h2 : Eq stage.radix 2 then
    LocalDef090 model
      (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := Eq.rec j ⋯ }))
      (Eq.rec bi.snd h2)
  else
    if h4 : Eq stage.radix 4 then
      LocalDef089 model
        (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := Eq.rec j ⋯ }))
        (Eq.rec bi.snd h4)
    else
      LocalDef086 model
        (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := j })) bi.snd
```

### D084: `LocalDef084`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `f82a1d5f9b23ae14e1beac36ee4b2eaedc7c5a5f46f4499a193d3b2f29b7ae73`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    LocalDef037 → LocalDef051 n → (ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x i =>
  ite (Eq stage.useTwiddle Bool.true)
    (LocalDef085 model (LocalDef091 model (stage.twiddleExponent i)) (x i)) (x i)
```

### D085: `LocalDef085`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `b93b10e70e4ca5713e6cc3f020f91d9daf574ecac767dd4fa20903c58c2fab0e`

Type:

```lean
LocalDef037 → Complex → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x y =>
  { re := model.flAdd (model.flMul x.re y.re) (Real.instNeg.neg (model.flMul x.im y.im)),
    im := model.flAdd (model.flMul x.re y.im) (model.flMul x.im y.re) }
```

### D086: `LocalDef086`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `84ebda7f0ff318133fd19d36acaa11b1992ef0584beeb0859f5e9a6771660e61`

Type:

```lean
{q : Nat} → [NeZero q] → LocalDef037 → (ZMod q → Complex) → ZMod q → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model x k =>
  LocalDef100 model fun j =>
    LocalDef085 model (LocalDef091 model (instHMul.hMul j k)) (x j)
```

### D087: `LocalDef087`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `10`
- Semantic SHA-256: `31b52ab0de107cfaac2abe09ac02426698622fa18c17b5517159dd8facd3a9cb`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : LocalDef051 n), Eq stage.radix 2 → Eq 2 stage.radix
```

### D088: `LocalDef088`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `10`
- Semantic SHA-256: `36c04751e7e69199fa2d88d60e3db54faf40e54416a6e4d0c808948aabd60c5b`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : LocalDef051 n), Eq stage.radix 4 → Eq 4 stage.radix
```

### D089: `LocalDef089`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `ba3f006d9032e7045e3bc4fd3080eaccb8160ccdc53642cc2770492ab10872de`

Type:

```lean
LocalDef037 → (ZMod 4 → Complex) → ZMod 4 → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x k =>
  have index := (ZMod.finEquiv 4).toEquiv;
  have term := fun i =>
    LocalDef096 (instHMul.hMul (EquivLike.toFunLike.coe index i) k)
      (x (EquivLike.toFunLike.coe index i));
  LocalDef099 model (LocalDef099 model (term 0) (term 1))
    (LocalDef099 model (term 2) (term 3))
```

### D090: `LocalDef090`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `763c4175157ca5bad026dfd600033c4c8ba290fc556e8d90fb929e74f74791ba`

Type:

```lean
LocalDef037 → (ZMod 2 → Complex) → ZMod 2 → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x k =>
  LocalDef100 model fun j => LocalDef097 (instHMul.hMul j k) (x j)
```

### D091: `LocalDef091`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `a6af37b386d000aa189d9da9937fcefac49c0085ff5de774b92de2619e0fdc9b`

Type:

```lean
{q : Nat} → [NeZero q] → LocalDef037 → ZMod q → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model j =>
  { re := model.flCos (LocalDef098 j), im := model.flSin (LocalDef098 j) }
```

### D092: `LocalDef092`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `b938991e119b06301e2cd03fff62ec1cddff900aeeb08cb43310f9ffc480d8b0`

Type:

```lean
LocalDef037 → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D093: `LocalDef093`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `72a3a0864d70744a999e06284a98176fab2e9c7b8debf6ec88e44bd0b8ba6de4`

Type:

```lean
LocalDef037 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D094: `LocalDef094`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `6d21356ec66cacf098051fc05ca9919a059a4a65a900eb3cc227bd26bee62a47`

Type:

```lean
LocalDef037 → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D095: `LocalDef095`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `38f27b8dcb3484eed14d8e2a32e4c6fa407c3ac190eef9ac592163ef83fe7312`

Type:

```lean
LocalDef037 → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.7
```

### D096: `LocalDef096`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `d7c3aaaa2d06ac8c4c1c139aee3d77d883674575ca9ce14ee4b18016db1fad79`

Type:

```lean
ZMod 4 → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun j x =>
  ite (Eq j 0) x
    (ite (Eq j 1) { re := Real.instNeg.neg x.im, im := x.re }
      (ite (Eq j 2) (Complex.instNeg.neg x) { re := x.im, im := Real.instNeg.neg x.re }))
```

### D097: `LocalDef097`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `428bc8f94723929b45fdb2bb504716bd8365b7563e491259d882896e7f032f20`

Type:

```lean
ZMod 2 → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun j x => ite (Eq j 0) x (Complex.instNeg.neg x)
```

### D098: `LocalDef098`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `46ff9a18b6c4b2cc32d5c954f428895ca4ab25a82e357b33d2062db8082f9ec5`

Type:

```lean
{q : Nat} → [NeZero q] → ZMod q → Real
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] j => instHDiv.hDiv (instHMul.hMul (instHMul.hMul 2 Real.pi) j.val.cast) q.cast
```

### D099: `LocalDef099`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `afb354edb26d952dae0834da42cca39b5ba8e7594489e99bffa1c580295f95a4`

Type:

```lean
LocalDef037 → Complex → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x y => { re := model.flAdd x.re y.re, im := model.flAdd x.im y.im }
```

### D100: `LocalDef100`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `947d8b493b9f83d1fee0edeb79367bf95e524991a119df339ba0ad45a661d4d3`

Type:

```lean
{q : Nat} → [NeZero q] → LocalDef037 → (ZMod q → Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model term =>
  have index := (ZMod.finEquiv q).toEquiv;
  { re := LocalDef103 model.flAdd q fun i => (term (EquivLike.toFunLike.coe index i)).re,
    im := LocalDef103 model.flAdd q fun i => (term (EquivLike.toFunLike.coe index i)).im }
```

### D101: `LocalDef101`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `11`
- Semantic SHA-256: `ed734b22ed9854026574c400f6f18f3f6f2ecba4c424c5f37b31a9c3161af165`

Type:

```lean
NeZero (instHAdd.hAdd 3 1)
```

### D102: `LocalDef102`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `11`
- Semantic SHA-256: `fc07827897ea6ceaa43dcb4499d7aa2aacd83067423edb8ca73b7bb2f57ee423`

Type:

```lean
NeZero (instHAdd.hAdd 1 1)
```

### D103: `LocalDef103`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `3a24e7a5c707c014d59b9d90d536db1f1c79ef135d2ba34adb6af8a4258efe41`

Type:

```lean
(Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun flAdd x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Real) x
    (fun x f x_2 =>
      LocalDef105 (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Real) x → Real) x
        x_2 (fun x x_3 => 0)
        (fun n v x => if h : Eq n 0 then v ⟨0, ⋯⟩ else flAdd (x.1 fun i => v i.castSucc) (v (Fin.last n))) f)
    x_1
```

### D104: `LocalDef104`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `13`
- Semantic SHA-256: `7f01e5fdb761df0e050b0929b93312fc9084bc345726c816952ed0fd4844be27`

Type:

```lean
∀ (n : Nat), Eq n 0 → instLTNat.lt 0 (instHAdd.hAdd n 1)
```

### D105: `LocalDef105`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `13`
- Semantic SHA-256: `56d4f4744c0103a83d3305dc49473baf5a72c1037bbec52ff87f6f4a5419f79e`

Type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      ((x : Fin 0 → Real) → motive 0 x) →
        ((n : Nat) → (v : Fin (instHAdd.hAdd n 1) → Real) → motive n.succ v) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D106: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D107: `DivInvMonoid.toDiv`

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

### D108: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D109: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D110: `Fin.fintype`

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

### D111: `Finset.sum`

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

### D112: `Finset.univ`

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

### D113: `HAdd.hAdd`

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

### D114: `HDiv.hDiv`

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

### D115: `HMul.hMul`

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

### D116: `HPow.hPow`

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

### D117: `LE.le`

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

### D118: `LT.lt`

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

### D119: `Monoid.toNatPow`

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

### D120: `MulZeroClass.toZero`

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

### D121: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D122: `Nat.instMulZeroClass`

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

### D123: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

### D124: `OfNat.ofNat`

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

### D125: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D126: `Real.instAdd`

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

### D127: `Real.instAddCommMonoid`

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

### D128: `Real.instDivInvMonoid`

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

### D129: `Real.instLE`

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

### D130: `Real.instLT`

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

### D131: `Real.instMonoid`

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

### D132: `Real.instMul`

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

### D133: `Real.instZero`

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

### D134: `Subtype.val`

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

### D135: `Zero.toOfNat0`

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

### D136: `instHAdd`

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

### D137: `instHDiv`

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

### D138: `instHMul`

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

### D139: `instHPow`

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

### D140: `instOfNatNat`

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

### D141: `Nat.cast`

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

### D142: `Real.instNatCast`

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

### D143: `Real.sqrt`

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

### D144: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

### D145: `AddCommMonoidWithOne.toAddMonoidWithOne`

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

### D146: `AddMonoidWithOne.toNatCast`

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

### D147: `Complex`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `06f5db8f409d6076be5ab5a3405277f735e30c46762deb074e76e94ef07eb934`

Type:

```lean
Type
```

### D148: `Complex.instNorm`

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

### D149: `Complex.instSub`

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

### D150: `ENNReal`

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

### D151: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D152: `Fin.instOfNat`

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

### D153: `Finset.prod`

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

### D154: `HSub.hSub`

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

### D155: `Nat.below`

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

### D156: `Nat.brecOn`

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

### D157: `Nat.instCommMonoid`

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

### D158: `Nat.ne_of_gt`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `efc85b6e2ba577017c57d5b88a2d6f39eaa33310359c247b44f3ff338427ac62`

Type:

```lean
∀ {a b : Nat}, instLTNat.lt b a → Ne a b
```

### D159: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D160: `NeZero.mk`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e2e32989d835a09f096b510efd93c48c325d5131f0dc0608e4b63d8e6448d9ad`

Type:

```lean
∀ {R : Type u_1} [inst : Zero R] {n : R}, Ne n 0 → NeZero n
```

### D161: `Norm.norm`

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

### D162: `One.toOfNat1`

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

### D163: `PiLp.instNorm`

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

### D164: `Real.instOne`

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

### D165: `Real.instSub`

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

### D166: `WithLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `beeca7e7d011bf353b991ee4fb3bf57a00fca40fd553001d24ad8181bda346e3`

Type:

```lean
ENNReal → Type u_1 → Type u_1
```

### D167: `WithLp.toLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `293799c52cddc04402243afb567ab5aa26e35f2b7064cbec3d87dc7fba0ba006`

Type:

```lean
(p : ENNReal) → {V : Type u_1} → V → WithLp p V
```

### D168: `instAddCommMonoidWithOneENNReal`

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

### D169: `instAddNat`

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

### D170: `instHSub`

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

### D171: `instLENat`

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

### D172: `instOfNatAtLeastTwo`

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

### D173: `Fin.castLE`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `741eedcc1330cedb8ff0a69095d6df1438c40a8c734f1526dc385e45bb9ae135`

Type:

```lean
{n m : Nat} → instLENat.le n m → Fin n → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} h i => ⟨i.val, ⋯⟩
```

### D174: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D175: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D176: `Fin.val`

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

### D177: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

### D178: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D179: `Nat.casesOn`

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

### D180: `Nat.decLt`

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

### D181: `Not`

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

### D182: `Pi.instFintype`

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

### D183: `ZMod`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `16bf0604575e2049c78de15301315a487d981f9b4918a56c63dc9410569ff212`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun x => ZMod.match_1 (fun x => Type) x (fun _ => Int) fun n => Fin (instHAdd.hAdd n 1)
```

### D184: `ZMod.fintype`

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

### D185: `Zero.ofOfNat0`

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

### D186: `dite`

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

### D187: `inferInstance`

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

### D188: `instDecidableEqFin`

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

### D189: `instDecidableEqNat`

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

### D190: `instLTNat`

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

### D191: `ite`

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

### D192: `AddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `4f50638d97f5d425f8c05152b76b46854b453bc1d6f50f0e215f12ac557f8270`

Type:

```lean
(A : Type u_1) → [AddMonoid A] → (M : Type u_2) → [Monoid M] → Type (max u_1 u_2)
```

### D193: `AddChar.instFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `83e85a9db1d0e5ecf4333397f4d7bc036d1237ee1458184cbc4f34ac900b688e`

Type:

```lean
{A : Type u_1} → {M : Type u_3} → [inst : AddMonoid A] → [inst_1 : Monoid M] → FunLike (AddChar A M) A M
```

Definition body (one-level semantic boundary):

```lean
fun {A} {M} [AddMonoid A] [Monoid M] => { coe := AddChar.toFun, coe_injective' := ⋯ }
```

### D194: `AddGroupWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Int.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ab901b5dbbaa698c61da5b353ee51145e713b8971414a6fdb991cde02b5cb677`

Type:

```lean
{R : Type u} → [self : AddGroupWithOne R] → AddMonoidWithOne R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddGroupWithOne R] => self.2
```

### D195: `AddMonoidWithOne.toAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `4fa12ffa6a6fee7c2d3050177e382f5c7883895f706698d037c6b045bef31105`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → AddMonoid R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.2
```

### D196: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D197: `CommRing.toNonUnitalCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D198: `CommRing.toRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c018410d7cd7a0cf748bc89452a2d03cd223cfa1f0ad262b865497873fcc8648`

Type:

```lean
{α : Type u} → [self : CommRing α] → Ring α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : CommRing α] => self.1
```

### D199: `Complex.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D200: `Complex.instNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Norm`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D201: `Complex.instNormedField`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D202: `Complex.instSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `008d132dd980a88182937c2214239a242f0e05220ab73a658ec569ddc4ad3f3e`

Type:

```lean
Semiring Complex
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D203: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D204: `Decidable.decide`

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

### D205: `Distrib.toMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1d05ddf657021fb5615c5054f46b4863aec4ca856ca48fbb75add25e1f0fe06f`

Type:

```lean
{R : Type u_1} → [self : Distrib R] → Mul R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : Distrib R] => self.1
```

### D206: `ENormedAddCommMonoid.toESeminormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7d58c19063063d627291b91068fa4bf2bf5ff88679897376ac465b9f52e93642`

Type:

```lean
{E : Type u_8} → {inst : TopologicalSpace E} → [self : ENormedAddCommMonoid E] → ESeminormedAddCommMonoid E
```

Definition body (one-level semantic boundary):

```lean
fun E {inst} [self : ENormedAddCommMonoid E] => self.1
```

### D207: `ESeminormedAddCommMonoid.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `38db724db757c42f8e8affdaa0b60310db98b78e8ba320c452775788f7191220`

Type:

```lean
{E : Type u_8} → [inst : TopologicalSpace E] → [self : ESeminormedAddCommMonoid E] → AddCommMonoid E
```

Definition body (one-level semantic boundary):

```lean
fun E [TopologicalSpace E] self => { toAddMonoid := self.toAddMonoid, add_comm := ⋯ }
```

### D208: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

### D209: `Fin.castSucc`

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

### D210: `Fin.last`

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

### D211: `Function.Surjective`

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

### D212: `Function.update`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `092e6c4864b94365603f748d7cf0dd798223b04b127d4c37969b0c09cac29193`

Type:

```lean
{α : Sort u} → {β : α → Sort v} → [DecidableEq α] → ((a : α) → β a) → (a' : α) → β a' → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] f a' v a => if h : Eq a a' then Eq.ndrec v ⋯ else f a
```

### D213: `MonoidWithZero.toMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c0f91ccdc0415c148969849b7a83ce67d87cf4c402704186fa19f6313928d90f`

Type:

```lean
{M₀ : Type u} → [self : MonoidWithZero M₀] → Monoid M₀
```

Definition body (one-level semantic boundary):

```lean
fun M₀ [self : MonoidWithZero M₀] => self.1
```

### D214: `NonUnitalCommRing.toNonUnitalNonAssocCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `3bd70454a5180abed6221bb3f73922ebc30c10136298d23eb30d358cdd2fdb82`

Type:

```lean
{α : Type u} → [self : NonUnitalCommRing α] → NonUnitalNonAssocCommRing α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalNonAssocRing := self.toNonUnitalNonAssocRing, mul_comm := ⋯ }
```

### D215: `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1082112ee2b1424cb7e1eff69df85640d23793811157d8a4401f364710bc21d2`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing α] → NonUnitalNonAssocRing α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocCommRing α] => self.1
```

### D216: `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D217: `NonUnitalNonAssocSemiring.toDistrib`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `5b49ec28e539eea6192ab07a9aee6da537ed1b5e017f2b9ef44d3a0ae51d79c6`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → Distrib α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toMul := self.toMul, toAdd := self.toAdd, left_distrib := ⋯, right_distrib := ⋯ }
```

### D218: `NormedAddCommGroup.toENormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Continuity`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D219: `NormedCommRing.toSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D220: `NormedField.toNormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Field.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D221: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D222: `Real.cos`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1377d30c9decd42f763baf8cb45f365ee121aec3ccf9f371c298d2926eba5a53`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => (Complex.cos (Complex.ofReal x)).re
```

### D223: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D224: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D225: `Real.sin`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7937a67d5952a981d1a70df574b1d79c6e87542f5d15a2b0fe35a8fe8d31811f`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => (Complex.sin (Complex.ofReal x)).re
```

### D226: `Ring.toAddGroupWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D227: `SeminormedCommRing.toSeminormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e3cbc92d1d5e37d9eaeb1d595c83a78f7af7e3a8d249a700fa3676ab4e0c3d60`

Type:

```lean
{α : Type u_5} → [self : SeminormedCommRing α] → SeminormedRing α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedCommRing α] => self.1
```

### D228: `SeminormedRing.toPseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e6ea9296e8643d5ae7cf334c065c9d6ebe4a95de22d3b0708a585db80e17322a`

Type:

```lean
{α : Type u_5} → [self : SeminormedRing α] → PseudoMetricSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedRing α] => self.3
```

### D229: `Semiring.toMonoidWithZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D230: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D231: `ZMod.commRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D232: `ZMod.stdAddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d8823a1e47eaa4d04423dedbc65db89ecb2a2b5484d0ac20a437a96d1f98677a`

Type:

```lean
{N : Nat} → [NeZero N] → AddChar (ZMod N) Complex
```

Definition body (one-level semantic boundary):

```lean
fun {N} [NeZero N] => Circle.coeHom.compAddChar ZMod.toCircle
```

### D233: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D234: `Equiv.instEquivLike`

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

### D235: `EquivLike.toFunLike`

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

### D236: `List.foldl`

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

### D237: `List.ofFn`

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

### D238: `Ne`

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

### D239: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D240: `instMulNat`

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

### D241: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

### D242: `Equiv.symm`

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

### D243: `Prod.fst`

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

### D244: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

### D245: `Prod.snd`

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

### D246: `instDecidableEqBool`

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

### D247: `Eq.rec`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `recursor`
- Distance from target type: `10`
- Semantic SHA-256: `26d7c884de9aaebaff7a572e5e22744a04d3a3d7e18e61503180424e03b7c5b9`

Type:

```lean
{α : Sort u_1} →
  {a : α} → {motive : (a_1 : α) → Eq a a_1 → Sort u} → motive a ⋯ → {a_1 : α} → (t : Eq a a_1) → motive a_1 t
```

### D248: `Complex.im`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `276278e52acc5a079152e9d98e5089746dc087e625b4583f0c8a78b06f4e42ef`

Type:

```lean
Complex → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D249: `Complex.mk`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `constructor`
- Distance from target type: `11`
- Semantic SHA-256: `eb086afc5605d698a41cc0dbd78c60aa93ea5b91b09555f0a3d4205e5c8c3d6d`

Type:

```lean
Real → Real → Complex
```

### D250: `Complex.re`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `d61ccb0f1eee778d5406d36759b34354009fc6e8d298adef3d9bfd8c57f16c75`

Type:

```lean
Complex → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D251: `Distrib.toAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `cf0362fc4cebf4743d0430077ad4081a1de510a75cfe1b4e6adc97f21271a3ba`

Type:

```lean
{R : Type u_1} → [self : Distrib R] → Add R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : Distrib R] => self.2
```

### D252: `Fin.instAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `b3ee547a63794f701578ce9e2965118436a96f41dd67c398ae9c530ccaf94956`

Type:

```lean
{n : Nat} → Add (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { add := Fin.add }
```

### D253: `Fin.instMul`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `b2c82cb3bad8033084de1152c3311705f097fea4b09de861cfbc259aa58cae3d`

Type:

```lean
{n : Nat} → Mul (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { mul := Fin.mul }
```

### D254: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D255: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D256: `RingEquiv.toEquiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Equiv`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `ad2bbda4cee02ba76b521c1b90d73ae4e3d2edfd8e0e1471d3d872a8a791afb2`

Type:

```lean
{R : Type u_7} →
  {S : Type u_8} → [inst : Mul R] → [inst_1 : Mul S] → [inst_2 : Add R] → [inst_3 : Add S] → RingEquiv R S → Equiv R S
```

Definition body (one-level semantic boundary):

```lean
fun R S [Mul R] [Mul S] [Add R] [Add S] self => self.1
```

### D257: `ZMod.finEquiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `c7185762b5ca67875cfbfd2fcf9c9669ff6295dab781a48d1dfda8dee8181f04`

Type:

```lean
(n : Nat) → [NeZero n] → RingEquiv (Fin n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  ZMod.finEquiv.match_1 (fun x x_2 => RingEquiv (Fin x) (ZMod x)) x x_1 (fun h => ⋯.elim) fun n x =>
    RingEquiv.refl (Fin (instHAdd.hAdd n 1))
```

### D258: `AddMonoidWithOne.toOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `12`
- Semantic SHA-256: `2ee638fd7292dbcf1e4adb85b14bbd0f304e8a260316e61621bf8eac03f03f6d`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → One R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.3
```

### D259: `Complex.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `5a2f4911bfc517e9691dcac1bf08b20c460e4df0b018a1f5ba049adbb5de99ae`

Type:

```lean
Neg Complex
```

Definition body (one-level semantic boundary):

```lean
{ neg := fun z => { re := Real.instNeg.neg z.re, im := Real.instNeg.neg z.im } }
```

### D260: `NonUnitalNonAssocSemiring.toMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `12`
- Semantic SHA-256: `87ddc8012963f013675a2d3b6dbd069bd2e6eeeafa9e7aff6d92bfbf7d848152`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → MulZeroClass α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toMul := self.toMul, toZero := self.toZero, zero_mul := ⋯, mul_zero := ⋯ }
```

### D261: `Real.pi`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `d75a7e5ab21b9e0fa41907d3afec6d87f8f264e448c96b4fd69b77195bdbebac`

Type:

```lean
Real
```

Definition body (one-level semantic boundary):

```lean
instHMul.hMul 2 (Classical.choose Real.exists_cos_eq_zero)
```

### D262: `ZMod.decidableEq`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `7fd304bbb6ed0755497ea3fc939287cfddd9667bc3c6f5612bca13081a5103ba`

Type:

```lean
(n : Nat) → DecidableEq (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun x =>
  ZMod.match_1 (fun x => DecidableEq (ZMod x)) x (fun _ => inferInstanceAs (DecidableEq Int)) fun n =>
    inferInstanceAs (DecidableEq (Fin (instHAdd.hAdd n 1)))
```

### D263: `ZMod.val`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `09f4356e066f5ae3957dc3f413b65273a0bf2b1f5828e9b1cfc9e08f21266213`

Type:

```lean
{n : Nat} → ZMod n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun x => ZMod.val.match_1 (fun x => ZMod x → Nat) x (fun _ => Int.natAbs) fun n => Fin.val
```

### D264: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `14`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```
