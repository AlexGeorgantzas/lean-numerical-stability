# Declaration dossier for P18-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p18_t3_method4s3pc_global_error_regimes
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    {ι : Type*} (method : P18Method4s3pCSourceModel)
    (smooth : P18StableMethod4s3pCBranch State ι method 4)
    (nonsmooth : P18StableMethod4s3pCBranch State ι method 3)
    (hsmooth : smooth.tauRegime = P18TauRegime.wellBehaved)
    (hnonsmooth :
      nonsmooth.tauRegime = P18TauRegime.notWellBehaved) :
    method.tableau.bPerturbation = (fun _ ↦ 0) ∧
      p18ThirdOrderConsistency method.tableau ∧
      p18SmoothPerturbationOrderThree method.tableau ∧
      p18UniformTwoTermGlobalOrder smooth.globalError
        smooth.globalSchemeError smooth.globalPerturbationError
        smooth.step smooth.epsilon 3 3 ∧
      p18UniformTwoTermGlobalOrder nonsmooth.globalError
        nonsmooth.globalSchemeError nonsmooth.globalPerturbationError
        nonsmooth.step nonsmooth.epsilon 3 2
```

## Elaborated target type

```lean
∀ {State : Type u_1} [inst : NormedAddCommGroup State] [inst_1 : NormedSpace Real State] {ι : Type u_2}
  (method : HighamBench.P18Method4s3pCSourceModel) (smooth : HighamBench.P18StableMethod4s3pCBranch State ι method 4)
  (nonsmooth : HighamBench.P18StableMethod4s3pCBranch State ι method 3),
  Eq smooth.tauRegime HighamBench.P18TauRegime.wellBehaved →
    Eq nonsmooth.tauRegime HighamBench.P18TauRegime.notWellBehaved →
      And (Eq method.tableau.bPerturbation fun x => 0)
        (And (HighamBench.p18ThirdOrderConsistency method.tableau)
          (And (HighamBench.p18SmoothPerturbationOrderThree method.tableau)
            (And
              (HighamBench.p18UniformTwoTermGlobalOrder smooth.globalError smooth.globalSchemeError
                smooth.globalPerturbationError smooth.step smooth.epsilon 3 3)
              (HighamBench.p18UniformTwoTermGlobalOrder nonsmooth.globalError nonsmooth.globalSchemeError
                nonsmooth.globalPerturbationError nonsmooth.step nonsmooth.epsilon 3 2))))
```

## Fully explicit elaborated target type

```lean
∀ {State : Type u_1} [inst : NormedAddCommGroup.{u_1} State]
  [inst_1 :
    @NormedSpace.{0, u_1} Real State Real.normedField (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)]
  {ι : Type u_2} (method : HighamBench.P18Method4s3pCSourceModel)
  (smooth :
    @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (nonsmooth :
    @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hsmooth :
    @Eq.{1} HighamBench.P18TauRegime
      (@HighamBench.P18StableMethod4s3pCBranch.tauRegime.{u_1, u_2} State inst inst_1 ι method
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
      HighamBench.P18TauRegime.wellBehaved)
  (hnonsmooth :
    @Eq.{1} HighamBench.P18TauRegime
      (@HighamBench.P18StableMethod4s3pCBranch.tauRegime.{u_1, u_2} State inst inst_1 ι method
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
      HighamBench.P18TauRegime.notWellBehaved),
  And
    (@Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (@HighamBench.P18AdditiveRKTableau.bPerturbation (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (HighamBench.P18Method4s3pCSourceModel.tableau method))
      fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
      @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (And
      (@HighamBench.p18ThirdOrderConsistency (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (HighamBench.P18Method4s3pCSourceModel.tableau method))
      (And
        (@HighamBench.p18SmoothPerturbationOrderThree (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (HighamBench.P18Method4s3pCSourceModel.tableau method))
        (And
          (@HighamBench.p18UniformTwoTermGlobalOrder.{u_2} ι
            (@HighamBench.P18StableMethod4s3pCBranch.globalError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
            (@HighamBench.P18StableMethod4s3pCBranch.globalSchemeError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
            (@HighamBench.P18StableMethod4s3pCBranch.globalPerturbationError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
            (@HighamBench.P18StableMethod4s3pCBranch.step.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
            (@HighamBench.P18StableMethod4s3pCBranch.epsilon.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) smooth)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@HighamBench.p18UniformTwoTermGlobalOrder.{u_2} ι
            (@HighamBench.P18StableMethod4s3pCBranch.globalError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
            (@HighamBench.P18StableMethod4s3pCBranch.globalSchemeError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
            (@HighamBench.P18StableMethod4s3pCBranch.globalPerturbationError.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
            (@HighamBench.P18StableMethod4s3pCBranch.step.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
            (@HighamBench.P18StableMethod4s3pCBranch.epsilon.{u_1, u_2} State inst inst_1 ι method
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) nonsmooth)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P18Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P18Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P18AdditiveRKTableau.bPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a4b3003dd7215c8a0cd285151ca1b0c1db2de401de3efd09290c9b97e1fe8763`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (self : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun s self => self.4
```

### D002: `HighamBench.P18Method4s3pCSourceModel`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a6fb2fb6e65d499557115b25f84fde1305e8ded046187f9a66fe511dd42adcd1`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D003: `HighamBench.P18Method4s3pCSourceModel.tableau`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `479eb24cb883cb3e8b2a44a6d2a457fb56f19c7e03af0b8ca3c49bc7249944b1`

Type:

```lean
HighamBench.P18Method4s3pCSourceModel → HighamBench.P18AdditiveRKTableau 4
```

Fully explicit type:

```lean
(self : HighamBench.P18Method4s3pCSourceModel) →
  HighamBench.P18AdditiveRKTableau (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D004: `HighamBench.P18StableMethod4s3pCBranch`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9881bdcce05a6bec0c2d42910be6e8d56064723bc1b2be0eb37af75c0f41d26b`

Type:

```lean
(State : Type u_1) →
  [inst : NormedAddCommGroup State] →
    [NormedSpace Real State] → Type u_2 → HighamBench.P18Method4s3pCSourceModel → Nat → Type (max u_1 u_2)
```

Fully explicit type:

```lean
(State : Type u_1) →
  [inst : NormedAddCommGroup.{u_1} State] →
    [@NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      (ι : Type u_2) →
        (method : HighamBench.P18Method4s3pCSourceModel) → (localPerturbationPower : Nat) → Type (max u_1 u_2)
```

### D005: `HighamBench.P18StableMethod4s3pCBranch.epsilon`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `77335368a7b06c5f8afb8d927aacd49b62f92d9a09d0906901c6f0512a0c7e40`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              Real
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.3
```

### D006: `HighamBench.P18StableMethod4s3pCBranch.globalError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6b3374be604d1122a7c33dce773678d22c1d3b5af2147418187b724319bceca3`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → ι → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.42
```

### D007: `HighamBench.P18StableMethod4s3pCBranch.globalPerturbationError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c2c56ec256c037fc95646603fc27aa47c9cae611e62f1a1511d1c618a3ba59ee`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → ι → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.41
```

### D008: `HighamBench.P18StableMethod4s3pCBranch.globalSchemeError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d389b576943d2450b1e7d1303ff81197db814e16482d13afbd43595da1578200`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → ι → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.40
```

### D009: `HighamBench.P18StableMethod4s3pCBranch.step`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e59c1525660117fc3eb45d0e0338a20eacef61d6ba7627d69b15ce801e7f9878`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → ι → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.2
```

### D010: `HighamBench.P18StableMethod4s3pCBranch.tauRegime`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `719d8a6cd7c40d824226c706f218b85d8daa59b6e14a888d6497cad33e04688a`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18StableMethod4s3pCBranch State ι method localPerturbationPower → HighamBench.P18TauRegime
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (self :
                @HighamBench.P18StableMethod4s3pCBranch.{u_1, u_2} State inst inst_1 ι method localPerturbationPower) →
              HighamBench.P18TauRegime
```

Definition body (one-level semantic boundary):

```lean
fun State [NormedAddCommGroup State] [NormedSpace Real State] ι method localPerturbationPower self => self.1
```

### D011: `HighamBench.P18TauRegime`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b767c21406e3044231f5207172a34a9fbfb2a3741a8c94714c57cd114d7f4866`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D012: `HighamBench.P18TauRegime.notWellBehaved`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `1`
- Semantic SHA-256: `1a1d7bb7e96d74e34a79e3214b3956e68d53dcf79e554184000bd6db71928e9f`

Type:

```lean
HighamBench.P18TauRegime
```

Fully explicit type:

```lean
HighamBench.P18TauRegime
```

### D013: `HighamBench.P18TauRegime.wellBehaved`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `1`
- Semantic SHA-256: `e9ef4b0ed8703b256897b553882291d8a5d39585e0f05f9ba4ac902bcc360cd2`

Type:

```lean
HighamBench.P18TauRegime
```

Fully explicit type:

```lean
HighamBench.P18TauRegime
```

### D014: `HighamBench.p18SmoothPerturbationOrderThree`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `12fc6ac2c8eab760c27bef7eb98d65be71cc67d9edd121e4d4794a6040369463`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Prop
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau =>
  And (Eq (HighamBench.p18CoeffDot tableau.bPerturbation HighamBench.p18TableauE) 0)
    (And (Eq (HighamBench.p18CoeffDot tableau.bPerturbation (HighamBench.p18TableauCTilde tableau)) 0)
      (And
        (Eq
          (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau) (HighamBench.p18TableauCPerturbation tableau))
          0)
        (And (Eq (HighamBench.p18CoeffDot tableau.bPerturbation (HighamBench.p18TableauCPerturbation tableau)) 0)
          (And
            (Eq
              (HighamBench.p18CoeffDot tableau.bPerturbation
                (HighamBench.p18CoeffMatVec (HighamBench.p18TableauATilde tableau)
                  (HighamBench.p18TableauCTilde tableau)))
              0)
            (And
              (Eq
                (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
                  (HighamBench.p18CoeffMatVec tableau.APerturbation (HighamBench.p18TableauCTilde tableau)))
                0)
              (And
                (Eq
                  (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
                    (HighamBench.p18CoeffMatVec (HighamBench.p18TableauATilde tableau)
                      (HighamBench.p18TableauCPerturbation tableau)))
                  0)
                (And
                  (Eq
                    (HighamBench.p18CoeffDot tableau.bPerturbation
                      (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCTilde tableau)
                        (HighamBench.p18TableauCTilde tableau)))
                    0)
                  (And
                    (Eq
                      (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
                        (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCTilde tableau)
                          (HighamBench.p18TableauCPerturbation tableau)))
                      0)
                    (And
                      (Eq
                        (HighamBench.p18CoeffDot tableau.bPerturbation
                          (HighamBench.p18CoeffMatVec tableau.APerturbation (HighamBench.p18TableauCTilde tableau)))
                        0)
                      (And
                        (Eq
                          (HighamBench.p18CoeffDot tableau.bPerturbation
                            (HighamBench.p18CoeffMatVec (HighamBench.p18TableauATilde tableau)
                              (HighamBench.p18TableauCPerturbation tableau)))
                          0)
                        (And
                          (Eq
                            (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
                              (HighamBench.p18CoeffMatVec tableau.APerturbation
                                (HighamBench.p18TableauCPerturbation tableau)))
                            0)
                          (And
                            (Eq
                              (HighamBench.p18CoeffDot tableau.bPerturbation
                                (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCPerturbation tableau)
                                  (HighamBench.p18TableauCTilde tableau)))
                              0)
                            (And
                              (Eq
                                (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
                                  (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCPerturbation tableau)
                                    (HighamBench.p18TableauCPerturbation tableau)))
                                0)
                              (And
                                (Eq
                                  (HighamBench.p18CoeffDot tableau.bPerturbation
                                    (HighamBench.p18CoeffMatVec tableau.APerturbation
                                      (HighamBench.p18TableauCPerturbation tableau)))
                                  0)
                                (Eq
                                  (HighamBench.p18CoeffDot tableau.bPerturbation
                                    (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCPerturbation tableau)
                                      (HighamBench.p18TableauCPerturbation tableau)))
                                  0)))))))))))))))
```

### D015: `HighamBench.p18ThirdOrderConsistency`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `288fc8df50fd034593361abbf0fc0cb1a2fd88f7bd55a457cc7d2eff5db71d49`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Prop
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau =>
  And (Eq (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau) HighamBench.p18TableauE) 1)
    (And
      (Eq (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau) (HighamBench.p18TableauCTilde tableau))
        (1 / 2))
      (And
        (Eq
          (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
            (HighamBench.p18CoeffHadamard (HighamBench.p18TableauCTilde tableau)
              (HighamBench.p18TableauCTilde tableau)))
          (1 / 3))
        (Eq
          (HighamBench.p18CoeffDot (HighamBench.p18TableauBTilde tableau)
            (HighamBench.p18CoeffMatVec (HighamBench.p18TableauATilde tableau) (HighamBench.p18TableauCTilde tableau)))
          (1 / 6))))
```

### D016: `HighamBench.p18UniformTwoTermGlobalOrder`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `857b1fa0013d8b7c827b923215409f73134c4af272d8ce63a936c72263964b27`

Type:

```lean
{ι : Type u_1} → (ι → Real) → (ι → Real) → (ι → Real) → (ι → Real) → Real → Nat → Nat → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (error schemeError perturbationError step : ι → Real) → (epsilon : Real) → (p m : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} error schemeError perturbationError step epsilon p m =>
  And (∀ (t : ι), Eq (error t) (instHAdd.hAdd (schemeError t) (perturbationError t)))
    (Exists fun schemeConstant =>
      Exists fun perturbationConstant =>
        And (Real.instLE.le 0 schemeConstant)
          (And (Real.instLE.le 0 perturbationConstant)
            (∀ (t : ι),
              And (Real.instLE.le (abs (schemeError t)) (instHMul.hMul schemeConstant (instHPow.hPow (step t) p)))
                (Real.instLE.le (abs (perturbationError t))
                  (instHMul.hMul (instHMul.hMul perturbationConstant (abs epsilon)) (instHPow.hPow (step t) m))))))
```

### D017: `HighamBench.P18AdditiveRKTableau`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `4707776dcdcfe568ae7f5bbf7c1d612e65746b37c13c21cfe4a3d7ebfca46681`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(s : Nat) → Type
```

### D018: `HighamBench.P18AdditiveRKTableau.APerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `429ca72b523a839090da99ea321174af9d58b75e8d3278be921b1037d2d5567a`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (self : HighamBench.P18AdditiveRKTableau s) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun s self => self.2
```

### D019: `HighamBench.P18Method4s3pCSourceModel.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2b73edfc2c9c2edb49544a566236fb9b49bd9cad2df0e5b917330e56f3153bdd`

Type:

```lean
(tableau : HighamBench.P18AdditiveRKTableau 4) →
  (Eq tableau.bPerturbation fun x => 0) →
    HighamBench.p18ThirdOrderConsistency tableau →
      HighamBench.p18SmoothPerturbationOrderThree tableau → HighamBench.P18Method4s3pCSourceModel
```

Fully explicit type:

```lean
(tableau : HighamBench.P18AdditiveRKTableau (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
  (perturbation_weights_zero :
      @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@HighamBench.P18AdditiveRKTableau.bPerturbation (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          tableau)
        fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    (third_order_consistency :
        @HighamBench.p18ThirdOrderConsistency (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) tableau) →
      (smooth_perturbation_order_three :
          @HighamBench.p18SmoothPerturbationOrderThree (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            tableau) →
        HighamBench.P18Method4s3pCSourceModel
```

### D020: `HighamBench.P18StableMethod4s3pCBranch.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `224a522c55dcc76379285e44bf7b71abb90a4a6a1a6626f661bfc913eaeb9b59`

Type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup State] →
    [inst_1 : NormedSpace Real State] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            HighamBench.P18TauRegime →
              (step : ι → Real) →
                (epsilon : Real) →
                  (stepCount : ι → Nat) →
                    (horizon localSchemeConstant localPerturbationConstant stabilityConstant : Real) →
                      (∀ (t : ι), Real.instLE.le 0 (step t)) →
                        Real.instLT.lt 0 epsilon →
                          (∀ (t : ι), instLTNat.lt 0 (stepCount t)) →
                            Real.instLE.le 0 horizon →
                              Real.instLE.le 0 localSchemeConstant →
                                Real.instLE.le 0 localPerturbationConstant →
                                  Real.instLE.le 0 stabilityConstant →
                                    (F FEpsilon tau : State → State) →
                                      (computedState exactState :
                                          (t : ι) → Fin (instHAdd.hAdd (stepCount t) 1) → State) →
                                        (oneStep :
                                            (t : ι) → Fin (stepCount t) → HighamBench.P18AdditiveRKOneStepRun State 4) →
                                          (∀ (t : ι) (j : Fin (stepCount t)), Eq (oneStep t j).step (step t)) →
                                            (∀ (t : ι) (j : Fin (stepCount t)), Eq (oneStep t j).epsilon epsilon) →
                                              (∀ (t : ι) (j : Fin (stepCount t)), Eq (oneStep t j).F F) →
                                                (∀ (t : ι) (j : Fin (stepCount t)),
                                                    Eq (oneStep t j).FEpsilon FEpsilon) →
                                                  (∀ (t : ι) (j : Fin (stepCount t)), Eq (oneStep t j).tau tau) →
                                                    (∀ (t : ι) (j : Fin (stepCount t)),
                                                        Eq (oneStep t j).a method.tableau.A) →
                                                      (∀ (t : ι) (j : Fin (stepCount t)),
                                                          Eq (oneStep t j).aPerturbation method.tableau.APerturbation) →
                                                        (∀ (t : ι) (j : Fin (stepCount t)),
                                                            Eq (oneStep t j).b method.tableau.b) →
                                                          (∀ (t : ι) (j : Fin (stepCount t)),
                                                              Eq (oneStep t j).bPerturbation
                                                                method.tableau.bPerturbation) →
                                                            (∀ (t : ι) (j : Fin (stepCount t)),
                                                                Eq (oneStep t j).initial (computedState t j.castSucc)) →
                                                              (∀ (t : ι) (j : Fin (stepCount t)),
                                                                  Eq (oneStep t j).perturbedNext
                                                                    (computedState t j.succ)) →
                                                                (∀ (t : ι) (j : Fin (stepCount t)),
                                                                    Eq (oneStep t j).referenceNext
                                                                      (exactState t j.succ)) →
                                                                  (schemeLocalError perturbationLocalError :
                                                                      (t : ι) → Fin (stepCount t) → Real) →
                                                                    (∀ (t : ι) (j : Fin (stepCount t)),
                                                                        Eq (schemeLocalError t j)
                                                                          (inst.norm
                                                                            (HighamBench.p18SchemeOneStepError
                                                                              (oneStep t j)))) →
                                                                      (∀ (t : ι) (j : Fin (stepCount t)),
                                                                          Eq (perturbationLocalError t j)
                                                                            (inst.norm
                                                                              (HighamBench.p18PerturbationOneStepError
                                                                                (oneStep t j)))) →
                                                                        (∀ (t : ι) (j : Fin (stepCount t)),
                                                                            Real.instLE.le (schemeLocalError t j)
                                                                              (instHMul.hMul localSchemeConstant
                                                                                (instHPow.hPow (step t) 4))) →
                                                                          (∀ (t : ι) (j : Fin (stepCount t)),
                                                                              Real.instLE.le
                                                                                (perturbationLocalError t j)
                                                                                (instHMul.hMul
                                                                                  (instHMul.hMul
                                                                                    localPerturbationConstant
                                                                                    (abs epsilon))
                                                                                  (instHPow.hPow (step t)
                                                                                    localPerturbationPower))) →
                                                                            (globalSchemeError globalPerturbationError
                                                                                globalError : ι → Real) →
                                                                              (∀ (t : ι),
                                                                                  Eq (globalError t)
                                                                                    (inst.norm
                                                                                      (instHSub.hSub
                                                                                        (exactState t
                                                                                          (Fin.last (stepCount t)))
                                                                                        (computedState t
                                                                                          (Fin.last (stepCount t)))))) →
                                                                                (∀ (t : ι),
                                                                                    Eq (globalError t)
                                                                                      (instHAdd.hAdd
                                                                                        (globalSchemeError t)
                                                                                        (globalPerturbationError t))) →
                                                                                  (∀ (t : ι),
                                                                                      Real.instLE.le
                                                                                        (abs (globalSchemeError t))
                                                                                        (instHMul.hMul stabilityConstant
                                                                                          (Finset.univ.sum fun j =>
                                                                                            schemeLocalError t j))) →
                                                                                    (∀ (t : ι),
                                                                                        Real.instLE.le
                                                                                          (abs
                                                                                            (globalPerturbationError t))
                                                                                          (instHMul.hMul
                                                                                            stabilityConstant
                                                                                            (Finset.univ.sum fun j =>
                                                                                              perturbationLocalError t
                                                                                                j))) →
                                                                                      (∀ (t : ι),
                                                                                          Real.instLE.le
                                                                                            (instHMul.hMul
                                                                                              (stepCount t).cast
                                                                                              (step t))
                                                                                            horizon) →
                                                                                        HighamBench.P18StableMethod4s3pCBranch
                                                                                          State ι method
                                                                                          localPerturbationPower
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : NormedAddCommGroup.{u_1} State] →
    [inst_1 :
        @NormedSpace.{0, u_1} Real State Real.normedField
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)] →
      {ι : Type u_2} →
        {method : HighamBench.P18Method4s3pCSourceModel} →
          {localPerturbationPower : Nat} →
            (tauRegime : HighamBench.P18TauRegime) →
              (step : ι → Real) →
                (epsilon : Real) →
                  (stepCount : ι → Nat) →
                    (horizon localSchemeConstant localPerturbationConstant stabilityConstant : Real) →
                      (step_nonneg :
                          ∀ (t : ι),
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (step t)) →
                        (epsilon_pos :
                            @LT.lt.{0} Real Real.instLT
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon) →
                          (step_count_pos :
                              ∀ (t : ι),
                                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  (stepCount t)) →
                            (horizon_nonneg :
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) horizon) →
                              (local_scheme_constant_nonneg :
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    localSchemeConstant) →
                                (local_perturbation_constant_nonneg :
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      localPerturbationConstant) →
                                  (stability_constant_nonneg :
                                      @LE.le.{0} Real Real.instLE
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        stabilityConstant) →
                                    (F FEpsilon tau : State → State) →
                                      (computedState exactState :
                                          (t : ι) →
                                            Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (stepCount t)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              State) →
                                        (oneStep :
                                            (t : ι) →
                                              Fin (stepCount t) →
                                                @HighamBench.P18AdditiveRKOneStepRun.{u_1} State
                                                  (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                  (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)
                                                    inst_1)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
                                          (run_step :
                                              ∀ (t : ι) (j : Fin (stepCount t)),
                                                @Eq.{1} Real
                                                  (@HighamBench.P18AdditiveRKOneStepRun.step.{u_1} State
                                                    (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                    (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)
                                                      inst_1)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    (oneStep t j))
                                                  (step t)) →
                                            (run_epsilon :
                                                ∀ (t : ι) (j : Fin (stepCount t)),
                                                  @Eq.{1} Real
                                                    (@HighamBench.P18AdditiveRKOneStepRun.epsilon.{u_1} State
                                                      (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                      (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State inst)
                                                        inst_1)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      (oneStep t j))
                                                    epsilon) →
                                              (run_F :
                                                  ∀ (t : ι) (j : Fin (stepCount t)),
                                                    @Eq.{u_1 + 1} (State → State)
                                                      (@HighamBench.P18AdditiveRKOneStepRun.F.{u_1} State
                                                        (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                        (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State
                                                            inst)
                                                          inst_1)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        (oneStep t j))
                                                      F) →
                                                (run_FEpsilon :
                                                    ∀ (t : ι) (j : Fin (stepCount t)),
                                                      @Eq.{u_1 + 1} (State → State)
                                                        (@HighamBench.P18AdditiveRKOneStepRun.FEpsilon.{u_1} State
                                                          (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                          (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State
                                                              inst)
                                                            inst_1)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          (oneStep t j))
                                                        FEpsilon) →
                                                  (run_tau :
                                                      ∀ (t : ι) (j : Fin (stepCount t)),
                                                        @Eq.{u_1 + 1} (State → State)
                                                          (@HighamBench.P18AdditiveRKOneStepRun.tau.{u_1} State
                                                            (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                            (@NormedSpace.toModule.{0, u_1} Real State Real.normedField
                                                              (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1} State
                                                                inst)
                                                              inst_1)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            (oneStep t j))
                                                          tau) →
                                                    (run_A :
                                                        ∀ (t : ι) (j : Fin (stepCount t)),
                                                          @Eq.{1}
                                                            (Fin
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4))) →
                                                              Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4))) →
                                                                Real)
                                                            (@HighamBench.P18AdditiveRKOneStepRun.a.{u_1} State
                                                              (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                              (@NormedSpace.toModule.{0, u_1} Real State
                                                                Real.normedField
                                                                (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                  State inst)
                                                                inst_1)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              (oneStep t j))
                                                            (@HighamBench.P18AdditiveRKTableau.A
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              (HighamBench.P18Method4s3pCSourceModel.tableau method))) →
                                                      (run_APerturbation :
                                                          ∀ (t : ι) (j : Fin (stepCount t)),
                                                            @Eq.{1}
                                                              (Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4))) →
                                                                Fin
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4))) →
                                                                  Real)
                                                              (@HighamBench.P18AdditiveRKOneStepRun.aPerturbation.{u_1}
                                                                State
                                                                (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                                (@NormedSpace.toModule.{0, u_1} Real State
                                                                  Real.normedField
                                                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                    State inst)
                                                                  inst_1)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                (oneStep t j))
                                                              (@HighamBench.P18AdditiveRKTableau.APerturbation
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                (HighamBench.P18Method4s3pCSourceModel.tableau
                                                                  method))) →
                                                        (run_b :
                                                            ∀ (t : ι) (j : Fin (stepCount t)),
                                                              @Eq.{1}
                                                                (Fin
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4))) →
                                                                  Real)
                                                                (@HighamBench.P18AdditiveRKOneStepRun.b.{u_1} State
                                                                  (@NormedAddCommGroup.toAddCommGroup.{u_1} State inst)
                                                                  (@NormedSpace.toModule.{0, u_1} Real State
                                                                    Real.normedField
                                                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                      State inst)
                                                                    inst_1)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  (oneStep t j))
                                                                (@HighamBench.P18AdditiveRKTableau.b
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  (HighamBench.P18Method4s3pCSourceModel.tableau
                                                                    method))) →
                                                          (run_bPerturbation :
                                                              ∀ (t : ι) (j : Fin (stepCount t)),
                                                                @Eq.{1}
                                                                  (Fin
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4))) →
                                                                    Real)
                                                                  (@HighamBench.P18AdditiveRKOneStepRun.bPerturbation.{u_1}
                                                                    State
                                                                    (@NormedAddCommGroup.toAddCommGroup.{u_1} State
                                                                      inst)
                                                                    (@NormedSpace.toModule.{0, u_1} Real State
                                                                      Real.normedField
                                                                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                        State inst)
                                                                      inst_1)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    (oneStep t j))
                                                                  (@HighamBench.P18AdditiveRKTableau.bPerturbation
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    (HighamBench.P18Method4s3pCSourceModel.tableau
                                                                      method))) →
                                                            (run_initial :
                                                                ∀ (t : ι) (j : Fin (stepCount t)),
                                                                  @Eq.{u_1 + 1} State
                                                                    (@HighamBench.P18AdditiveRKOneStepRun.initial.{u_1}
                                                                      State
                                                                      (@NormedAddCommGroup.toAddCommGroup.{u_1} State
                                                                        inst)
                                                                      (@NormedSpace.toModule.{0, u_1} Real State
                                                                        Real.normedField
                                                                        (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                          State inst)
                                                                        inst_1)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4)))
                                                                      (oneStep t j))
                                                                    (computedState t (@Fin.castSucc (stepCount t) j))) →
                                                              (run_perturbed_next :
                                                                  ∀ (t : ι) (j : Fin (stepCount t)),
                                                                    @Eq.{u_1 + 1} State
                                                                      (@HighamBench.P18AdditiveRKOneStepRun.perturbedNext.{u_1}
                                                                        State
                                                                        (@NormedAddCommGroup.toAddCommGroup.{u_1} State
                                                                          inst)
                                                                        (@NormedSpace.toModule.{0, u_1} Real State
                                                                          Real.normedField
                                                                          (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                            State inst)
                                                                          inst_1)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                          (instOfNatNat (nat_lit 4)))
                                                                        (oneStep t j))
                                                                      (computedState t (@Fin.succ (stepCount t) j))) →
                                                                (run_reference_next :
                                                                    ∀ (t : ι) (j : Fin (stepCount t)),
                                                                      @Eq.{u_1 + 1} State
                                                                        (@HighamBench.P18AdditiveRKOneStepRun.referenceNext.{u_1}
                                                                          State
                                                                          (@NormedAddCommGroup.toAddCommGroup.{u_1}
                                                                            State inst)
                                                                          (@NormedSpace.toModule.{0, u_1} Real State
                                                                            Real.normedField
                                                                            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                              State inst)
                                                                            inst_1)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                            (instOfNatNat (nat_lit 4)))
                                                                          (oneStep t j))
                                                                        (exactState t (@Fin.succ (stepCount t) j))) →
                                                                  (schemeLocalError perturbationLocalError :
                                                                      (t : ι) → Fin (stepCount t) → Real) →
                                                                    (scheme_local_error_eq :
                                                                        ∀ (t : ι) (j : Fin (stepCount t)),
                                                                          @Eq.{1} Real (schemeLocalError t j)
                                                                            (@Norm.norm.{u_1} State
                                                                              (@NormedAddCommGroup.toNorm.{u_1} State
                                                                                inst)
                                                                              (@HighamBench.p18SchemeOneStepError.{u_1}
                                                                                State
                                                                                (@NormedAddCommGroup.toAddCommGroup.{u_1}
                                                                                  State inst)
                                                                                (@NormedSpace.toModule.{0, u_1} Real
                                                                                  State Real.normedField
                                                                                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                                    State inst)
                                                                                  inst_1)
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                                  (instOfNatNat (nat_lit 4)))
                                                                                (oneStep t j)))) →
                                                                      (perturbation_local_error_eq :
                                                                          ∀ (t : ι) (j : Fin (stepCount t)),
                                                                            @Eq.{1} Real (perturbationLocalError t j)
                                                                              (@Norm.norm.{u_1} State
                                                                                (@NormedAddCommGroup.toNorm.{u_1} State
                                                                                  inst)
                                                                                (@HighamBench.p18PerturbationOneStepError.{u_1}
                                                                                  State
                                                                                  (@NormedAddCommGroup.toAddCommGroup.{u_1}
                                                                                    State inst)
                                                                                  (@NormedSpace.toModule.{0, u_1} Real
                                                                                    State Real.normedField
                                                                                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_1}
                                                                                      State inst)
                                                                                    inst_1)
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                                    (instOfNatNat (nat_lit 4)))
                                                                                  (oneStep t j)))) →
                                                                        (scheme_local_bound :
                                                                            ∀ (t : ι) (j : Fin (stepCount t)),
                                                                              @LE.le.{0} Real Real.instLE
                                                                                (schemeLocalError t j)
                                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul)
                                                                                  localSchemeConstant
                                                                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                                                    (@instHPow.{0, 0} Real Nat
                                                                                      (@Monoid.toNatPow.{0} Real
                                                                                        Real.instMonoid))
                                                                                    (step t)
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                                      (instOfNatNat (nat_lit 4)))))) →
                                                                          (perturbation_local_bound :
                                                                              ∀ (t : ι) (j : Fin (stepCount t)),
                                                                                @LE.le.{0} Real Real.instLE
                                                                                  (perturbationLocalError t j)
                                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                    (@instHMul.{0} Real Real.instMul)
                                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                      (@instHMul.{0} Real Real.instMul)
                                                                                      localPerturbationConstant
                                                                                      (@abs.{0} Real Real.lattice
                                                                                        Real.instAddGroup epsilon))
                                                                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                                                      (@instHPow.{0, 0} Real Nat
                                                                                        (@Monoid.toNatPow.{0} Real
                                                                                          Real.instMonoid))
                                                                                      (step t)
                                                                                      localPerturbationPower))) →
                                                                            (globalSchemeError globalPerturbationError
                                                                                globalError : ι → Real) →
                                                                              (global_error_eq :
                                                                                  ∀ (t : ι),
                                                                                    @Eq.{1} Real (globalError t)
                                                                                      (@Norm.norm.{u_1} State
                                                                                        (@NormedAddCommGroup.toNorm.{u_1}
                                                                                          State inst)
                                                                                        (@HSub.hSub.{u_1, u_1, u_1}
                                                                                          State State State
                                                                                          (@instHSub.{u_1} State
                                                                                            (@SubNegMonoid.toSub.{u_1}
                                                                                              State
                                                                                              (@AddGroup.toSubNegMonoid.{u_1}
                                                                                                State
                                                                                                (@NormedAddGroup.toAddGroup.{u_1}
                                                                                                  State
                                                                                                  (@NormedAddCommGroup.toNormedAddGroup.{u_1}
                                                                                                    State inst)))))
                                                                                          (exactState t
                                                                                            (Fin.last (stepCount t)))
                                                                                          (computedState t
                                                                                            (Fin.last
                                                                                              (stepCount t)))))) →
                                                                                (global_split :
                                                                                    ∀ (t : ι),
                                                                                      @Eq.{1} Real (globalError t)
                                                                                        (@HAdd.hAdd.{0, 0, 0} Real Real
                                                                                          Real
                                                                                          (@instHAdd.{0} Real
                                                                                            Real.instAdd)
                                                                                          (globalSchemeError t)
                                                                                          (globalPerturbationError
                                                                                            t))) →
                                                                                  (stable_scheme_accumulation :
                                                                                      ∀ (t : ι),
                                                                                        @LE.le.{0} Real Real.instLE
                                                                                          (@abs.{0} Real Real.lattice
                                                                                            Real.instAddGroup
                                                                                            (globalSchemeError t))
                                                                                          (@HMul.hMul.{0, 0, 0} Real
                                                                                            Real Real
                                                                                            (@instHMul.{0} Real
                                                                                              Real.instMul)
                                                                                            stabilityConstant
                                                                                            (@Finset.sum.{0, 0}
                                                                                              (Fin (stepCount t)) Real
                                                                                              Real.instAddCommMonoid
                                                                                              (@Finset.univ.{0}
                                                                                                (Fin (stepCount t))
                                                                                                (Fin.fintype
                                                                                                  (stepCount t)))
                                                                                              fun
                                                                                                (j :
                                                                                                  Fin (stepCount t)) =>
                                                                                              schemeLocalError t j))) →
                                                                                    (stable_perturbation_accumulation :
                                                                                        ∀ (t : ι),
                                                                                          @LE.le.{0} Real Real.instLE
                                                                                            (@abs.{0} Real Real.lattice
                                                                                              Real.instAddGroup
                                                                                              (globalPerturbationError
                                                                                                t))
                                                                                            (@HMul.hMul.{0, 0, 0} Real
                                                                                              Real Real
                                                                                              (@instHMul.{0} Real
                                                                                                Real.instMul)
                                                                                              stabilityConstant
                                                                                              (@Finset.sum.{0, 0}
                                                                                                (Fin (stepCount t)) Real
                                                                                                Real.instAddCommMonoid
                                                                                                (@Finset.univ.{0}
                                                                                                  (Fin (stepCount t))
                                                                                                  (Fin.fintype
                                                                                                    (stepCount t)))
                                                                                                fun
                                                                                                  (j :
                                                                                                    Fin
                                                                                                      (stepCount t)) =>
                                                                                                perturbationLocalError t
                                                                                                  j))) →
                                                                                      (finite_time_horizon :
                                                                                          ∀ (t : ι),
                                                                                            @LE.le.{0} Real Real.instLE
                                                                                              (@HMul.hMul.{0, 0, 0} Real
                                                                                                Real Real
                                                                                                (@instHMul.{0} Real
                                                                                                  Real.instMul)
                                                                                                (@Nat.cast.{0} Real
                                                                                                  Real.instNatCast
                                                                                                  (stepCount t))
                                                                                                (step t))
                                                                                              horizon) →
                                                                                        @HighamBench.P18StableMethod4s3pCBranch.{u_1,
                                                                                              u_2}
                                                                                          State inst inst_1 ι method
                                                                                          localPerturbationPower
```

### D021: `HighamBench.p18CoeffDot`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `bd9b2b87931791a0513395de521f55820ffea08ecd6e5327f9285fb57802653d`

Type:

```lean
{s : Nat} → (Fin s → Real) → (Fin s → Real) → Real
```

Fully explicit type:

```lean
{s : Nat} → (x y : Fin s → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x y => Finset.univ.sum fun i => instHMul.hMul (x i) (y i)
```

### D022: `HighamBench.p18CoeffHadamard`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9744d86b4fa53b459dbaebbe4af9ed542fc9df730bcfb949971f292acb657aa1`

Type:

```lean
{s : Nat} → (Fin s → Real) → (Fin s → Real) → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (x y : Fin s → Real) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x y i => instHMul.hMul (x i) (y i)
```

### D023: `HighamBench.p18CoeffMatVec`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6d6065bfcec4876b221aaa96bfe3d07b5525312256365327c3ca230674119e64`

Type:

```lean
{s : Nat} → (Fin s → Fin s → Real) → (Fin s → Real) → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (A : Fin s → Fin s → Real) → (x : Fin s → Real) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D024: `HighamBench.p18CorrectedMidpointA._proof_1`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `73b505915b492ba531c87e9764e0d5ad003f6adabc0e4e427d7163ba079d5cba`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D025: `HighamBench.p18TableauATilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ee8220c148f360ca2c5581b83d4a26c93a56906d502543cb9d7960e7a62a6d88`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau => HighamBench.p18CoeffMatAdd tableau.A tableau.APerturbation
```

### D026: `HighamBench.p18TableauBTilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `75e5557b9f1d25c9fc334bbb26be595e568a8e1c1ea0336a2763f55723d6edcd`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau => HighamBench.p18Add tableau.b tableau.bPerturbation
```

### D027: `HighamBench.p18TableauCPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3e5040c5d4123ace5781f5d5fd1a125734ba9089b6dcdb677aefb7bc3fa0742d`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau => HighamBench.p18CoeffMatVec tableau.APerturbation HighamBench.p18TableauE
```

### D028: `HighamBench.p18TableauCTilde`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `94ced9dc72e33e54e521deaacff695cfc380e2a480195b71a78e5489b47e640a`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau => HighamBench.p18Add (HighamBench.p18TableauC tableau) (HighamBench.p18TableauCPerturbation tableau)
```

### D029: `HighamBench.p18TableauE`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7f9f543d69d4b74969293f396c6f6ea54c726476744bc18edb84b55ece100b83`

Type:

```lean
{s : Nat} → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} x => 1
```

### D030: `HighamBench.p18ThirdOrderConsistency._proof_1`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `a08ab4402398c6bd1f68f19c36b1f99fa188c4d2b9ddc5c58819fbef332199e7`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D031: `HighamBench.p18ThirdOrderConsistency._proof_2`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `70330146196be1e0bd3bb184c8f7f9f37293db5721456c8e46d7ecd135c088cc`

Type:

```lean
(instHAdd.hAdd 5 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D032: `HighamBench.P18AdditiveRKOneStepRun`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
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

### D033: `HighamBench.P18AdditiveRKOneStepRun.F`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D034: `HighamBench.P18AdditiveRKOneStepRun.FEpsilon`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D035: `HighamBench.P18AdditiveRKOneStepRun.a`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0f9c153d0cd46b9791739d00a4768217bb7c8c6fde5416b08c99c12b7fa3497d`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.11
```

### D036: `HighamBench.P18AdditiveRKOneStepRun.aPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9a3bf9a637c1264ca777e2bfbc389a858ba65c40f2de15e85ba7af199dcb2dee`

Type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup State] →
    [inst_1 : Module Real State] → {s : Nat} → HighamBench.P18AdditiveRKOneStepRun State s → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{State : Type u_1} →
  [inst : AddCommGroup.{u_1} State] →
    [inst_1 : @Module.{0, u_1} Real State Real.semiring (@AddCommGroup.toAddCommMonoid.{u_1} State inst)] →
      {s : Nat} → (self : @HighamBench.P18AdditiveRKOneStepRun.{u_1} State inst inst_1 s) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun State [AddCommGroup State] [Module Real State] s self => self.12
```

### D037: `HighamBench.P18AdditiveRKOneStepRun.b`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D038: `HighamBench.P18AdditiveRKOneStepRun.bPerturbation`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D039: `HighamBench.P18AdditiveRKOneStepRun.epsilon`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b8f3fdd154bd6f63357f69d7dfe27513624444bd796b6152e818628c0c7b341a`

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
fun State [AddCommGroup State] [Module Real State] s self => self.3
```

### D040: `HighamBench.P18AdditiveRKOneStepRun.initial`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a1d9a129ef7f7ff51092afa79cb5b7510ea48203531575727b2ec8061645c016`

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
fun State [AddCommGroup State] [Module Real State] s self => self.5
```

### D041: `HighamBench.P18AdditiveRKOneStepRun.perturbedNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D042: `HighamBench.P18AdditiveRKOneStepRun.referenceNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D043: `HighamBench.P18AdditiveRKOneStepRun.step`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D044: `HighamBench.P18AdditiveRKOneStepRun.tau`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fba1f2a6ed49485a5bf5b6dd06ec358aa020f06b6341a6b58fa15d8a0e1b1577`

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
fun State [AddCommGroup State] [Module Real State] s self => self.9
```

### D045: `HighamBench.P18AdditiveRKTableau.A`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9c294a133dc31407762d606ef5236571d24d78c08b8136987df454e3a7a6072a`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (self : HighamBench.P18AdditiveRKTableau s) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun s self => self.1
```

### D046: `HighamBench.P18AdditiveRKTableau.b`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `bc1a09a3bf27bdb80e4ec9aaea5a9f788dde8b3bddf7443e41f00e147cc59aea`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (self : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun s self => self.3
```

### D047: `HighamBench.P18AdditiveRKTableau.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c7bf0253d56b9ad83cb43ab3220b7425bdf19ae60ad08a231d32de9892ba92c7`

Type:

```lean
{s : Nat} →
  (Fin s → Fin s → Real) → (Fin s → Fin s → Real) → (Fin s → Real) → (Fin s → Real) → HighamBench.P18AdditiveRKTableau s
```

Fully explicit type:

```lean
{s : Nat} →
  (A APerturbation : Fin s → Fin s → Real) → (b bPerturbation : Fin s → Real) → HighamBench.P18AdditiveRKTableau s
```

### D048: `HighamBench.p18Add`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a618ade07a852d5fd95ede3f352cb8e1b2123e6bc0d9cc7b34857ff4b7502a01`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHAdd.hAdd (x i) (y i)
```

### D049: `HighamBench.p18CoeffMatAdd`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `56b7797f070c648392187943e282e7b0bd11f79ea8e2fa3f5d933012f7f63e9c`

Type:

```lean
{s : Nat} → (Fin s → Fin s → Real) → (Fin s → Fin s → Real) → Fin s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (A B : Fin s → Fin s → Real) → Fin s → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} A B i j => instHAdd.hAdd (A i j) (B i j)
```

### D050: `HighamBench.p18PerturbationOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D051: `HighamBench.p18SchemeOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D052: `HighamBench.p18TableauC`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2e0354735cf2ca33d0bbfb256d00c7c118a4b8aa88c70d94590150143dfd5fcc`

Type:

```lean
{s : Nat} → HighamBench.P18AdditiveRKTableau s → Fin s → Real
```

Fully explicit type:

```lean
{s : Nat} → (tableau : HighamBench.P18AdditiveRKTableau s) → Fin s → Real
```

Definition body (one-level semantic boundary):

```lean
fun {s} tableau => HighamBench.p18CoeffMatVec tableau.A HighamBench.p18TableauE
```

### D053: `HighamBench.P18AdditiveRKOneStepRun.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
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

### D054: `HighamBench.P18AdditiveRKOneStepRun.schemeNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D055: `HighamBench.p18ModuleStageSum`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D056: `And`

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

### D057: `Eq`

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

### D058: `Fin`

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

### D059: `Nat`

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

### D060: `NormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `7289fc1f1aac42f488a1fe69c897c4d418a0fa8699118dd0f273085d7d95b741`

Type:

```lean
Type u_8 → Type u_8
```

Fully explicit type:

```lean
(E : Type u_8) → Type u_8
```

### D061: `NormedAddCommGroup.toSeminormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7327759e5e9417c54393e7566584cd72d79c77b4ca018ea408c5d024667587be`

Type:

```lean
{E : Type u_5} → [NormedAddCommGroup E] → SeminormedAddCommGroup E
```

Fully explicit type:

```lean
{E : Type u_5} → [NormedAddCommGroup.{u_5} E] → SeminormedAddCommGroup.{u_5} E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : NormedAddCommGroup E] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddCommGroup := __src.toAddCommGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D062: `NormedSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Module.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `6b6b5b2582dac5d94b5d2a99eac51e4b8bee1f8e652cdec27b52f9c5d5ca5960`

Type:

```lean
(𝕜 : Type u_6) → (E : Type u_7) → [NormedField 𝕜] → [SeminormedAddCommGroup E] → Type (max u_6 u_7)
```

Fully explicit type:

```lean
(𝕜 : Type u_6) → (E : Type u_7) → [NormedField.{u_6} 𝕜] → [SeminormedAddCommGroup.{u_7} E] → Type (max u_6 u_7)
```

### D063: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D064: `Real`

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

### D065: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D066: `Real.normedField`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Field.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3249555a2824aa1e4e9c966b630ef876ae52df63ed09d0838da173aa28c0f77b`

Type:

```lean
NormedField Real
```

Fully explicit type:

```lean
NormedField.{0} Real
```

Definition body (one-level semantic boundary):

```lean
let __src := Real.normedAddCommGroup;
let __src_1 := Real.instField;
{ toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := Real.normedField._proof_1,
  toMul := __src_1.toMul, left_distrib := Real.normedField._proof_2, right_distrib := Real.normedField._proof_3,
  zero_mul := Real.normedField._proof_4, mul_zero := Real.normedField._proof_5, mul_assoc := Real.normedField._proof_6,
  toOne := __src_1.toOne, one_mul := Real.normedField._proof_7, mul_one := Real.normedField._proof_8,
  toNatCast := __src_1.toNatCast, natCast_zero := Real.normedField._proof_9, natCast_succ := Real.normedField._proof_10,
  npow := __src_1.npow, npow_zero := Real.normedField._proof_11, npow_succ := Real.normedField._proof_12,
  toNeg := __src.toNeg, toSub := __src.toSub, sub_eq_add_neg := Real.normedField._proof_13, zsmul := __src.zsmul,
  zsmul_zero' := Real.normedField._proof_14, zsmul_succ' := Real.normedField._proof_15,
  zsmul_neg' := Real.normedField._proof_16, neg_add_cancel := Real.normedField._proof_17,
  toIntCast := __src_1.toIntCast, intCast_ofNat := Real.normedField._proof_18,
  intCast_negSucc := Real.normedField._proof_19, mul_comm := Real.normedField._proof_20, toInv := __src_1.toInv,
  toDiv := __src_1.toDiv, div_eq_mul_inv := ⋯, zpow := __src_1.zpow, zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯,
  toNontrivial := ⋯, toNNRatCast := __src_1.toNNRatCast, toRatCast := __src_1.toRatCast, mul_inv_cancel := ⋯,
  inv_zero := ⋯, nnratCast_def := ⋯, nnqsmul := __src_1.nnqsmul, nnqsmul_def := ⋯, ratCast_def := ⋯,
  qsmul := __src_1.qsmul, qsmul_def := ⋯, toMetricSpace := __src.toMetricSpace, dist_eq := ⋯, norm_mul := ⋯ }
```

### D067: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D068: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D069: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Fully explicit type:

```lean
{G : Type u} → [self : DivInvMonoid.{u} G] → Div.{u} G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D070: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D071: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D072: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HDiv.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D073: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HMul.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D074: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D075: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D076: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D077: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Fully explicit type:

```lean
{α : Type u_1} → [One.{u_1} α] → OfNat.{u_1} α (nat_lit 1)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D078: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D079: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Fully explicit type:

```lean
AddGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D080: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`

Type:

```lean
DivInvMonoid Real
```

Fully explicit type:

```lean
DivInvMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toMonoid := Real.instMonoid, toInv := Real.instInv, div := DivInvMonoid.div',
  div_eq_mul_inv := Real.instDivInvMonoid._proof_1, zpow := zpowRec, zpow_zero' := Real.instDivInvMonoid._proof_2,
  zpow_succ' := Real.instDivInvMonoid._proof_3, zpow_neg' := Real.instDivInvMonoid._proof_4 }
```

### D081: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D082: `Real.instMonoid`

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

### D083: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Fully explicit type:

```lean
Mul.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D084: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Fully explicit type:

```lean
NatCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D085: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Fully explicit type:

```lean
One.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
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

Fully explicit type:

```lean
Lattice.{0} Real
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

Fully explicit type:

```lean
{α : Type u_1} → [Lattice.{u_1} α] → [AddGroup.{u_1} α] → (a : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D088: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

Fully explicit type:

```lean
{α : Type u_1} → [Div.{u_1} α] → HDiv.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D090: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Mul.{u_1} α] → HMul.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D091: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D092: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Fully explicit type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast.{u_1} R] → [Nat.AtLeastTwo n] → OfNat.{u_1} R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D093: `AddGroup.toSubNegMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D094: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
{n : Nat} →
  Fin n →
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D095: `Fin.fintype`

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

### D096: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`

Type:

```lean
(n : Nat) → Fin (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
(n : Nat) →
  Fin
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun n => ⟨n, ⋯⟩
```

### D097: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
{n : Nat} →
  Fin n →
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D098: `Finset.sum`

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

### D099: `Finset.univ`

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

### D100: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D101: `LT.lt`

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

### D102: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

Fully explicit type:

```lean
(n : Nat) → Prop
```

### D103: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D104: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Fully explicit type:

```lean
{E : Type u_8} → [self : Norm.{u_8} E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D105: `NormedAddCommGroup.toAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c92bdde4376567f29ebdebaf4a7dd986bfb96211cd0306e14540b80cd23009d2`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → AddCommGroup E
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup.{u_8} E] → AddCommGroup.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.2
```

### D106: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup.{u_8} E] → Norm.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D107: `NormedAddCommGroup.toNormedAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cdc7999c66248f7b0f68477de30ff4d9ea7a7f0df0bc6f092bc024f699d646fe`

Type:

```lean
{E : Type u_5} → [NormedAddCommGroup E] → NormedAddGroup E
```

Fully explicit type:

```lean
{E : Type u_5} → [NormedAddCommGroup.{u_5} E] → NormedAddGroup.{u_5} E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : NormedAddCommGroup E] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddGroup := __src.toAddGroup, toMetricSpace := __src.toMetricSpace, dist_eq := ⋯ }
```

### D108: `NormedAddGroup.toAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `06ba17aab699c28aaa8877d0b107536ebd2aefd8bf59143b2357c84bb820d89e`

Type:

```lean
{E : Type u_8} → [self : NormedAddGroup E] → AddGroup E
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NormedAddGroup.{u_8} E] → AddGroup.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddGroup E] => self.2
```

### D109: `NormedSpace.toModule`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Module.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `5ced27e2d9cc2259d662cced299ca3071b9598822fc551dad5a5d6dd0f3a9df4`

Type:

```lean
{𝕜 : Type u_6} →
  {E : Type u_7} → {inst : NormedField 𝕜} → {inst_1 : SeminormedAddCommGroup E} → [self : NormedSpace 𝕜 E] → Module 𝕜 E
```

Fully explicit type:

```lean
{𝕜 : Type u_6} →
  {E : Type u_7} →
    {inst : NormedField.{u_6} 𝕜} →
      {inst_1 : SeminormedAddCommGroup.{u_7} E} →
        [self : @NormedSpace.{u_6, u_7} 𝕜 E inst inst_1] →
          @Module.{u_6, u_7} 𝕜 E
            (@DivisionSemiring.toSemiring.{u_6} 𝕜
              (@Semifield.toDivisionSemiring.{u_6} 𝕜 (@Field.toSemifield.{u_6} 𝕜 (@NormedField.toField.{u_6} 𝕜 inst))))
            (@AddCommGroup.toAddCommMonoid.{u_7} E (@SeminormedAddCommGroup.toAddCommGroup.{u_7} E inst_1))
```

Definition body (one-level semantic boundary):

```lean
fun 𝕜 E {inst} {inst_1} [self : NormedSpace 𝕜 E] => self.1
```

### D110: `Real.instAddCommMonoid`

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

### D111: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Fully explicit type:

```lean
LT.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D112: `SubNegMonoid.toSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D113: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Fully explicit type:

```lean
Add.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D114: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D115: `instLTNat`

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

### D116: `AddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `087ff419a44ee7e835bedcf1beda5a1fee5971b4ef4f17124a5a63cd2b0beb30`

Type:

```lean
Type u → Type u
```

Fully explicit type:

```lean
(G : Type u) → Type u
```

### D117: `AddCommGroup.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D118: `AddCommGroup.toAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D119: `Module`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Module.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `132ed119db2ae117b4c85e91594e4fcde0e02a8fde0fb2ee5c57a7a9263c219c`

Type:

```lean
(R : Type u) → (M : Type v) → [Semiring R] → [AddCommMonoid M] → Type (max u v)
```

Fully explicit type:

```lean
(R : Type u) → (M : Type v) → [Semiring.{u} R] → [AddCommMonoid.{v} M] → Type (max u v)
```

### D120: `Real.semiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D121: `AddCommMagma.toAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D122: `AddCommMonoid.toAddCommSemigroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D123: `AddCommSemigroup.toAddCommMagma`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D124: `AddMonoid.toAddZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D125: `AddZero.toZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D126: `AddZeroClass.toAddZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D127: `DistribMulAction.toDistribSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D128: `DistribSMul.toSMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D129: `HSMul.hSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D130: `Module.toDistribMulAction`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Module.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D131: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D132: `SMulZeroClass.toSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Action.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D133: `SubNegMonoid.toAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D134: `instHSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
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

## Complete local imported sources

### `HighamBench.Core`

Path: `paper_bencmark/highambench/shared/HighamBench/Core.lean`
SHA-256: `8c84e05c04f4245e067d3a971dafa45bcfe92f55bbc24f2305964a8e2b9bd55a`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench common core

This file is deliberately independent of the evaluated library. It contains
only the floating-point model and notation used by more than one benchmark
paper.
-/

namespace HighamBench

open scoped BigOperators

/-- The part of the usual floating-point model needed for ordinary summation. -/
structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- Higham's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- The denominator in `gamma u n` is positive. -/
def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Left-to-right recursive summation, with a one-element sum kept exact. -/
noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

end HighamBench
```

### `HighamBench.P18Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P18Definitions.lean`
SHA-256: `d0fdac24940ee54cdcd5a60f0c0e4fc4c81d30ef6c03fc89dde95dfc627ecbad`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Paper-scoped squared Euclidean norm for finite Runge--Kutta error vectors. -/
noncomputable def p18VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite Runge--Kutta error vectors. -/
noncomputable def p18VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p18VecNorm2Sq x)

/-- Add the scheme and perturbation error components. -/
def p18Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Subtract two finite state vectors. -/
def p18Sub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - y i

/-- Scale a finite error vector. -/
def p18Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- A coefficient-weighted sum of Runge--Kutta stage vectors. -/
noncomputable def p18StageSum {n s : ℕ}
    (weights : Fin s → ℝ) (values : Fin s → Fin n → ℝ) : Fin n → ℝ :=
  fun k => ∑ j : Fin s, weights j * values j k

/-- A coefficient-weighted stage sum in an arbitrary real state module. -/
noncomputable def p18ModuleStageSum {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ} (weights : Fin s → ℝ)
    (values : Fin s → State) : State :=
  ∑ j : Fin s, weights j • values j

/-- One execution of the original additive Runge--Kutta method (3.1), together
with the comparison scheme obtained by replacing `F^epsilon` by `F`.

Using (3.1) avoids choosing a side in the paper's sign conflict: equation
(2.3) gives `epsilon * tau = F - F^epsilon`, whereas (3.2) prints the signs
obtained from the opposite convention. The operator equation below records
(2.3), while the stage and output equations record (3.1) directly. -/
structure P18AdditiveRKOneStepRun (State : Type*) [AddCommGroup State]
    [Module ℝ State] (s : ℕ) where
  stage_count_pos : 0 < s
  step : ℝ
  epsilon : ℝ
  epsilon_ne_zero : epsilon ≠ 0
  initial : State
  referenceNext : State
  F : State → State
  FEpsilon : State → State
  tau : State → State
  operator_perturbation : ∀ y,
    epsilon • tau y = F y - FEpsilon y
  a : Fin s → Fin s → ℝ
  aPerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ
  schemeStages : Fin s → State
  perturbedStages : Fin s → State
  schemeNext : State
  perturbedNext : State
  scheme_stage_equation : ∀ i,
    schemeStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => F (schemeStages j))
  scheme_output_equation :
    schemeNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => F (schemeStages j))
  perturbed_stage_equation : ∀ i,
    perturbedStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => FEpsilon (perturbedStages j))
  perturbed_output_equation :
    perturbedNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => FEpsilon (perturbedStages j))

/-- Total one-step error of the perturbed method. -/
def p18TotalOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.perturbedNext

/-- Approximation error of the unperturbed Runge--Kutta scheme. -/
def p18SchemeOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.schemeNext

/-- Error introduced by replacing the scheme output by the perturbed output. -/
def p18PerturbationOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.schemeNext - run.perturbedNext

/-- Equation (3.1b) unfolded for the difference between the comparison output
and the perturbed output. -/
noncomputable def p18PerturbationOutputExpansion {State : Type*}
    [AddCommGroup State] [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.schemeStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.F (run.schemeStages j))) -
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.perturbedStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.FEpsilon (run.perturbedStages j)))

/-- Finite coefficient dot product used in the P18 order conditions. -/
noncomputable def p18CoeffDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, x i * y i

/-- Finite coefficient matrix-vector product. -/
noncomputable def p18CoeffMatVec {s : ℕ}
    (A : Fin s → Fin s → ℝ) (x : Fin s → ℝ) : Fin s → ℝ :=
  fun i => ∑ j : Fin s, A i j * x j

/-- Pointwise addition of two coefficient matrices. -/
def p18CoeffMatAdd {s : ℕ}
    (A B : Fin s → Fin s → ℝ) : Fin s → Fin s → ℝ :=
  fun i j => A i j + B i j

/-- Absolute-value dot product in the nonsmooth perturbation conditions (3.4). -/
noncomputable def p18CoeffAbsDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, |x i| * |y i|

/-- The two-stage corrected implicit-midpoint coefficient matrix `A` printed
after equation (4.1). -/
noncomputable def p18CorrectedMidpointA : Fin 2 → Fin 2 → ℝ :=
  !![0, 0; (1 / 2 : ℝ), 0]

/-- The corrected implicit-midpoint node vector `c`. -/
noncomputable def p18CorrectedMidpointC : Fin 2 → ℝ :=
  ![0, (1 / 2 : ℝ)]

/-- The corrected implicit-midpoint output weights `b`. -/
noncomputable def p18CorrectedMidpointB : Fin 2 → ℝ :=
  ![0, 1]

/-- The low-precision coefficient matrix `A^epsilon` in equation (4.1). -/
noncomputable def p18CorrectedMidpointAPerturbation : Fin 2 → Fin 2 → ℝ :=
  !![(1 / 2 : ℝ), 0; 0, 0]

/-- The low-precision node vector `c^epsilon`. -/
noncomputable def p18CorrectedMidpointCPerturbation : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), 0]

/-- The low-precision output weights `b^epsilon`. -/
noncomputable def p18CorrectedMidpointBPerturbation : Fin 2 → ℝ :=
  ![0, 0]

/-- The combined corrected-midpoint matrix `A tilde`. -/
noncomputable def p18CorrectedMidpointATilde : Fin 2 → Fin 2 → ℝ :=
  !![(1 / 2 : ℝ), 0; (1 / 2 : ℝ), 0]

/-- The combined corrected-midpoint nodes `c tilde`. -/
noncomputable def p18CorrectedMidpointCTilde : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- The combined corrected-midpoint output weights `b tilde`. -/
noncomputable def p18CorrectedMidpointBTilde : Fin 2 → ℝ :=
  ![0, 1]

/-- The all-ones coefficient vector `e` for the two-stage order conditions. -/
noncomputable def p18CorrectedMidpointE : Fin 2 → ℝ :=
  ![1, 1]

/-- Pointwise coefficient product used in Runge--Kutta order conditions. -/
def p18CoeffHadamard {s : ℕ}
    (x y : Fin s → ℝ) : Fin s → ℝ :=
  fun i => x i * y i

/-- Tolerance used to certify identities from coefficients printed to fifteen
decimal places. -/
noncomputable def p18PrintedCoeffTolerance : ℝ :=
  2 / 10 ^ 15

/-- The full-precision Method 4s3pC matrix printed on page 18. -/
noncomputable def p18Method4s3pCA : Fin 4 → Fin 4 → ℝ :=
  !![0, 0, 0, 0;
     -0.050470366527530, 0, 0, 0;
     0.368613367355336, 0.273504374252976, 0, 0;
     1.803794668975043, 0.097485042980759, -1.895660952342050, 0]

/-- The perturbation matrix `A^epsilon` for Method 4s3pC. -/
noncomputable def p18Method4s3pCAPerturbation : Fin 4 → Fin 4 → ℝ :=
  !![0.511243008730995, 0, 0, 0;
     -1.999347282862640, 1.957161067302390, 0, 0;
     0.443312893511937, -0.573131033672219, 0.128283796414019, 0;
     -2, -0.160330320741428, 0.579597314161362, 1.484688928981990]

/-- The Method 4s3pC output weights `b`. -/
noncomputable def p18Method4s3pCB : Fin 4 → ℝ :=
  ![0.002837446974069, 0.336264433650450,
    0.806376720267787, -0.145478600892306]

/-- The Method 4s3pC perturbation output weights `b^epsilon`. -/
noncomputable def p18Method4s3pCBPerturbation : Fin 4 → ℝ :=
  ![0, 0, 0, 0]

/-- The all-ones vector for the four-stage Method 4s3pC conditions. -/
noncomputable def p18Method4s3pCE : Fin 4 → ℝ :=
  ![1, 1, 1, 1]

/-- The Method 4s3pC full-precision nodes `c = A*e`. -/
noncomputable def p18Method4s3pCC : Fin 4 → ℝ :=
  p18CoeffMatVec p18Method4s3pCA p18Method4s3pCE

/-- The Method 4s3pC perturbation nodes `c^epsilon = A^epsilon*e`. -/
noncomputable def p18Method4s3pCCPerturbation : Fin 4 → ℝ :=
  p18CoeffMatVec p18Method4s3pCAPerturbation p18Method4s3pCE

/-- The combined Method 4s3pC matrix `A tilde`. -/
noncomputable def p18Method4s3pCATilde : Fin 4 → Fin 4 → ℝ :=
  p18CoeffMatAdd p18Method4s3pCA p18Method4s3pCAPerturbation

/-- The combined Method 4s3pC nodes `c tilde`. -/
noncomputable def p18Method4s3pCCTilde : Fin 4 → ℝ :=
  p18Add p18Method4s3pCC p18Method4s3pCCPerturbation

/-- The combined Method 4s3pC weights `b tilde`. -/
noncomputable def p18Method4s3pCBTilde : Fin 4 → ℝ :=
  p18Add p18Method4s3pCB p18Method4s3pCBPerturbation

/-- An exact additive Runge--Kutta tableau. The Method 4s3pC decimals are only
a printed representation of such a tableau; the paper does not identify the
unprinted exact values. -/
structure P18AdditiveRKTableau (s : ℕ) where
  A : Fin s → Fin s → ℝ
  APerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ

noncomputable def p18TableauE {s : ℕ} : Fin s → ℝ :=
  fun _ ↦ 1

noncomputable def p18TableauATilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → Fin s → ℝ :=
  p18CoeffMatAdd tableau.A tableau.APerturbation

noncomputable def p18TableauBTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add tableau.b tableau.bPerturbation

noncomputable def p18TableauC {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.A p18TableauE

noncomputable def p18TableauCPerturbation {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.APerturbation p18TableauE

noncomputable def p18TableauCTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add (p18TableauC tableau) (p18TableauCPerturbation tableau)

/-- All four consistency conditions through order three on page 7. -/
def p18ThirdOrderConsistency {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot (p18TableauBTilde tableau) p18TableauE = 1 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCTilde tableau) = 1 / 2 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 1 / 3 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 1 / 6

/-- Every simplified well-behaved-perturbation condition (3.5a)--(3.5f)
through perturbation order three. Conditions that become automatic when
`b^epsilon = 0` remain explicit. -/
def p18SmoothPerturbationOrderThree {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot tableau.bPerturbation p18TableauE = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCTilde tableau) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0

/-- The source-level interpretation of the underlying exact Method 4s3pC
tableau. Exact order conditions are explicit because the rounded decimal table
cannot prove them as literal rational identities. -/
structure P18Method4s3pCSourceModel where
  tableau : P18AdditiveRKTableau 4
  perturbation_weights_zero : tableau.bPerturbation = fun _ ↦ 0
  third_order_consistency : p18ThirdOrderConsistency tableau
  smooth_perturbation_order_three :
    p18SmoothPerturbationOrderThree tableau

/-- The two regularity cases distinguished by the source. The paper describes
but does not uniquely formalize "well behaved", so the tag is kept explicit. -/
inductive P18TauRegime where
  | wellBehaved
  | notWellBehaved
  deriving DecidableEq

/-- A norm-independent two-term interpretation of
`O(h^p) + O(epsilon h^m)` over the supplied asymptotic family. The hidden
constants are existential and the scheme and perturbation contributions stay
separate. -/
def p18UniformTwoTermGlobalOrder {ι : Type*}
    (error schemeError perturbationError step : ι → ℝ)
    (epsilon : ℝ) (p m : ℕ) : Prop :=
  (∀ t, error t = schemeError t + perturbationError t) ∧
    ∃ schemeConstant perturbationConstant : ℝ,
      0 ≤ schemeConstant ∧ 0 ≤ perturbationConstant ∧
        ∀ t,
          |schemeError t| ≤ schemeConstant * step t ^ p ∧
            |perturbationError t| ≤
              perturbationConstant * |epsilon| * step t ^ m

/-- One asymptotic family of stable Method 4s3pC executions. The local errors
are norms of actual additive Runge--Kutta one-step errors. Stability bounds
their accumulated global contributions by the sums of those local errors;
the final global orders are deliberately not fields of this structure. -/
structure P18StableMethod4s3pCBranch
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ι : Type*) (method : P18Method4s3pCSourceModel)
    (localPerturbationPower : ℕ) where
  tauRegime : P18TauRegime
  step : ι → ℝ
  epsilon : ℝ
  stepCount : ι → ℕ
  horizon : ℝ
  localSchemeConstant : ℝ
  localPerturbationConstant : ℝ
  stabilityConstant : ℝ
  step_nonneg : ∀ t, 0 ≤ step t
  epsilon_pos : 0 < epsilon
  step_count_pos : ∀ t, 0 < stepCount t
  horizon_nonneg : 0 ≤ horizon
  local_scheme_constant_nonneg : 0 ≤ localSchemeConstant
  local_perturbation_constant_nonneg : 0 ≤ localPerturbationConstant
  stability_constant_nonneg : 0 ≤ stabilityConstant
  F : State → State
  FEpsilon : State → State
  tau : State → State
  computedState : ∀ t, Fin (stepCount t + 1) → State
  exactState : ∀ t, Fin (stepCount t + 1) → State
  oneStep : ∀ t, Fin (stepCount t) →
    P18AdditiveRKOneStepRun State 4
  run_step : ∀ t j, (oneStep t j).step = step t
  run_epsilon : ∀ t j, (oneStep t j).epsilon = epsilon
  run_F : ∀ t j, (oneStep t j).F = F
  run_FEpsilon : ∀ t j, (oneStep t j).FEpsilon = FEpsilon
  run_tau : ∀ t j, (oneStep t j).tau = tau
  run_A : ∀ t j, (oneStep t j).a = method.tableau.A
  run_APerturbation : ∀ t j,
    (oneStep t j).aPerturbation = method.tableau.APerturbation
  run_b : ∀ t j, (oneStep t j).b = method.tableau.b
  run_bPerturbation : ∀ t j,
    (oneStep t j).bPerturbation = method.tableau.bPerturbation
  run_initial : ∀ t j,
    (oneStep t j).initial = computedState t j.castSucc
  run_perturbed_next : ∀ t j,
    (oneStep t j).perturbedNext = computedState t j.succ
  run_reference_next : ∀ t j,
    (oneStep t j).referenceNext = exactState t j.succ
  schemeLocalError : ∀ t, Fin (stepCount t) → ℝ
  perturbationLocalError : ∀ t, Fin (stepCount t) → ℝ
  scheme_local_error_eq : ∀ t j,
    schemeLocalError t j = ‖p18SchemeOneStepError (oneStep t j)‖
  perturbation_local_error_eq : ∀ t j,
    perturbationLocalError t j =
      ‖p18PerturbationOneStepError (oneStep t j)‖
  scheme_local_bound : ∀ t j,
    schemeLocalError t j ≤ localSchemeConstant * step t ^ 4
  perturbation_local_bound : ∀ t j,
    perturbationLocalError t j ≤
      localPerturbationConstant * |epsilon| *
        step t ^ localPerturbationPower
  globalSchemeError : ι → ℝ
  globalPerturbationError : ι → ℝ
  globalError : ι → ℝ
  global_error_eq : ∀ t,
    globalError t =
      ‖exactState t (Fin.last (stepCount t)) -
        computedState t (Fin.last (stepCount t))‖
  global_split : ∀ t,
    globalError t = globalSchemeError t + globalPerturbationError t
  stable_scheme_accumulation : ∀ t,
    |globalSchemeError t| ≤
      stabilityConstant * ∑ j, schemeLocalError t j
  stable_perturbation_accumulation : ∀ t,
    |globalPerturbationError t| ≤
      stabilityConstant * ∑ j, perturbationLocalError t j
  finite_time_horizon : ∀ t,
    (stepCount t : ℝ) * step t ≤ horizon

end HighamBench
```
