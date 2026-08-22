# Declaration dossier for P19-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t2_modular_gmres_forward_error
    {n : ℕ} (semantics : P19FirstOrderSemantics)
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family)
    (appendix : P19StaticAppendixATheory family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (P19Algorithm2Conditions (family.iteration k) →
        ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
          let q := appendix.rightQuantities k MR MRinv hMR
          p19FirstOrderLe semantics
            (p19ForwardError family.system.xExact
              (family.iteration k).xHat)
            ((family.iteration k).dimensionFactor *
              p19StaticXi MR MRinv q *
              p19ConditionNumberF
                (p19StaticSplitOperator family.system MRinv)
                (p19StaticSplitInverse family.system MR)))
```

## Elaborated target type

```lean
∀ {n : Nat} (semantics : HighamBench.P19FirstOrderSemantics) (family : HighamBench.P19Theorem31Family n semantics),
  HighamBench.P19MGSSelectionLaw family →
    ∀ (appendix : HighamBench.P19StaticAppendixATheory family),
      Exists fun k =>
        And (HighamBench.p19IterationWellConditioned (family.iteration k))
          (HighamBench.P19Algorithm2Conditions (family.iteration k) →
            ∀ (MR MRinv : HighamBench.P19Matrix n) (hMR : HighamBench.p19InversePair MR MRinv),
              have q := appendix.rightQuantities k MR MRinv hMR;
              HighamBench.p19FirstOrderLe semantics
                (HighamBench.p19ForwardError family.system.xExact (family.iteration k).xHat)
                (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor (HighamBench.p19StaticXi MR MRinv q))
                  (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                    (HighamBench.p19StaticSplitInverse family.system MR))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (semantics : HighamBench.P19FirstOrderSemantics) (family : HighamBench.P19Theorem31Family n semantics)
  (mgs : @HighamBench.P19MGSSelectionLaw n semantics family)
  (appendix : @HighamBench.P19StaticAppendixATheory n semantics family),
  @Exists.{1} (HighamBench.P19Theorem31Dimension n) fun (k : HighamBench.P19Theorem31Dimension n) =>
    And
      (@HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
        (@HighamBench.P19Theorem31Family.iteration n semantics family k))
      (@HighamBench.P19Algorithm2Conditions n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k) →
        ∀ (MR MRinv : HighamBench.P19Matrix n) (hMR : @HighamBench.p19InversePair n MR MRinv),
          have q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv :=
            @HighamBench.P19StaticAppendixATheory.rightQuantities n semantics family appendix k MR MRinv hMR;
          HighamBench.p19FirstOrderLe semantics
            (@HighamBench.p19ForwardError n
              (@HighamBench.P19Theorem31System.xExact n (@HighamBench.P19Theorem31Family.system n semantics family))
              (@HighamBench.P19Algorithm2Iteration.xHat n (@HighamBench.P19Theorem31Family.system n semantics family)
                semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                  (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                (@HighamBench.p19StaticXi n semantics family k MR MRinv q))
              (@HighamBench.p19ConditionNumberF n
                (@HighamBench.p19StaticSplitOperator n (@HighamBench.P19Theorem31Family.system n semantics family)
                  MRinv)
                (@HighamBench.p19StaticSplitInverse n (@HighamBench.P19Theorem31Family.system n semantics family) MR))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P19Algorithm2Conditions`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f3da5a71d70cb6862c8500b208a4f5a9a8679a38a6b7d68318ea1e5a3fa54eb0`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Prop
```

### D002: `HighamBench.P19Algorithm2Iteration.dimensionFactor`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bd61c8f1e579e2bc426d5a08c59735f265c1098959fb615dd750676b8f5f9f9`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.1
```

### D003: `HighamBench.P19Algorithm2Iteration.xHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0f616cd1d9ce48e6eb27c83d2c4a4c2df84dd67d173d645b05f7301f1c36da83`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.25
```

### D004: `HighamBench.P19FirstOrderSemantics`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a20664f9def445da45faf4e94b9d57628f2c92d716d878ab43853aebfc279a4f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D005: `HighamBench.P19MGSSelectionLaw`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b67e2d9f04acecbc78207a030a90d981c008234f8a4032f60100150823aba8a3`

Type:

```lean
{n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19Theorem31Family n semantics → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} → (family : HighamBench.P19Theorem31Family n semantics) → Prop
```

### D006: `HighamBench.P19Matrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `da34af64745188df680411658bb275d858795f5d4483f121fbd1b2751be7bd09`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D007: `HighamBench.P19StaticAppendixATheory`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f878ea97002c4b2194fa2f73c12e0f0c4b72630967712bbf65fa43c50ff031fa`

Type:

```lean
{n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19Theorem31Family n semantics → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} → (family : HighamBench.P19Theorem31Family n semantics) → Type
```

### D008: `HighamBench.P19StaticAppendixATheory.rightQuantities`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `79c3a6536a92b7a762cd0d7c31fc8459e7439753c676c7c63292a9e9c21108b1`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      HighamBench.P19StaticAppendixATheory family →
        (k : HighamBench.P19Theorem31Dimension n) →
          (MR MRinv : HighamBench.P19Matrix n) →
            HighamBench.p19InversePair MR MRinv → HighamBench.P19StaticRightQuantities family k MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (self : @HighamBench.P19StaticAppendixATheory n semantics family) →
        (k : HighamBench.P19Theorem31Dimension n) →
          (MR MRinv : HighamBench.P19Matrix n) →
            @HighamBench.p19InversePair n MR MRinv → @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.1
```

### D009: `HighamBench.P19StaticRightQuantities`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cdb178e57a28c2c5ee320fc7a43c465f7e981c77a239d21d1559d69277e7a564`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    HighamBench.P19Theorem31Family n semantics →
      HighamBench.P19Theorem31Dimension n → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) → (MR MRinv : HighamBench.P19Matrix n) → Type
```

### D010: `HighamBench.P19Theorem31Dimension`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ba4d761a25f81cfb346c892740752ac617f111a2ec0eef599d417bd7f7d3e658`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Subtype fun k => And (instLTNat.lt 0 k) (instLENat.le k n)
```

### D011: `HighamBench.P19Theorem31Family`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cc83d8798f9a47a79576057c89bdc261929f89427a25b80ab5445df3cd5f82a3`

Type:

```lean
Nat → HighamBench.P19FirstOrderSemantics → Type
```

Fully explicit type:

```lean
(n : Nat) → (semantics : HighamBench.P19FirstOrderSemantics) → Type
```

### D012: `HighamBench.P19Theorem31Family.basisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `48b8971fe31959b7c84e4fa154d6726a70bcbe3b6bc2717c09056064d86842e0`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) → HighamBench.P19Theorem31BasisFamily self.system
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      @HighamBench.P19Theorem31BasisFamily n (@HighamBench.P19Theorem31Family.system n semantics self)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D013: `HighamBench.P19Theorem31Family.iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `19b31c6eb7cb832d22efb7b1839ce0bc1843824506aa8009381c2a4b584f2da2`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        HighamBench.P19Algorithm2Iteration self.system semantics self.basisFamily k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        @HighamBench.P19Algorithm2Iteration n (@HighamBench.P19Theorem31Family.system n semantics self) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics self) k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D014: `HighamBench.P19Theorem31Family.system`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f9b5cc522a99882317f849e0f893e587ce7572ee9af8b6bcf8da993caceb2a83`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    HighamBench.P19Theorem31Family n semantics → HighamBench.P19Theorem31System n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) → HighamBench.P19Theorem31System n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D015: `HighamBench.P19Theorem31System.xExact`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c060fd2e6cb0459f8835569f03cacb0ab0a92b86296d51c2585bb7100236edd6`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D016: `HighamBench.p19ConditionNumberF`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0caab4531a1846f654c1dd00b274cf19ace9e44cbf1773a4d95f56800e9ffd1`

Type:

```lean
{n : Nat} → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : HighamBench.P19Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (HighamBench.p19FrobNorm Ainv) (HighamBench.p19FrobNorm A)
```

### D017: `HighamBench.p19FirstOrderLe`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `35e87ffbddb5973e07dcc90dac89a3894e57974b204159105b2394786a93ec95`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Real → Prop
```

Fully explicit type:

```lean
(semantics : HighamBench.P19FirstOrderSemantics) → (lhs rhs : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D018: `HighamBench.p19ForwardError`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `de704d15118aaa066da7b9d608fb5f38683c608a436633eec639f8da74709601`

Type:

```lean
{n : Nat} → HighamBench.P19Vector n → HighamBench.P19Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x xHat : HighamBench.P19Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (HighamBench.p19VecNorm2 (instHSub.hSub xHat x)) (HighamBench.p19VecNorm2 x)
```

### D019: `HighamBench.p19InversePair`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `77b8f45040142dc9a1f4c41dcad3fdb3c16d0ebc240adbaa5dac1c0ffabb00df`

Type:

```lean
{n : Nat} → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : HighamBench.P19Matrix n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv =>
  And (∀ (x : HighamBench.P19Vector n), Eq (HighamBench.p19MatVec Ainv (HighamBench.p19MatVec A x)) x)
    (∀ (x : HighamBench.P19Vector n), Eq (HighamBench.p19MatVec A (HighamBench.p19MatVec Ainv x)) x)
```

### D020: `HighamBench.p19IterationWellConditioned`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837ad167b07baa790538584ded0302c4a219440403d2a43dfcb0dfd365ded950`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  And (Real.instLE.le (instHDiv.hDiv 1 iteration.vHatSpectrum.sigmaMin) (4 / 3))
    (Real.instLE.le iteration.vHatSpectrum.sigmaMax (4 / 3))
```

### D021: `HighamBench.p19StaticSplitInverse`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4cb66673cf665323a02c7eb0c2c6dc429e9bd04200a6e3229334df0c1b9d3f4b`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → (MR : HighamBench.P19Matrix n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MR => HighamBench.p19SquareRectMul MR (HighamBench.p19SquareRectMul system.Ainv system.ML)
```

### D022: `HighamBench.p19StaticSplitOperator`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c25f2199e58a4a4de5edf313b6a5d571be22105c7937a8116262d0e4917f09a1`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → (MRinv : HighamBench.P19Matrix n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MRinv => HighamBench.p19SquareRectMul system.MLinv (HighamBench.p19SquareRectMul system.A MRinv)
```

### D023: `HighamBench.p19StaticXi`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f2bb3e83a46a0dfed93d2a90100870ec073df2ef99f0582cc00b88a6ba6e4ca8`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19StaticRightQuantities family k MR MRinv → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  have run := family.iteration k;
  HighamBench.p19ModularEnvelope (HighamBench.p19StaticAlpha MR MRinv q) (HighamBench.p19StaticBeta MR MRinv q)
    (HighamBench.p19StaticLambda family.system MR MRinv) run.epsilonC run.epsilonB run.ug run.epsilonX
```

### D024: `HighamBench.P19Algorithm2Conditions.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `255e05d9169cf68160ec75d831b67a6c01b7321d65c3244a232270c4e9a6a0f2`

Type:

```lean
∀ {n : Nat} {system : HighamBench.P19Theorem31System n} {semantics : HighamBench.P19FirstOrderSemantics}
  {basisFamily : HighamBench.P19Theorem31BasisFamily system} {k : HighamBench.P19Theorem31Dimension n}
  {iteration : HighamBench.P19Algorithm2Iteration system semantics basisFamily k},
  And (Real.instLE.le 0 iteration.epsilonC)
      (And (Real.instLE.le 0 iteration.epsilonB)
        (And (Real.instLE.le 0 iteration.ug) (Real.instLE.le 0 iteration.epsilonX))) →
    Real.instLE.le (HighamBench.p19FrobNorm iteration.deltaC)
        (instHMul.hMul iteration.epsilonC
          (HighamBench.p19FrobNorm (HighamBench.p19StaticExactC system (basisFamily.basis k.val)))) →
      Real.instLE.le (HighamBench.p19VecNorm2 iteration.deltaB)
          (instHMul.hMul iteration.epsilonB (HighamBench.p19VecNorm2 (HighamBench.p19StaticExactB system))) →
        HighamBench.p19IsLeastSquaresSolution (instHAdd.hAdd iteration.computedC iteration.leastSquaresDeltaC)
            (instHAdd.hAdd iteration.computedB iteration.leastSquaresDeltaB) iteration.yHat →
          (∀ (j : Fin (instHAdd.hAdd k.val 1)),
              Real.instLE.le
                (HighamBench.p19VecNorm2
                  (HighamBench.p19Column
                    (HighamBench.p19Augment iteration.leastSquaresDeltaB iteration.leastSquaresDeltaC) j))
                (instHMul.hMul (instHMul.hMul iteration.dimensionFactor iteration.ug)
                  (HighamBench.p19VecNorm2
                    (HighamBench.p19Column (HighamBench.p19Augment iteration.computedB iteration.computedC) j)))) →
            semantics.small
                (instHMul.hMul iteration.ug
                  (HighamBench.p19RectConditionF2 iteration.computedC iteration.computedCSpectrum.sigmaMin)) →
              semantics.small
                  (instHMul.hMul (instHAdd.hAdd (instHAdd.hAdd iteration.epsilonC iteration.epsilonB) iteration.ug)
                    (HighamBench.p19RectConditionF2 (HighamBench.p19StaticExactC system (basisFamily.basis k.val))
                      iteration.exactCSpectrum.sigmaMin)) →
                Real.instLE.le (HighamBench.p19VecNorm2 iteration.deltaX)
                    (instHMul.hMul iteration.epsilonX
                      (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec (basisFamily.basis k.val) iteration.yHat))) →
                  semantics.small iteration.epsilonX → HighamBench.P19Algorithm2Conditions iteration
```

Fully explicit type:

```lean
∀ {n : Nat} {system : HighamBench.P19Theorem31System n} {semantics : HighamBench.P19FirstOrderSemantics}
  {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} {k : HighamBench.P19Theorem31Dimension n}
  {iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k}
  (accuracy_nonneg :
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HighamBench.P19Algorithm2Iteration.epsilonC n system semantics basisFamily k iteration))
      (And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HighamBench.P19Algorithm2Iteration.epsilonB n system semantics basisFamily k iteration))
        (And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HighamBench.P19Algorithm2Iteration.ug n system semantics basisFamily k iteration))
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HighamBench.P19Algorithm2Iteration.epsilonX n system semantics basisFamily k iteration)))))
  (computation_error_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p19FrobNorm n
        (@Subtype.val.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          k)
        (@HighamBench.P19Algorithm2Iteration.deltaC n system semantics basisFamily k iteration))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.epsilonC n system semantics basisFamily k iteration)
        (@HighamBench.p19FrobNorm n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)
          (@HighamBench.p19StaticExactC n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            system
            (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k))))))
  (rhs_error_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p19VecNorm2 n
        (@HighamBench.P19Algorithm2Iteration.deltaB n system semantics basisFamily k iteration))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.epsilonB n system semantics basisFamily k iteration)
        (@HighamBench.p19VecNorm2 n (@HighamBench.p19StaticExactB n system))))
  (least_squares_solution :
    @HighamBench.p19IsLeastSquaresSolution n
      (@Subtype.val.{1} Nat
        (fun (k : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n))
        k)
      (@HAdd.hAdd.{0, 0, 0}
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (@instHAdd.{0}
          (HighamBench.P19RectMatrix n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k))
          (@Matrix.add.{0, 0, 0} (Fin n)
            (Fin
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k))
            Real Real.instAdd))
        (@HighamBench.P19Algorithm2Iteration.computedC n system semantics basisFamily k iteration)
        (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC n system semantics basisFamily k iteration))
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
        (@instHAdd.{0} (HighamBench.P19Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        (@HighamBench.P19Algorithm2Iteration.computedB n system semantics basisFamily k iteration)
        (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB n system semantics basisFamily k iteration))
      (@HighamBench.P19Algorithm2Iteration.yHat n system semantics basisFamily k iteration))
  (least_squares_column_bound :
    ∀
      (j :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @LE.le.{0} Real Real.instLE
        (@HighamBench.p19VecNorm2 n
          (@HighamBench.p19Column n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HighamBench.p19Augment n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB n system semantics basisFamily k iteration)
              (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC n system semantics basisFamily k iteration))
            j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.P19Algorithm2Iteration.dimensionFactor n system semantics basisFamily k iteration)
            (@HighamBench.P19Algorithm2Iteration.ug n system semantics basisFamily k iteration))
          (@HighamBench.p19VecNorm2 n
            (@HighamBench.p19Column n
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HighamBench.p19Augment n
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                (@HighamBench.P19Algorithm2Iteration.computedB n system semantics basisFamily k iteration)
                (@HighamBench.P19Algorithm2Iteration.computedC n system semantics basisFamily k iteration))
              j))))
  (computedC_numerically_nonsingular :
    HighamBench.P19FirstOrderSemantics.small semantics
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.ug n system semantics basisFamily k iteration)
        (@HighamBench.p19RectConditionF2 n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)
          (@HighamBench.P19Algorithm2Iteration.computedC n system semantics basisFamily k iteration)
          (@HighamBench.P19SingularValueData.sigmaMin n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@HighamBench.P19Algorithm2Iteration.computedC n system semantics basisFamily k iteration)
            (@HighamBench.P19Algorithm2Iteration.computedCSpectrum n system semantics basisFamily k iteration)))))
  (combined_model_small :
    HighamBench.P19FirstOrderSemantics.small semantics
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HighamBench.P19Algorithm2Iteration.epsilonC n system semantics basisFamily k iteration)
            (@HighamBench.P19Algorithm2Iteration.epsilonB n system semantics basisFamily k iteration))
          (@HighamBench.P19Algorithm2Iteration.ug n system semantics basisFamily k iteration))
        (@HighamBench.p19RectConditionF2 n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)
          (@HighamBench.p19StaticExactC n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            system
            (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)))
          (@HighamBench.P19SingularValueData.sigmaMin n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@HighamBench.p19StaticExactC n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              system
              (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)))
            (@HighamBench.P19Algorithm2Iteration.exactCSpectrum n system semantics basisFamily k iteration)))))
  (solution_error_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p19VecNorm2 n
        (@HighamBench.P19Algorithm2Iteration.deltaX n system semantics basisFamily k iteration))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.epsilonX n system semantics basisFamily k iteration)
        (@HighamBench.p19VecNorm2 n
          (@HighamBench.p19RectMatVec n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k))
            (@HighamBench.P19Algorithm2Iteration.yHat n system semantics basisFamily k iteration)))))
  (solution_small :
    HighamBench.P19FirstOrderSemantics.small semantics
      (@HighamBench.P19Algorithm2Iteration.epsilonX n system semantics basisFamily k iteration)),
  @HighamBench.P19Algorithm2Conditions n system semantics basisFamily k iteration
```

### D025: `HighamBench.P19Algorithm2Iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f4879bef746a587dacfe91ab1a424bce7078d52c23f5781d3d8d85d64b2e912e`

Type:

```lean
{n : Nat} →
  (system : HighamBench.P19Theorem31System n) →
    HighamBench.P19FirstOrderSemantics →
      HighamBench.P19Theorem31BasisFamily system → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (system : HighamBench.P19Theorem31System n) →
    (semantics : HighamBench.P19FirstOrderSemantics) →
      (basisFamily : @HighamBench.P19Theorem31BasisFamily n system) → (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D026: `HighamBench.P19Algorithm2Iteration.epsilonB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f8030bfc92643eceb346f953d6858c99670b9bac33003239e0d7a3301ae7fe23`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.4
```

### D027: `HighamBench.P19Algorithm2Iteration.epsilonC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fbab99a9750c59d1a1e583743df520e7d44c5cc91bb8f953dd579b781c71de46`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.3
```

### D028: `HighamBench.P19Algorithm2Iteration.epsilonX`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f7561b0267689d981281ecd75c09df38fe7833e3c39fc79174e4f25762311905`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.6
```

### D029: `HighamBench.P19Algorithm2Iteration.ug`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4719f7a83a03368282078d24f181cee29a7a4a469c3c34d7ae10554be584afb9`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.5
```

### D030: `HighamBench.P19Algorithm2Iteration.vHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e8833827bd3a748534cb2317f9f1b570eb9df72748910ae72b2f34cd8d63c4a3`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.13
```

### D031: `HighamBench.P19Algorithm2Iteration.vHatSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6c6a21a70e9a127eec34be18a02b5156e7c6fd3553d869f8a57f86ef151cbc57`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : HighamBench.P19Algorithm2Iteration system semantics basisFamily k) →
            HighamBench.P19SingularValueData self.vHat
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            @HighamBench.P19SingularValueData n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.P19Algorithm2Iteration.vHat n system semantics basisFamily k self)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.28
```

### D032: `HighamBench.P19FirstOrderSemantics.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a249dfd13648ccda052f87210f4319154f5c284c54962efd48e215532eae0d6b`

Type:

```lean
(Real → Prop) → (secondOrder : Real → Prop) → secondOrder 0 → HighamBench.P19FirstOrderSemantics
```

Fully explicit type:

```lean
(small secondOrder : Real → Prop) →
  (zero_secondOrder : secondOrder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    HighamBench.P19FirstOrderSemantics
```

### D033: `HighamBench.P19FirstOrderSemantics.secondOrder`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ddf671e3d58393ee511310b987314be908539f15467ae3cf73e66807e455755c`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P19FirstOrderSemantics) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D034: `HighamBench.P19MGSSelectionLaw.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1497d719068f8d8895ba60bd603e9d3c8c9016560b59759954bd461a979d201f`

Type:

```lean
∀ {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics} {family : HighamBench.P19Theorem31Family n semantics},
  HighamBench.p19IterationWellConditioned (family.iteration ⟨1, ⋯⟩) →
    (∀ (k : Nat) (hkpos : instLTNat.lt 0 k) (hklt : instLTNat.lt k n),
        let current := ⟨k, ⋯⟩;
        let next := ⟨instHAdd.hAdd k 1, ⋯⟩;
        Not (HighamBench.p19IterationWellConditioned (family.iteration next)) →
          HighamBench.p19MGSNearDependence (family.iteration current)) →
      HighamBench.P19MGSSelectionLaw family
```

Fully explicit type:

```lean
∀ {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics} {family : HighamBench.P19Theorem31Family n semantics}
  (first_dimension_good :
    @HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
      (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
      (@Subtype.mk.{1} Nat
        (fun (k : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@And.intro
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) Nat.zero_lt_one
          (@HighamBench.P19Theorem31System.dimension_pos n
            (@HighamBench.P19Theorem31Family.system n semantics family))))
      (@HighamBench.P19Theorem31Family.iteration n semantics family
        (@Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@And.intro
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) Nat.zero_lt_one
            (@HighamBench.P19Theorem31System.dimension_pos n
              (@HighamBench.P19Theorem31Family.system n semantics family))))))
  (loss_implies_near_dependence :
    ∀ (k : Nat) (hkpos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
      (hklt : @LT.lt.{0} Nat instLTNat k n),
      let current : HighamBench.P19Theorem31Dimension n :=
        @Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          k
          (@And.intro (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n) hkpos (@Nat.le_of_lt k n hklt));
      let next : HighamBench.P19Theorem31Dimension n :=
        @Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@And.intro
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              n)
            (Nat.succ_pos k)
            (@Iff.mpr (@LE.le.{0} Nat instLENat (Nat.succ k) n) (@LT.lt.{0} Nat instLTNat k n) (@Nat.succ_le_iff k n)
              hklt));
      Not
          (@HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family)
            semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) next
            (@HighamBench.P19Theorem31Family.iteration n semantics family next)) →
        @HighamBench.p19MGSNearDependence n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) current
          (@HighamBench.P19Theorem31Family.iteration n semantics family current)),
  @HighamBench.P19MGSSelectionLaw n semantics family
```

### D035: `HighamBench.P19SingularValueData.sigmaMax`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `39b1024085d127c92aa430d39d98d3d00a99a5d1c44ea3bcaff897aa19328ba4`

Type:

```lean
{m k : Nat} → {A : HighamBench.P19RectMatrix m k} → HighamBench.P19SingularValueData A → Real
```

Fully explicit type:

```lean
{m k : Nat} → {A : HighamBench.P19RectMatrix m k} → (self : @HighamBench.P19SingularValueData m k A) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.2
```

### D036: `HighamBench.P19SingularValueData.sigmaMin`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1013716a93aaa4244e940de911b2c7afefa568b957b54095b8426864b032c52c`

Type:

```lean
{m k : Nat} → {A : HighamBench.P19RectMatrix m k} → HighamBench.P19SingularValueData A → Real
```

Fully explicit type:

```lean
{m k : Nat} → {A : HighamBench.P19RectMatrix m k} → (self : @HighamBench.P19SingularValueData m k A) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.1
```

### D037: `HighamBench.P19StaticAppendixATheory.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0b99057edf7eba18d77a5822550ccb3122e66f1ce382e968b86ae4de5c4dcaf6`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (rightQuantities :
          (k : HighamBench.P19Theorem31Dimension n) →
            (MR MRinv : HighamBench.P19Matrix n) →
              HighamBench.p19InversePair MR MRinv → HighamBench.P19StaticRightQuantities family k MR MRinv) →
        ((k : HighamBench.P19Theorem31Dimension n) →
            HighamBench.p19IterationWellConditioned (family.iteration k) →
              Or (Eq k.val n) (HighamBench.p19MGSNearDependence (family.iteration k)) →
                HighamBench.P19Algorithm2Conditions (family.iteration k) →
                  (MR MRinv : HighamBench.P19Matrix n) →
                    (hMR : HighamBench.p19InversePair MR MRinv) →
                      HighamBench.P19StaticAppendixAExpansion family k MR MRinv (rightQuantities k MR MRinv hMR)) →
          HighamBench.P19StaticAppendixATheory family
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (rightQuantities :
          (k : HighamBench.P19Theorem31Dimension n) →
            (MR MRinv : HighamBench.P19Matrix n) →
              @HighamBench.p19InversePair n MR MRinv →
                @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) →
        (expansion :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family)
                  semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                  (@HighamBench.P19Theorem31Family.iteration n semantics family k) →
                Or
                    (@Eq.{1} Nat
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      n)
                    (@HighamBench.p19MGSNearDependence n (@HighamBench.P19Theorem31Family.system n semantics family)
                      semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                      (@HighamBench.P19Theorem31Family.iteration n semantics family k)) →
                  @HighamBench.P19Algorithm2Conditions n (@HighamBench.P19Theorem31Family.system n semantics family)
                      semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                      (@HighamBench.P19Theorem31Family.iteration n semantics family k) →
                    (MR MRinv : HighamBench.P19Matrix n) →
                      (hMR : @HighamBench.p19InversePair n MR MRinv) →
                        @HighamBench.P19StaticAppendixAExpansion n semantics family k MR MRinv
                          (rightQuantities k MR MRinv hMR)) →
          @HighamBench.P19StaticAppendixATheory n semantics family
```

### D038: `HighamBench.P19StaticRightQuantities.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `54b2fb2699fdda10cec4cd98026ef5d71f8ac18d3e70b55e827d0943bb0eb135`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (mrzSpectrum :
              HighamBench.P19SingularValueData (HighamBench.p19SquareRectMul MR (family.basisFamily.basis k.val))) →
            Real.instLT.lt 0 mrzSpectrum.sigmaMin →
              Real.instLT.lt 0
                  (HighamBench.p19FrobNorm
                    (HighamBench.p19StaticExactC family.system (family.basisFamily.basis k.val))) →
                Real.instLT.lt 0 (HighamBench.p19FrobNorm (HighamBench.p19StaticSplitOperator family.system MRinv)) →
                  Real.instLT.lt 0 (HighamBench.p19ConditionNumberF MR MRinv) →
                    Real.instLT.lt 0
                        (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                          (HighamBench.p19StaticSplitInverse family.system MR)) →
                      HighamBench.P19StaticRightQuantities family k MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (mrzSpectrum :
              @HighamBench.P19SingularValueData n
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                (@HighamBench.p19SquareRectMul n
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)
                  MR
                  (@HighamBench.P19Theorem31BasisFamily.basis n
                    (@HighamBench.P19Theorem31Family.system n semantics family)
                    (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                          (@LE.le.{0} Nat instLENat k n))
                      k)))) →
            (mrz_sigmaMin_pos :
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@HighamBench.P19SingularValueData.sigmaMin n
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                          (@LE.le.{0} Nat instLENat k n))
                      k)
                    (@HighamBench.p19SquareRectMul n
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      MR
                      (@HighamBench.P19Theorem31BasisFamily.basis n
                        (@HighamBench.P19Theorem31Family.system n semantics family)
                        (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            And
                              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                              (@LE.le.{0} Nat instLENat k n))
                          k)))
                    mrzSpectrum)) →
              (exactC_norm_pos :
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@HighamBench.p19FrobNorm n
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      (@HighamBench.p19StaticExactC n
                        (@Subtype.val.{1} Nat
                          (fun (k : Nat) =>
                            And
                              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                              (@LE.le.{0} Nat instLENat k n))
                          k)
                        (@HighamBench.P19Theorem31Family.system n semantics family)
                        (@HighamBench.P19Theorem31BasisFamily.basis n
                          (@HighamBench.P19Theorem31Family.system n semantics family)
                          (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))))) →
                (split_operator_norm_pos :
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HighamBench.p19FrobNorm n n
                        (@HighamBench.p19StaticSplitOperator n
                          (@HighamBench.P19Theorem31Family.system n semantics family) MRinv))) →
                  (mr_condition_pos :
                      @LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        (@HighamBench.p19ConditionNumberF n MR MRinv)) →
                    (split_condition_pos :
                        @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (@HighamBench.p19ConditionNumberF n
                            (@HighamBench.p19StaticSplitOperator n
                              (@HighamBench.P19Theorem31Family.system n semantics family) MRinv)
                            (@HighamBench.p19StaticSplitInverse n
                              (@HighamBench.P19Theorem31Family.system n semantics family) MR))) →
                      @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv
```

### D039: `HighamBench.P19Theorem31BasisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cd7346b530ce5e5d6ba1c2e5416ee7c43d715dd345875961bcce92cbe5f41e14`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → Type
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → Type
```

### D040: `HighamBench.P19Theorem31Family.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f076c552518a53410edcb7f11b49475fb90d812b0212bc30431c42bf011d836`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (system : HighamBench.P19Theorem31System n) →
      (basisFamily : HighamBench.P19Theorem31BasisFamily system) →
        ((k : HighamBench.P19Theorem31Dimension n) →
            HighamBench.P19Algorithm2Iteration system semantics basisFamily k) →
          HighamBench.P19Theorem31Family n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (system : HighamBench.P19Theorem31System n) →
      (basisFamily : @HighamBench.P19Theorem31BasisFamily n system) →
        (iteration :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
          HighamBench.P19Theorem31Family n semantics
```

### D041: `HighamBench.P19Theorem31System`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1fc353b1b432c0c1ef430f4cf2ff9afcfbed92f49cf465d778ddda0a635dd4d`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D042: `HighamBench.P19Theorem31System.A`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4bfdf1aea21b236835dd2c7582c4c22271b794da188a0ba1ccc5a694afff4be4`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D043: `HighamBench.P19Theorem31System.Ainv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5af7fc516b339d9009da5411f78f824a75063e508c6084b47f8ef7e44f62db8e`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D044: `HighamBench.P19Theorem31System.ML`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `49bf2034c91342a98820db7017c34f0a2e9d1c3aaff5c66811d036bd3b1a1dcf`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D045: `HighamBench.P19Theorem31System.MLinv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ef0cd4e713f0114adf6c09b9205814f09e9a4779fd1ba97cdfa6d00458ff172c`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D046: `HighamBench.P19Vector`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f1f6f4466f0d4de5052934629682ac38b1dc670a54dad0a303f7ed04448984d9`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D047: `HighamBench.p19FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1d77e739886fafe42f3444123b92bfd0ee9c522738b34d29764b9a10cb431f73`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Real
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D048: `HighamBench.p19IterationWellConditioned._proof_1`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e36ed6bfde9948e287453e8e216377bb07ab71b2d92789cf0f62d8ac7d27adbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D049: `HighamBench.p19IterationWellConditioned._proof_2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `a53f13b94d3dbfd1b78203ce451bfa60bbd01b058daa3f65ff6c7d30ec55b8bd`

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

### D050: `HighamBench.p19MatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1ae9d14b7b4a526e86a7616a8ca6e9f01f9c771fcb8636b83a7aee0f1c7547c1`

Type:

```lean
{n : Nat} → HighamBench.P19Matrix n → HighamBench.P19Vector n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P19Matrix n) → (x : HighamBench.P19Vector n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D051: `HighamBench.p19ModularEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4d1f50569f1e938522ad9eb1ae93404d40243c6ec09407ff5120e6b1032a551c`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
(alpha beta lambda epsilonC epsilonB ug epsilonX : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun alpha beta lambda epsilonC epsilonB ug epsilonX =>
  instHAdd.hAdd
    (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul alpha epsilonC) (instHMul.hMul beta epsilonB)) (instHMul.hMul beta ug))
    (instHMul.hMul lambda epsilonX)
```

### D052: `HighamBench.p19SquareRectMul`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2b8444b51bdd6b2f43ba4d5ab8376e63a1788f241ad49a66ee55d945464e1769`

Type:

```lean
{n k : Nat} → HighamBench.P19Matrix n → HighamBench.P19RectMatrix n k → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n k : Nat} → (A : HighamBench.P19Matrix n) → (B : HighamBench.P19RectMatrix n k) → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D053: `HighamBench.p19StaticAlpha`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `94ad6765fd2d1d76a7cf6f5e694fe696559cc294ae4aa2092584da7318d86f0e`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19StaticRightQuantities family k MR MRinv → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  instHMul.hMul (instHDiv.hDiv (HighamBench.p19ConditionNumberF MR MRinv) q.mrzSpectrum.sigmaMin)
    (instHDiv.hDiv
      (HighamBench.p19FrobNorm (HighamBench.p19StaticExactC family.system (family.basisFamily.basis k.val)))
      (HighamBench.p19FrobNorm (HighamBench.p19StaticSplitOperator family.system MRinv)))
```

### D054: `HighamBench.p19StaticBeta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc6616164dde51b36dde0851bbe04442ce448feaf37560cbf0eb1c080b14ab56`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19StaticRightQuantities family k MR MRinv → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  instHMul.hMul
    (Real.instMax.max 1
      (instHDiv.hDiv
        (instHDiv.hDiv
          (HighamBench.p19FrobNorm (HighamBench.p19StaticExactC family.system (family.basisFamily.basis k.val)))
          (HighamBench.p19FrobNorm (HighamBench.p19StaticSplitOperator family.system MRinv)))
        q.mrzSpectrum.sigmaMin))
    (HighamBench.p19ConditionNumberF MR MRinv)
```

### D055: `HighamBench.p19StaticLambda`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ef76c331af6971ea383a0e720b65e84633e2cc7d764624ac05082af69c1970f0`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → (MR MRinv : HighamBench.P19Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MR MRinv =>
  instHDiv.hDiv 1
    (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator system MRinv)
      (HighamBench.p19StaticSplitInverse system MR))
```

### D056: `HighamBench.p19VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6b6e1bd375429f5aeb20a6f7108df37b3e72d1ec77d5e9de9ed7b15b6a12565e`

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
fun {n} x => (HighamBench.p19VecNorm2Sq x).sqrt
```

### D057: `HighamBench.P19Algorithm2Iteration.computedB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0a36228ab177e3d96350f260b42b0b39cdbb2e3af19df1b61a4bdbe4767eb7c1`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.10
```

### D058: `HighamBench.P19Algorithm2Iteration.computedC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `50a6535dd8ce1360428870bf95756a470737cd826b008cdbfad61b0808d02dee`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.7
```

### D059: `HighamBench.P19Algorithm2Iteration.computedCSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7824e63acaf19271f33d66772ca09d12cc7c9a38fa97405a605ee999bc4894e9`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : HighamBench.P19Algorithm2Iteration system semantics basisFamily k) →
            HighamBench.P19SingularValueData self.computedC
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            @HighamBench.P19SingularValueData n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.P19Algorithm2Iteration.computedC n system semantics basisFamily k self)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.23
```

### D060: `HighamBench.P19Algorithm2Iteration.deltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `737380e55e6f4d002c09906b6bcf025c9bda8e34cbadd9e15e1eacd15618ad5b`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.11
```

### D061: `HighamBench.P19Algorithm2Iteration.deltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8b975d7f99cb27792acfddfe57d6c62419fd06a5e22f149738ab976b8c92053c`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.8
```

### D062: `HighamBench.P19Algorithm2Iteration.deltaX`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c769c6055e58ce13a82154d73aaa12e36f093be38b8a1ef2590884646050568e`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.26
```

### D063: `HighamBench.P19Algorithm2Iteration.exactCSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `68907e28bc6082835e07880ef0723e3331dc590838e9ae56902d97687d8e0975`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k →
            HighamBench.P19SingularValueData (HighamBench.p19StaticExactC system (basisFamily.basis k.val))
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            @HighamBench.P19SingularValueData n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.p19StaticExactC n
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                system
                (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)))
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.24
```

### D064: `HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `09771da30686fc5e2cf381c4665caae33df2500d4d8fef9e37d1cf8a4130281b`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.20
```

### D065: `HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1474e23e024f85a3713cc0794a6573e2e4071d9d614f92fe14145947ab293054`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.21
```

### D066: `HighamBench.P19Algorithm2Iteration.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7878f8fc84c9629c27889bbc10be4df2f10323a0af9ee7131d71f631b0264ce2`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (dimensionFactor : Real) →
            Real.instLE.le 1 dimensionFactor →
              Real →
                Real →
                  Real →
                    Real →
                      (computedC deltaC : HighamBench.P19RectMatrix n k.val) →
                        Eq computedC
                            (instHAdd.hAdd (HighamBench.p19StaticExactC system (basisFamily.basis k.val)) deltaC) →
                          (computedB deltaB : HighamBench.P19Vector n) →
                            Eq computedB (instHAdd.hAdd (HighamBench.p19StaticExactB system) deltaB) →
                              (vHat : HighamBench.P19RectMatrix n k.val) →
                                (vHatNext : HighamBench.P19RectMatrix n (instHAdd.hAdd k.val 1)) →
                                  (beta : Real) →
                                    (hessenberg : HighamBench.P19RectMatrix (instHAdd.hAdd k.val 1) k.val) →
                                      HighamBench.p19IsUpperHessenberg hessenberg →
                                        Eq (HighamBench.p19Augment computedB computedC)
                                            (HighamBench.p19RectMatMul vHatNext
                                              (HighamBench.p19Augment (HighamBench.p19ScaledFirstBasisVector beta)
                                                hessenberg)) →
                                          (∀ (i : Fin n) (j : Fin k.val), Eq (vHat i j) (vHatNext i j.castSucc)) →
                                            HighamBench.P19Vector n →
                                              HighamBench.P19RectMatrix n k.val →
                                                (yHat : HighamBench.P19Vector k.val) →
                                                  HighamBench.P19SingularValueData computedC →
                                                    HighamBench.P19SingularValueData
                                                        (HighamBench.p19StaticExactC system (basisFamily.basis k.val)) →
                                                      (xHat deltaX : HighamBench.P19Vector n) →
                                                        Eq xHat
                                                            (instHAdd.hAdd
                                                              (HighamBench.p19RectMatVec (basisFamily.basis k.val) yHat)
                                                              deltaX) →
                                                          HighamBench.P19SingularValueData vHat →
                                                            HighamBench.P19Algorithm2Iteration system semantics
                                                              basisFamily k
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (dimensionFactor : Real) →
            (dimensionFactor_one_le :
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  dimensionFactor) →
              (epsilonC epsilonB ug epsilonX : Real) →
                (computedC deltaC :
                    HighamBench.P19RectMatrix n
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)) →
                  (computation_equation :
                      @Eq.{1}
                        (HighamBench.P19RectMatrix n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))
                        computedC
                        (@HAdd.hAdd.{0, 0, 0}
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (@instHAdd.{0}
                            (HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            (@Matrix.add.{0, 0, 0} (Fin n)
                              (Fin
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k))
                              Real Real.instAdd))
                          (@HighamBench.p19StaticExactC n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k)
                            system
                            (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)))
                          deltaC)) →
                    (computedB deltaB : HighamBench.P19Vector n) →
                      (rhs_equation :
                          @Eq.{1} (HighamBench.P19Vector n) computedB
                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                              (HighamBench.P19Vector n)
                              (@instHAdd.{0} (HighamBench.P19Vector n)
                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                              (@HighamBench.p19StaticExactB n system) deltaB)) →
                        (vHat :
                            HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)) →
                          (vHatNext :
                              HighamBench.P19RectMatrix n
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            (beta : Real) →
                              (hessenberg :
                                  HighamBench.P19RectMatrix
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@Subtype.val.{1} Nat
                                      (fun (k : Nat) =>
                                        And
                                          (@LT.lt.{0} Nat instLTNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                          (@LE.le.{0} Nat instLENat k n))
                                      k)) →
                                (hessenberg_upper :
                                    @HighamBench.p19IsUpperHessenberg
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k)
                                      hessenberg) →
                                  (mgs_givens_relation :
                                      @Eq.{1}
                                        (HighamBench.P19RectMatrix n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@HighamBench.p19Augment n
                                          (@Subtype.val.{1} Nat
                                            (fun (k : Nat) =>
                                              And
                                                (@LT.lt.{0} Nat instLTNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                (@LE.le.{0} Nat instLENat k n))
                                            k)
                                          computedB computedC)
                                        (@HighamBench.p19RectMatMul n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          vHatNext
                                          (@HighamBench.p19Augment
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@HighamBench.p19ScaledFirstBasisVector
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)
                                              beta)
                                            hessenberg))) →
                                    (vHat_prefix :
                                        ∀ (i : Fin n)
                                          (j :
                                            Fin
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)),
                                          @Eq.{1} Real (vHat i j)
                                            (vHatNext i
                                              (@Fin.castSucc
                                                (@Subtype.val.{1} Nat
                                                  (fun (k : Nat) =>
                                                    And
                                                      (@LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                      (@LE.le.{0} Nat instLENat k n))
                                                  k)
                                                j))) →
                                      (leastSquaresDeltaB : HighamBench.P19Vector n) →
                                        (leastSquaresDeltaC :
                                            HighamBench.P19RectMatrix n
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)) →
                                          (yHat :
                                              HighamBench.P19Vector
                                                (@Subtype.val.{1} Nat
                                                  (fun (k : Nat) =>
                                                    And
                                                      (@LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                      (@LE.le.{0} Nat instLENat k n))
                                                  k)) →
                                            (computedCSpectrum :
                                                @HighamBench.P19SingularValueData n
                                                  (@Subtype.val.{1} Nat
                                                    (fun (k : Nat) =>
                                                      And
                                                        (@LT.lt.{0} Nat instLTNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                          k)
                                                        (@LE.le.{0} Nat instLENat k n))
                                                    k)
                                                  computedC) →
                                              (exactCSpectrum :
                                                  @HighamBench.P19SingularValueData n
                                                    (@Subtype.val.{1} Nat
                                                      (fun (k : Nat) =>
                                                        And
                                                          (@LT.lt.{0} Nat instLTNat
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                              (instOfNatNat (nat_lit 0)))
                                                            k)
                                                          (@LE.le.{0} Nat instLENat k n))
                                                      k)
                                                    (@HighamBench.p19StaticExactC n
                                                      (@Subtype.val.{1} Nat
                                                        (fun (k : Nat) =>
                                                          And
                                                            (@LT.lt.{0} Nat instLTNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                (instOfNatNat (nat_lit 0)))
                                                              k)
                                                            (@LE.le.{0} Nat instLENat k n))
                                                        k)
                                                      system
                                                      (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                                                        (@Subtype.val.{1} Nat
                                                          (fun (k : Nat) =>
                                                            And
                                                              (@LT.lt.{0} Nat instLTNat
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                  (instOfNatNat (nat_lit 0)))
                                                                k)
                                                              (@LE.le.{0} Nat instLENat k n))
                                                          k)))) →
                                                (xHat deltaX : HighamBench.P19Vector n) →
                                                  (solution_equation :
                                                      @Eq.{1} (HighamBench.P19Vector n) xHat
                                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                          (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                          (@instHAdd.{0} (HighamBench.P19Vector n)
                                                            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                              fun (i : Fin n) => Real.instAdd))
                                                          (@HighamBench.p19RectMatVec n
                                                            (@Subtype.val.{1} Nat
                                                              (fun (k : Nat) =>
                                                                And
                                                                  (@LT.lt.{0} Nat instLTNat
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                      (instOfNatNat (nat_lit 0)))
                                                                    k)
                                                                  (@LE.le.{0} Nat instLENat k n))
                                                              k)
                                                            (@HighamBench.P19Theorem31BasisFamily.basis n system
                                                              basisFamily
                                                              (@Subtype.val.{1} Nat
                                                                (fun (k : Nat) =>
                                                                  And
                                                                    (@LT.lt.{0} Nat instLTNat
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                        (instOfNatNat (nat_lit 0)))
                                                                      k)
                                                                    (@LE.le.{0} Nat instLENat k n))
                                                                k))
                                                            yHat)
                                                          deltaX)) →
                                                    (vHatSpectrum :
                                                        @HighamBench.P19SingularValueData n
                                                          (@Subtype.val.{1} Nat
                                                            (fun (k : Nat) =>
                                                              And
                                                                (@LT.lt.{0} Nat instLTNat
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                    (instOfNatNat (nat_lit 0)))
                                                                  k)
                                                                (@LE.le.{0} Nat instLENat k n))
                                                            k)
                                                          vHat) →
                                                      @HighamBench.P19Algorithm2Iteration n system semantics basisFamily
                                                        k
```

### D067: `HighamBench.P19Algorithm2Iteration.yHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `17f32ecc0179dc60da4f31e7911e5c48e15e77ecc3d4689d7406db80def04525`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19Vector
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.22
```

### D068: `HighamBench.P19FirstOrderSemantics.small`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1bc30297c5d6628f7a45cd5221fd0209542b9615afa5f93728f12b0e31dc32b5`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P19FirstOrderSemantics) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D069: `HighamBench.P19RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `439dd553c0545a1da7e92aa2fe36a24aa581a6f27bc01f3f2b81504fea271a29`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(m k : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D070: `HighamBench.P19SingularValueData`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Type
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → Type
```

### D071: `HighamBench.P19StaticAppendixAExpansion`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `65eed1fd067dfb3e5a580791ed563e989356533e3bad89d99fd5a0ade6de3581`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19StaticRightQuantities family k MR MRinv → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) → Type
```

### D072: `HighamBench.P19StaticRightQuantities.mrzSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4eb7527f6531dcb13870aa8043a1b097765583fdd88a79a19aa96217957c326c`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          HighamBench.P19StaticRightQuantities family k MR MRinv →
            HighamBench.P19SingularValueData (HighamBench.p19SquareRectMul MR (family.basisFamily.basis k.val))
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (self : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv) →
            @HighamBench.P19SingularValueData n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.p19SquareRectMul n
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                MR
                (@HighamBench.P19Theorem31BasisFamily.basis n
                  (@HighamBench.P19Theorem31Family.system n semantics family)
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)))
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family k MR MRinv self => self.1
```

### D073: `HighamBench.P19Theorem31BasisFamily.basis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e068250f38486d591a2adfb1d7f2c918bc70608277fca9f7321223a7e5e37cbb`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    HighamBench.P19Theorem31BasisFamily system → (k : Nat) → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (self : @HighamBench.P19Theorem31BasisFamily n system) → (k : Nat) → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun n system self => self.1
```

### D074: `HighamBench.P19Theorem31BasisFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `436dbb701a39337ce5332902d90e6973e9b3a19d7776ff8eb60c5b47e5d23e93`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (basis : (k : Nat) → HighamBench.P19RectMatrix n k) →
      (∀ (k : Nat), instLTNat.lt 0 k → instLENat.le k n → HighamBench.p19FullColumnRank (basis k)) →
        (∀ (k : Nat),
            instLTNat.lt k n → ∀ (i : Fin n) (j : Fin k), Eq (basis k i j) (basis (instHAdd.hAdd k 1) i j.castSucc)) →
          HighamBench.P19Theorem31BasisFamily system
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (basis : (k : Nat) → HighamBench.P19RectMatrix n k) →
      (full_rank :
          ∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
              @LE.le.{0} Nat instLENat k n → @HighamBench.p19FullColumnRank n k (basis k)) →
        (column_prefix :
            ∀ (k : Nat),
              @LT.lt.{0} Nat instLTNat k n →
                ∀ (i : Fin n) (j : Fin k),
                  @Eq.{1} Real (basis k i j)
                    (basis
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      i (@Fin.castSucc k j))) →
          @HighamBench.P19Theorem31BasisFamily n system
```

### D075: `HighamBench.P19Theorem31System.dimension_pos`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7bcc8692a7674f34e3a15ff70ef2f751cd9c1fac7daae1fce18d92dbba9eb545`

Type:

```lean
∀ {n : Nat} (self : HighamBench.P19Theorem31System n), instLTNat.lt 0 n
```

Fully explicit type:

```lean
∀ {n : Nat} (self : HighamBench.P19Theorem31System n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n
```

### D076: `HighamBench.P19Theorem31System.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b6ce3331a8ec6712c83ccceaf2dca3a6a89ee6e003288845219a21bd32c3a9a7`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv ML MLinv : HighamBench.P19Matrix n) →
      (b xExact : HighamBench.P19Vector n) →
        HighamBench.p19InversePair A Ainv →
          HighamBench.p19InversePair ML MLinv →
            Ne b 0 → Eq (HighamBench.p19MatVec A xExact) b → HighamBench.P19Theorem31System n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (A Ainv ML MLinv : HighamBench.P19Matrix n) →
      (b xExact : HighamBench.P19Vector n) →
        (A_inverse : @HighamBench.p19InversePair n A Ainv) →
          (ML_inverse : @HighamBench.p19InversePair n ML MLinv) →
            (b_nonzero :
                @Ne.{1} (HighamBench.P19Vector n) b
                  (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                      (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero)))) →
              (exact_solution : @Eq.{1} (HighamBench.P19Vector n) (@HighamBench.p19MatVec n A xExact) b) →
                HighamBench.P19Theorem31System n
```

### D077: `HighamBench.p19Augment`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2fe0e06752730d60394b59adb4b76c6f22ea6681023a70406cbdcfc4ba900101`

Type:

```lean
{n k : Nat} → HighamBench.P19Vector n → HighamBench.P19RectMatrix n k → HighamBench.P19RectMatrix n (instHAdd.hAdd k 1)
```

Fully explicit type:

```lean
{n k : Nat} →
  (b : HighamBench.P19Vector n) →
    (C : HighamBench.P19RectMatrix n k) →
      HighamBench.P19RectMatrix n
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b C i i_1 => Fin.cases (b i) (fun j => C i j) i_1
```

### D078: `HighamBench.p19Column`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d1c96c67d25102fa9368afc8215a13cc0626a5b92b4ea3b4e4f9c82429d0c977`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Fin k → HighamBench.P19Vector m
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (j : Fin k) → HighamBench.P19Vector m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A j i => A i j
```

### D079: `HighamBench.p19IsLeastSquaresSolution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3007f611ab5087af1f0566bf60dfd75fc71f78dad5e293cff7cd63de4c42ed91`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → HighamBench.P19Vector m → HighamBench.P19Vector k → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (b : HighamBench.P19Vector m) → (y : HighamBench.P19Vector k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : HighamBench.P19Vector k),
    Real.instLE.le (HighamBench.p19VecNorm2 (instHSub.hSub b (HighamBench.p19RectMatVec A y)))
      (HighamBench.p19VecNorm2 (instHSub.hSub b (HighamBench.p19RectMatVec A z)))
```

### D080: `HighamBench.p19MGSNearDependence`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `bebe1d1e8d8d001aa18eb0792f2f6a1ee4a0fc6ffe41d08bf7c18d43bb054680`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  ∀ (phi : Real),
    Real.instLT.lt 0 phi →
      HighamBench.p19NearRankDeficient
        (HighamBench.p19Augment (fun i => instHMul.hMul (HighamBench.p19StaticExactB system i) phi)
          (HighamBench.p19StaticExactC system (basisFamily.basis k.val)))
        (instHMul.hMul (instHMul.hMul iteration.dimensionFactor (instHAdd.hAdd iteration.ug iteration.epsilonC))
          (HighamBench.p19FrobNorm
            (HighamBench.p19Augment (fun i => instHMul.hMul (HighamBench.p19StaticExactB system i) phi)
              (HighamBench.p19StaticExactC system (basisFamily.basis k.val)))))
```

### D081: `HighamBench.p19RectConditionF2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4be40f532556d3e77ff183d73f58ca53c39906eff20cfa2a95d74371577bb95c`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Real → Real
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (sigmaMin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigmaMin => instHDiv.hDiv (HighamBench.p19FrobNorm A) sigmaMin
```

### D082: `HighamBench.p19RectMatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5e9563ecebb7f14ef3dfee0df9571dc5b992f9e32c9c0c19c6b34001b872d8e1`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → HighamBench.P19Vector k → HighamBench.P19Vector m
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (x : HighamBench.P19Vector k) → HighamBench.P19Vector m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D083: `HighamBench.p19StaticExactB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4319e900a6bd10e9333ccb65413a9942cdbde8a752183b6e91ddff40f73fa205`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19MatVec system.MLinv system.b
```

### D084: `HighamBench.p19StaticExactC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `76bb6b06369be7ce2a16c093984eddc2dcc6362f2a005d765bda96800c51fcdd`

Type:

```lean
{n k : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19RectMatrix n k → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n k : Nat} →
  (system : HighamBench.P19Theorem31System n) → (Z : HighamBench.P19RectMatrix n k) → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} system Z => HighamBench.p19SquareRectMul system.MLinv (HighamBench.p19SquareRectMul system.A Z)
```

### D085: `HighamBench.p19VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e29dbb51f77b0df1c2e4cbb308e8a6e36e232c2b0ce38cd883c0b946cd01ea97`

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

### D086: `HighamBench.P19SingularValueData.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `785b5c97bf75f07f40320aa93a7623aeb13039753f9b0be30629411ab231dca4`

Type:

```lean
{m k : Nat} →
  {A : HighamBench.P19RectMatrix m k} →
    (sigmaMin sigmaMax : Real) →
      Real.instLE.le 0 sigmaMin →
        Real.instLE.le 0 sigmaMax →
          (∀ (x : HighamBench.P19Vector k),
              Real.instLE.le (instHMul.hMul sigmaMin (HighamBench.p19VecNorm2 x))
                (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x))) →
            (∀ (x : HighamBench.P19Vector k),
                Real.instLE.le (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x))
                  (instHMul.hMul sigmaMax (HighamBench.p19VecNorm2 x))) →
              (instLTNat.lt 0 k →
                  Exists fun x =>
                    And (Eq (HighamBench.p19VecNorm2 x) 1)
                      (Eq (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x)) sigmaMin)) →
                (instLTNat.lt 0 k →
                    Exists fun x =>
                      And (Eq (HighamBench.p19VecNorm2 x) 1)
                        (Eq (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x)) sigmaMax)) →
                  HighamBench.P19SingularValueData A
```

Fully explicit type:

```lean
{m k : Nat} →
  {A : HighamBench.P19RectMatrix m k} →
    (sigmaMin sigmaMax : Real) →
      (sigmaMin_nonneg :
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            sigmaMin) →
        (sigmaMax_nonneg :
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              sigmaMax) →
          (lower_gain :
              ∀ (x : HighamBench.P19Vector k),
                @LE.le.{0} Real Real.instLE
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) sigmaMin
                    (@HighamBench.p19VecNorm2 k x))
                  (@HighamBench.p19VecNorm2 m (@HighamBench.p19RectMatVec m k A x))) →
            (upper_gain :
                ∀ (x : HighamBench.P19Vector k),
                  @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 m (@HighamBench.p19RectMatVec m k A x))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) sigmaMax
                      (@HighamBench.p19VecNorm2 k x))) →
              (min_attained :
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                    @Exists.{1} (HighamBench.P19Vector k) fun (x : HighamBench.P19Vector k) =>
                      And
                        (@Eq.{1} Real (@HighamBench.p19VecNorm2 k x)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (@Eq.{1} Real (@HighamBench.p19VecNorm2 m (@HighamBench.p19RectMatVec m k A x)) sigmaMin)) →
                (max_attained :
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                      @Exists.{1} (HighamBench.P19Vector k) fun (x : HighamBench.P19Vector k) =>
                        And
                          (@Eq.{1} Real (@HighamBench.p19VecNorm2 k x)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (@Eq.{1} Real (@HighamBench.p19VecNorm2 m (@HighamBench.p19RectMatVec m k A x)) sigmaMax)) →
                  @HighamBench.P19SingularValueData m k A
```

### D087: `HighamBench.P19StaticAppendixAExpansion.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `622a39b4a5db3cb07f08c52b8caccba0945c736ad923945fcec0d054401588b8`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          {q : HighamBench.P19StaticRightQuantities family k MR MRinv} →
            (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                HighamBench.P19Vector n) →
              Eq (instHSub.hSub (family.iteration k).xHat family.system.xExact)
                  (instHAdd.hAdd
                    (instHAdd.hAdd
                      (instHAdd.hAdd (instHAdd.hAdd computationContribution rhsContribution) gmresContribution)
                      solutionContribution)
                    remainder) →
                semantics.secondOrder
                    (instHDiv.hDiv (HighamBench.p19VecNorm2 remainder) (HighamBench.p19VecNorm2 family.system.xExact)) →
                  Real.instLE.le
                      (instHDiv.hDiv (HighamBench.p19VecNorm2 computationContribution)
                        (HighamBench.p19VecNorm2 family.system.xExact))
                      (instHMul.hMul
                        (instHMul.hMul (family.iteration k).dimensionFactor
                          (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                            (HighamBench.p19StaticSplitInverse family.system MR)))
                        (instHMul.hMul (HighamBench.p19StaticAlpha MR MRinv q)
                          (HighamBench.p19SafeRelativeMagnitude (HighamBench.p19FrobNorm (family.iteration k).deltaC)
                            (HighamBench.p19FrobNorm
                              (HighamBench.p19StaticExactC family.system (family.basisFamily.basis k.val)))))) →
                    Real.instLE.le
                        (instHDiv.hDiv (HighamBench.p19VecNorm2 rhsContribution)
                          (HighamBench.p19VecNorm2 family.system.xExact))
                        (instHMul.hMul
                          (instHMul.hMul (family.iteration k).dimensionFactor
                            (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                              (HighamBench.p19StaticSplitInverse family.system MR)))
                          (instHMul.hMul (HighamBench.p19StaticBeta MR MRinv q)
                            (HighamBench.p19SafeRelativeMagnitude (HighamBench.p19VecNorm2 (family.iteration k).deltaB)
                              (HighamBench.p19VecNorm2 (HighamBench.p19StaticExactB family.system))))) →
                      Real.instLE.le
                          (instHDiv.hDiv (HighamBench.p19VecNorm2 gmresContribution)
                            (HighamBench.p19VecNorm2 family.system.xExact))
                          (instHMul.hMul
                            (instHMul.hMul (family.iteration k).dimensionFactor
                              (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                                (HighamBench.p19StaticSplitInverse family.system MR)))
                            (instHMul.hMul (HighamBench.p19StaticBeta MR MRinv q) (family.iteration k).ug)) →
                        Real.instLE.le
                            (instHDiv.hDiv (HighamBench.p19VecNorm2 solutionContribution)
                              (HighamBench.p19VecNorm2 family.system.xExact))
                            (instHMul.hMul
                              (HighamBench.p19ConditionNumberF (HighamBench.p19StaticSplitOperator family.system MRinv)
                                (HighamBench.p19StaticSplitInverse family.system MR))
                              (instHMul.hMul (HighamBench.p19StaticLambda family.system MR MRinv)
                                (HighamBench.p19SafeRelativeMagnitude
                                  (HighamBench.p19VecNorm2 (family.iteration k).deltaX)
                                  (HighamBench.p19VecNorm2
                                    (HighamBench.p19RectMatVec (family.basisFamily.basis k.val)
                                      (family.iteration k).yHat))))) →
                          HighamBench.P19StaticAppendixAExpansion family k MR MRinv q
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {k : HighamBench.P19Theorem31Dimension n} →
        {MR MRinv : HighamBench.P19Matrix n} →
          {q : @HighamBench.P19StaticRightQuantities n semantics family k MR MRinv} →
            (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                HighamBench.P19Vector n) →
              (error_decomposition :
                  @Eq.{1} (HighamBench.P19Vector n)
                    (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                      (@instHSub.{0} (HighamBench.P19Vector n)
                        (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                      (@HighamBench.P19Algorithm2Iteration.xHat n
                        (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                        (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                      (@HighamBench.P19Theorem31System.xExact n
                        (@HighamBench.P19Theorem31Family.system n semantics family)))
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                      (@instHAdd.{0} (HighamBench.P19Vector n)
                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                        (HighamBench.P19Vector n)
                        (@instHAdd.{0} (HighamBench.P19Vector n)
                          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                          (HighamBench.P19Vector n)
                          (@instHAdd.{0} (HighamBench.P19Vector n)
                            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                            (HighamBench.P19Vector n)
                            (@instHAdd.{0} (HighamBench.P19Vector n)
                              (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                            computationContribution rhsContribution)
                          gmresContribution)
                        solutionContribution)
                      remainder)) →
                (remainder_second_order :
                    HighamBench.P19FirstOrderSemantics.secondOrder semantics
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HighamBench.p19VecNorm2 n remainder)
                        (@HighamBench.p19VecNorm2 n
                          (@HighamBench.P19Theorem31System.xExact n
                            (@HighamBench.P19Theorem31Family.system n semantics family))))) →
                  (computation_gain_bound :
                      @LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HighamBench.p19VecNorm2 n computationContribution)
                          (@HighamBench.p19VecNorm2 n
                            (@HighamBench.P19Theorem31System.xExact n
                              (@HighamBench.P19Theorem31Family.system n semantics family))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                              (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                              (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                              (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                            (@HighamBench.p19ConditionNumberF n
                              (@HighamBench.p19StaticSplitOperator n
                                (@HighamBench.P19Theorem31Family.system n semantics family) MRinv)
                              (@HighamBench.p19StaticSplitInverse n
                                (@HighamBench.P19Theorem31Family.system n semantics family) MR)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HighamBench.p19StaticAlpha n semantics family k MR MRinv q)
                            (HighamBench.p19SafeRelativeMagnitude
                              (@HighamBench.p19FrobNorm n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k)
                                (@HighamBench.P19Algorithm2Iteration.deltaC n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                  (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
                              (@HighamBench.p19FrobNorm n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k)
                                (@HighamBench.p19StaticExactC n
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k)
                                  (@HighamBench.P19Theorem31Family.system n semantics family)
                                  (@HighamBench.P19Theorem31BasisFamily.basis n
                                    (@HighamBench.P19Theorem31Family.system n semantics family)
                                    (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                                    (@Subtype.val.{1} Nat
                                      (fun (k : Nat) =>
                                        And
                                          (@LT.lt.{0} Nat instLTNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                          (@LE.le.{0} Nat instLENat k n))
                                      k)))))))) →
                    (rhs_gain_bound :
                        @LE.le.{0} Real Real.instLE
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HighamBench.p19VecNorm2 n rhsContribution)
                            (@HighamBench.p19VecNorm2 n
                              (@HighamBench.P19Theorem31System.xExact n
                                (@HighamBench.P19Theorem31Family.system n semantics family))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                                (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                              (@HighamBench.p19ConditionNumberF n
                                (@HighamBench.p19StaticSplitOperator n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) MRinv)
                                (@HighamBench.p19StaticSplitInverse n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) MR)))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HighamBench.p19StaticBeta n semantics family k MR MRinv q)
                              (HighamBench.p19SafeRelativeMagnitude
                                (@HighamBench.p19VecNorm2 n
                                  (@HighamBench.P19Algorithm2Iteration.deltaB n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                    (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                    (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
                                (@HighamBench.p19VecNorm2 n
                                  (@HighamBench.p19StaticExactB n
                                    (@HighamBench.P19Theorem31Family.system n semantics family))))))) →
                      (gmres_gain_bound :
                          @LE.le.{0} Real Real.instLE
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HighamBench.p19VecNorm2 n gmresContribution)
                              (@HighamBench.p19VecNorm2 n
                                (@HighamBench.P19Theorem31System.xExact n
                                  (@HighamBench.P19Theorem31Family.system n semantics family))))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                  (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                                (@HighamBench.p19ConditionNumberF n
                                  (@HighamBench.p19StaticSplitOperator n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) MRinv)
                                  (@HighamBench.p19StaticSplitInverse n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) MR)))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HighamBench.p19StaticBeta n semantics family k MR MRinv q)
                                (@HighamBench.P19Algorithm2Iteration.ug n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                  (@HighamBench.P19Theorem31Family.iteration n semantics family k))))) →
                        (solution_gain_bound :
                            @LE.le.{0} Real Real.instLE
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@HighamBench.p19VecNorm2 n solutionContribution)
                                (@HighamBench.p19VecNorm2 n
                                  (@HighamBench.P19Theorem31System.xExact n
                                    (@HighamBench.P19Theorem31Family.system n semantics family))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HighamBench.p19ConditionNumberF n
                                  (@HighamBench.p19StaticSplitOperator n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) MRinv)
                                  (@HighamBench.p19StaticSplitInverse n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) MR))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HighamBench.p19StaticLambda n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) MR MRinv)
                                  (HighamBench.p19SafeRelativeMagnitude
                                    (@HighamBench.p19VecNorm2 n
                                      (@HighamBench.P19Algorithm2Iteration.deltaX n
                                        (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                        (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
                                    (@HighamBench.p19VecNorm2 n
                                      (@HighamBench.p19RectMatVec n
                                        (@Subtype.val.{1} Nat
                                          (fun (k : Nat) =>
                                            And
                                              (@LT.lt.{0} Nat instLTNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                              (@LE.le.{0} Nat instLENat k n))
                                          k)
                                        (@HighamBench.P19Theorem31BasisFamily.basis n
                                          (@HighamBench.P19Theorem31Family.system n semantics family)
                                          (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                                          (@Subtype.val.{1} Nat
                                            (fun (k : Nat) =>
                                              And
                                                (@LT.lt.{0} Nat instLTNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                (@LE.le.{0} Nat instLENat k n))
                                            k))
                                        (@HighamBench.P19Algorithm2Iteration.yHat n
                                          (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                          (@HighamBench.P19Theorem31Family.iteration n semantics family k)))))))) →
                          @HighamBench.P19StaticAppendixAExpansion n semantics family k MR MRinv q
```

### D088: `HighamBench.P19Theorem31System.b`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `f2a130fd36774a5574504267aaab72b46108b1c686d97df059b452f44cf66199`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D089: `HighamBench.p19FullColumnRank`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `84de5f440851ab2c3f7c3f00b48f7e6daa85ef2eb14e213077a5d2a91ee34c06`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Function.Injective (HighamBench.p19RectMatVec A)
```

### D090: `HighamBench.p19IsUpperHessenberg`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `40e9dda219091e0a8274024ac3a6a6ec9b0f2c87f705a5d5c83ed03835619d3e`

Type:

```lean
{k : Nat} → HighamBench.P19RectMatrix (instHAdd.hAdd k 1) k → Prop
```

Fully explicit type:

```lean
{k : Nat} →
  (H :
      HighamBench.P19RectMatrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        k) →
    Prop
```

Definition body (one-level semantic boundary):

```lean
fun {k} H => ∀ (i : Fin (instHAdd.hAdd k 1)) (j : Fin k), instLTNat.lt (instHAdd.hAdd j.val 1) i.val → Eq (H i j) 0
```

### D091: `HighamBench.p19NearRankDeficient`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `16466bbe231c4c118f1c0663cc1bb4687beb871eeebede56fe75c840088e6a50`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Real → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (threshold : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A threshold =>
  Exists fun x =>
    And (Eq (HighamBench.p19VecNorm2 x) 1)
      (Real.instLT.lt (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x)) threshold)
```

### D092: `HighamBench.p19RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ea659dd0af1e90317a62571898bde6fc8ded022ac6934bf0f96c8e9243b11c08`

Type:

```lean
{m k q : Nat} → HighamBench.P19RectMatrix m k → HighamBench.P19RectMatrix k q → HighamBench.P19RectMatrix m q
```

Fully explicit type:

```lean
{m k q : Nat} →
  (A : HighamBench.P19RectMatrix m k) → (B : HighamBench.P19RectMatrix k q) → HighamBench.P19RectMatrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D093: `HighamBench.p19ScaledFirstBasisVector`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7eeb372ed49009a9fbaa619f7d7edd369b54e614c91e79ae1a32ede22433dc11`

Type:

```lean
{k : Nat} → Real → HighamBench.P19Vector (instHAdd.hAdd k 1)
```

Fully explicit type:

```lean
{k : Nat} →
  (beta : Real) →
    HighamBench.P19Vector
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {k} beta i => ite (Eq i.val 0) beta 0
```

### D094: `HighamBench.p19SafeRelativeMagnitude`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e90ca3fde1791e8677db326faa8ac6b95895f175f7ab0b517236d9c16c6a1872`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(actual reference : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun actual reference => ite (Eq reference 0) 0 (instHDiv.hDiv actual reference)
```

### D095: `And`

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

### D096: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D097: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D098: `Nat`

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

### D099: `Real`

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

### D100: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D101: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D102: `DivInvMonoid.toDiv`

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

### D103: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D104: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D105: `HAdd.hAdd`

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

### D106: `HDiv.hDiv`

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

### D107: `HSub.hSub`

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

### D108: `LE.le`

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

### D109: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D110: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Fully explicit type:

```lean
(m : Type u) → (n : Type u') → (α : Type v) → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D111: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D112: `One.toOfNat1`

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

### D113: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`

Type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub (G i)] → Sub ((i : ι) → G i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub.{u_4} (G i)] → Sub.{max u_1 u_4} ((i : ι) → G i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {G} [(i : ι) → Sub (G i)] => { sub := fun f g i => instHSub.hSub (f i) (g i) }
```

### D114: `Real.instAdd`

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

### D115: `Real.instAddGroup`

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

### D116: `Real.instDivInvMonoid`

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

### D117: `Real.instLE`

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

Fully explicit type:

```lean
NatCast.{0} Real
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

Fully explicit type:

```lean
One.{0} Real
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

Fully explicit type:

```lean
Sub.{0} Real
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

Fully explicit type:

```lean
Lattice.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D122: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Sort (max 1 u)
```

### D123: `Subtype.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `69c61ab82498e5563eaf5f0313ea7f2164c284c3dc742024a30332372a46663d`

Type:

```lean
{α : Sort u} → {p : α → Prop} → Subtype p → α
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (self : @Subtype.{u} α p) → α
```

Definition body (one-level semantic boundary):

```lean
fun α p self => self.1
```

### D124: `abs`

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

### D125: `instHAdd`

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

### D126: `instHDiv`

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

### D127: `instHSub`

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

### D128: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Fully explicit type:

```lean
LE.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D129: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D130: `instOfNatAtLeastTwo`

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

### D131: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D132: `And.intro`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `232593c5c388d46173a03223cb6b55ff2a132de1d4dfae47c09b5ba49b1e4f83`

Type:

```lean
∀ {a b : Prop}, a → b → And a b
```

Fully explicit type:

```lean
∀ {a b : Prop} (left : a) (right : b), And a b
```

### D133: `Fin.fintype`

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

### D134: `Finset.sum`

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

### D135: `Finset.univ`

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

### D136: `Iff.mpr`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `abcae2cc4e99f1dc596c9080dca30ec894770912ebfc2b6ad2910b661baa68ed`

Type:

```lean
∀ {a b : Prop}, Iff a b → b → a
```

Fully explicit type:

```lean
∀ {a b : Prop} (self : Iff a b), b → a
```

### D137: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add.{v} α] → Add.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D138: `Matrix.frobeniusNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3f944d9003e72c887b38048a3f469c42c010d0e141780ed19b0137eb25d742ba`

Type:

```lean
{m : Type u_3} →
  {n : Type u_4} →
    {α : Type u_5} → [Fintype m] → [Fintype n] → [NormedAddCommGroup α] → NormedAddCommGroup (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_3} →
  {n : Type u_4} →
    {α : Type u_5} →
      [Fintype.{u_3} m] →
        [Fintype.{u_4} n] →
          [NormedAddCommGroup.{u_5} α] → NormedAddCommGroup.{max (max u_5 u_4) u_3} (Matrix.{u_3, u_4, u_5} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Fintype m] [Fintype n] [NormedAddCommGroup α] => PiLp.normedAddCommGroupToPi 2 fun a => n → α
```

### D139: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6fa198061d1b8595a7b8b0ed74bd9e48f2c7a18aa01bf39d9c30be49c1d4741c`

Type:

```lean
{α : Type u} → [self : Max α] → α → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Max.{u} α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Max α] => self.1
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

Fully explicit type:

```lean
(n : Nat) → Prop
```

### D141: `Nat.le_of_lt`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `ff212a95500662f3fc7ee2c8e4193476d63a9914c09b07b917a87fc24a0c94ad`

Type:

```lean
∀ {n m : Nat}, instLTNat.lt n m → instLENat.le n m
```

Fully explicit type:

```lean
∀ {n m : Nat}, @LT.lt.{0} Nat instLTNat n m → @LE.le.{0} Nat instLENat n m
```

### D142: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D143: `Nat.succ_le_iff`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `d5b55de88f550a3dcb1879518a5688ec9a4d8ca18878d7d0d8df30740c0ae92b`

Type:

```lean
∀ {m n : Nat}, Iff (instLENat.le m.succ n) (instLTNat.lt m n)
```

Fully explicit type:

```lean
∀ {m n : Nat}, Iff (@LE.le.{0} Nat instLENat (Nat.succ m) n) (@LT.lt.{0} Nat instLTNat m n)
```

### D144: `Nat.succ_pos`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `0e7e3546875c3c758b7e9f771f5146afbe4374a7356e205021f87835237aeaa7`

Type:

```lean
∀ (n : Nat), instLTNat.lt 0 n.succ
```

Fully explicit type:

```lean
∀ (n : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.succ n)
```

### D145: `Nat.zero_lt_one`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7af00b6e71ddbd58776e8dc3a2c9845b1099ebd1b1c29b6b3d4e09c80c3bc1a7`

Type:

```lean
instLTNat.lt 0 1
```

Fully explicit type:

```lean
@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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

Fully explicit type:

```lean
{E : Type u_8} → [self : Norm.{u_8} E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D147: `NormedAddCommGroup.toNorm`

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

### D148: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Fully explicit type:

```lean
(a : Prop) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D149: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D150: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add.{u_5} (M i)] → Add.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D151: `Real.instAddCommMonoid`

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

### D152: `Real.instLT`

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

### D153: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `313f6558836157f8e8b4ea7be18fb6953bf9aefc4dcb68940ef5c4889e18a763`

Type:

```lean
Max Real
```

Fully explicit type:

```lean
Max.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```

### D154: `Real.instZero`

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

### D155: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Fully explicit type:

```lean
NormedAddCommGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```

### D156: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D157: `Subtype.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `488ac61b6d3c07fb9a2f54a03a39e6001a4c7cedfd07515f0f9865e7fef9ef51`

Type:

```lean
{α : Sort u} → {p : α → Prop} → (val : α) → p val → Subtype p
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (val : α) → (property : p val) → @Subtype.{u} α p
```

### D158: `Zero.toOfNat0`

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

### D159: `instAddNat`

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

### D160: `Fin.cases`

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

Fully explicit type:

```lean
{n : Nat} →
  {motive :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Sort u_1} →
    (zero :
        motive
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))) →
      (succ : (i : Fin n) → motive (@Fin.succ n i)) →
        (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} zero succ i => Fin.induction zero (fun i x => succ i) i
```

### D161: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D162: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D163: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D164: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D165: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero.{u_5} (M i)] → Zero.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```

### D166: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D167: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D168: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Fully explicit type:

```lean
{n : Nat} → (self : Fin n) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D169: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```

### D170: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

Type:

```lean
DecidableEq Nat
```

Fully explicit type:

```lean
DecidableEq.{1} Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D171: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t e : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D172: `Real.decidableEq`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `58b21b2d8719c9bf9f6e23c4dbf1284069f5ce6f35c64915e45284792e8a5bcf`

Type:

```lean
(a b : Real) → Decidable (Eq a b)
```

Fully explicit type:

```lean
(a b : Real) → Decidable (@Eq.{1} Real a b)
```

Definition body (one-level semantic boundary):

```lean
fun a b => inferInstance
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

### `HighamBench.P19Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P19Definitions.lean`
SHA-256: `d1ee3760a4b34e9b845d1f5a65909aed6737cf7fb411c3607928aed8ed72ee27`

```lean
import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

/-- A finite square real matrix in the P19 model. -/
abbrev P19Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite rectangular real matrix in the P19 model. -/
abbrev P19RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

/-- A finite real vector in the P19 model. -/
abbrev P19Vector (n : ℕ) := Fin n → ℝ

/-- Paper-scoped squared Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p19VecNorm2Sq x)

/-- Add two paper-scoped finite error vectors. -/
def p19Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Scale a paper-scoped finite error vector. -/
def p19Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- Exact scalar envelope corresponding to `ξ` in equation (3.8). -/
def p19ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p19MatVec {n : ℕ} (A : P19Matrix n)
    (x : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Exact finite rectangular matrix-vector multiplication. -/
noncomputable def p19RectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

/-- Exact multiplication of a square matrix by a rectangular matrix. -/
noncomputable def p19SquareRectMul {n k : ℕ} (A : P19Matrix n)
    (B : P19RectMatrix n k) : P19RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

/-- Exact multiplication of two conforming rectangular matrices. -/
noncomputable def p19RectMatMul {m k q : ℕ} (A : P19RectMatrix m k)
    (B : P19RectMatrix k q) : P19RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

/-- The Frobenius norm used by the matrix perturbation models in (3.2)-(3.8). -/
noncomputable def p19FrobNorm {m k : ℕ} (A : P19RectMatrix m k) : ℝ :=
  ‖A‖

/-- A matrix column represented as a finite vector. -/
def p19Column {m k : ℕ} (A : P19RectMatrix m k) (j : Fin k) : P19Vector m :=
  fun i ↦ A i j

/-- Append a vector as the first column of a rectangular matrix. -/
noncomputable def p19Augment {n k : ℕ} (b : P19Vector n)
    (C : P19RectMatrix n k) : P19RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i) (fun j ↦ C i j)

/-- The vector `beta * e_1` in the MGS factorization (3.1). -/
def p19ScaledFirstBasisVector {k : ℕ} (beta : ℝ) : P19Vector (k + 1) :=
  fun i ↦ if i.val = 0 then beta else 0

/-- The structural upper-Hessenberg condition on the MGS factor. -/
def p19IsUpperHessenberg {k : ℕ}
    (H : P19RectMatrix (k + 1) k) : Prop :=
  ∀ i j, j.val + 1 < i.val → H i j = 0

/-- Two square matrices are certified inverses through their exact actions. -/
def p19InversePair {n : ℕ} (A Ainv : P19Matrix n) : Prop :=
  (∀ x : P19Vector n, p19MatVec Ainv (p19MatVec A x) = x) ∧
    ∀ x : P19Vector n, p19MatVec A (p19MatVec Ainv x) = x

/-- Exact least-squares optimality for line 3 of Algorithm 2. -/
def p19IsLeastSquaresSolution {m k : ℕ} (A : P19RectMatrix m k)
    (b : P19Vector m) (y : P19Vector k) : Prop :=
  ∀ z : P19Vector k,
    p19VecNorm2 (b - p19RectMatVec A y) ≤
      p19VecNorm2 (b - p19RectMatVec A z)

/-- A rectangular matrix has full column rank when its exact action is injective. -/
def p19FullColumnRank {m k : ℕ} (A : P19RectMatrix m k) : Prop :=
  Function.Injective (p19RectMatVec A)

/-- Certified extremal singular values for a finite real matrix. The gain and
attainment clauses give the exact Euclidean meanings of `sigma_min` and
`sigma_max` without depending on a particular SVD implementation. -/
structure P19SingularValueData {m k : ℕ} (A : P19RectMatrix m k) where
  sigmaMin : ℝ
  sigmaMax : ℝ
  sigmaMin_nonneg : 0 ≤ sigmaMin
  sigmaMax_nonneg : 0 ≤ sigmaMax
  lower_gain : ∀ x : P19Vector k,
    sigmaMin * p19VecNorm2 x ≤ p19VecNorm2 (p19RectMatVec A x)
  upper_gain : ∀ x : P19Vector k,
    p19VecNorm2 (p19RectMatVec A x) ≤ sigmaMax * p19VecNorm2 x
  min_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMin
  max_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMax

/-- One explicit nonnegative low-degree polynomial represented by `c(n,k)`. -/
structure P19PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

/-- Evaluation of the recorded low-degree polynomial factor. -/
noncomputable def p19PolynomialFactorValue (c : P19PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

/-- A scalar remainder that is second order in the combined precision scale. -/
def p19SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise version of the paper's `lesssim`: an inequality modulo an
otherwise unspecified second-order remainder. -/
def p19FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p19SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The paper's qualitative `theta << 1` along a precision regime. -/
def p19MuchLessThanOneAt {ι : Type*} (l : Filter ι)
    (theta : ι → ℝ) : Prop :=
  Filter.Tendsto theta l (nhds 0) ∧
    ∀ᶠ t in l, 0 ≤ theta t ∧ theta t < 1

/-- An increasing family of full-rank search bases. Successive members agree
on all previously present columns. -/
structure P19IncreasingBasisFamily (n : ℕ) (ι : Type*) where
  basis : (k : ℕ) → ι → P19RectMatrix n k
  full_rank : ∀ (k : ℕ), k ≤ n → ∀ (t : ι), p19FullColumnRank (basis k t)
  column_prefix : ∀ (k : ℕ) (t : ι) (i : Fin n) (j : Fin k), k < n →
    basis k t i j = basis (k + 1) t i j.castSucc

/-- Frobenius-to-smallest-singular-value condition measure for a rectangular
matrix. This is the paper's `kappa_F,2` interpretation of an unqualified
rectangular `kappa`. -/
noncomputable def p19RectConditionF2 {m k : ℕ}
    (A : P19RectMatrix m k) (sigmaMin : ℝ) : ℝ :=
  p19FrobNorm A / sigmaMin

/-- Frobenius condition number represented using a certified inverse. -/
noncomputable def p19ConditionNumberF {n : ℕ}
    (A Ainv : P19Matrix n) : ℝ :=
  p19FrobNorm Ainv * p19FrobNorm A

/-- One precision-parametrized execution of Algorithm 2 at the key dimension
selected by the MGS analysis used in Theorem 3.1. The fields through
`solution_small` are precisely the four modules (3.2)-(3.6). The final defect
fields record the near-orthogonality estimate recalled from the MGS analysis;
they do not assume either displayed `4/3` conclusion. -/
structure P19ModularGMRESRun {n : ℕ} {ι : Type*} (l : Filter ι) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  basisFamily : P19IncreasingBasisFamily n ι
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  epsilonC : ι → ℝ
  epsilonB : ι → ℝ
  ug : ι → ℝ
  epsilonX : ι → ℝ
  accuracy_nonneg : ∀ t,
    0 ≤ epsilonC t ∧ 0 ≤ epsilonB t ∧ 0 ≤ ug t ∧ 0 ≤ epsilonX t
  accuracy_tendsto_zero :
    Filter.Tendsto epsilonC l (nhds 0) ∧
      Filter.Tendsto epsilonB l (nhds 0) ∧
      Filter.Tendsto ug l (nhds 0) ∧
      Filter.Tendsto epsilonX l (nhds 0)
  computedC : ι → P19RectMatrix n keyDimension
  deltaC : ι → P19RectMatrix n keyDimension
  computation_equation : ∀ t,
    computedC t =
      p19SquareRectMul MLinv
          (p19SquareRectMul A (basisFamily.basis keyDimension t)) +
        deltaC t
  computation_error_bound : ∀ t,
    p19FrobNorm (deltaC t) ≤
      epsilonC t *
        p19FrobNorm
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  computedB : ι → P19Vector n
  deltaB : ι → P19Vector n
  rhs_equation : ∀ t,
    computedB t = p19MatVec MLinv b + deltaB t
  rhs_error_bound : ∀ t,
    p19VecNorm2 (deltaB t) ≤ epsilonB t * p19VecNorm2 (p19MatVec MLinv b)
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_givens_relation : ∀ t,
    p19Augment (computedB t) (computedC t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedC t + leastSquaresDeltaC t)
      (computedB t + leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column (p19Augment (computedB t) (computedC t)) j)
  computedCSpectrum : ∀ t, P19SingularValueData (computedC t)
  computedC_numerically_nonsingular :
    p19MuchLessThanOneAt l (fun t ↦
      ug t *
        p19RectConditionF2 (computedC t)
          (computedCSpectrum t).sigmaMin)
  exactCSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MLinv
        (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  combined_model_small :
    p19MuchLessThanOneAt l (fun t ↦
      (epsilonC t + epsilonB t + ug t) *
        p19RectConditionF2
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
          (exactCSpectrum t).sigmaMin)
  xHat : ι → P19Vector n
  deltaX : ι → P19Vector n
  solution_equation : ∀ t,
    xHat t = p19RectMatVec (basisFamily.basis keyDimension t) (yHat t) + deltaX t
  solution_error_bound : ∀ t,
    p19VecNorm2 (deltaX t) ≤
      epsilonX t *
        p19VecNorm2
          (p19RectMatVec (basisFamily.basis keyDimension t) (yHat t))
  solution_small : p19MuchLessThanOneAt l epsilonX
  vHatSpectrum : ∀ t, P19SingularValueData (vHat t)
  mgsOrthogonalityDefect : ι → ℝ
  mgs_defect_nonneg : ∀ t, 0 ≤ mgsOrthogonalityDefect t
  mgs_defect_small : ∀ᶠ t in l, mgsOrthogonalityDefect t ≤ 7 / 16
  mgs_sigmaMin_sq_lower : ∀ t,
    1 - mgsOrthogonalityDefect t ≤ (vHatSpectrum t).sigmaMin ^ 2
  mgs_sigmaMax_sq_upper : ∀ t,
    (vHatSpectrum t).sigmaMax ^ 2 ≤ 1 + mgsOrthogonalityDefect t

/-- The combined precision scale used to classify the omitted second-order
terms in Theorem 3.1. -/
noncomputable def p19PrecisionScale {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ run.epsilonC t + run.epsilonB t + run.ug t + run.epsilonX t

/-- The exact left-preconditioned basis product in (3.2). -/
noncomputable def p19ExactC {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (t : ι) :
    P19RectMatrix n run.keyDimension :=
  p19SquareRectMul run.MLinv
    (p19SquareRectMul run.A (run.basisFamily.basis run.keyDimension t))

/-- The split-preconditioned operator `M_L^{-1} A M_R^{-1}`. -/
noncomputable def p19SplitOperator {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul run.MLinv (p19SquareRectMul run.A MRinv)

/-- Its certified inverse `M_R A^{-1} M_L`. -/
noncomputable def p19SplitInverse {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul run.Ainv run.ML)

/-- The normalized forward error (2.1). -/
noncomputable def p19ForwardError {n : ℕ}
    (x xHat : P19Vector n) : ℝ :=
  p19VecNorm2 (xHat - x) / p19VecNorm2 x

/-- Exact singular-value data needed to instantiate `alpha` and `beta` for one
arbitrary nonsingular analytical right preconditioner. -/
structure P19RightPreconditionedQuantities {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MR
        (run.basisFamily.basis run.keyDimension t))
  mrz_sigmaMin_pos : ∀ t, 0 < (mrzSpectrum t).sigmaMin

/-- The coefficient `alpha` below equation (3.8). -/
noncomputable def p19Alpha {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  (p19ConditionNumberF MR MRinv / (q.mrzSpectrum t).sigmaMin) *
    (p19FrobNorm (p19ExactC run t) /
      p19FrobNorm (p19SplitOperator run MRinv))

/-- The coefficient `beta` below equation (3.8). -/
noncomputable def p19Beta {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  max 1
      ((p19FrobNorm (p19ExactC run t) /
          p19FrobNorm (p19SplitOperator run MRinv)) /
        (q.mrzSpectrum t).sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- The coefficient `lambda` below equation (3.8). -/
noncomputable def p19Lambda {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19SplitOperator run MRinv) (p19SplitInverse run MR)

/-- The exact four-source quantity `xi` in equation (3.8). -/
noncomputable def p19Xi {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  p19ModularEnvelope (p19Alpha run MR MRinv q t)
    (p19Beta run MR MRinv q t) (p19Lambda run MR MRinv)
    (run.epsilonC t) (run.epsilonB t) (run.ug t) (run.epsilonX t)

/-- Appendix-A propagation certificate for the four heterogeneous Algorithm 2
errors. Each contribution is formally tied to its source perturbation; their
sum, rather than the final forward-error inequality, is recorded. -/
structure P19ForwardAnalysis {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  quantities : P19RightPreconditionedQuantities run MR MRinv
  computationPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  rhsPropagation : ι → P19Vector n → P19Vector n
  leastSquaresBPropagation : ι → P19Vector n → P19Vector n
  leastSquaresCPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  solutionPropagation : ι → P19Vector n → P19Vector n
  computationContribution : ι → P19Vector n
  rhsContribution : ι → P19Vector n
  gmresContribution : ι → P19Vector n
  solutionContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  computation_link : ∀ t,
    computationContribution t = computationPropagation t (run.deltaC t)
  rhs_link : ∀ t, rhsContribution t = rhsPropagation t (run.deltaB t)
  gmres_link : ∀ t,
    gmresContribution t =
      leastSquaresBPropagation t (run.leastSquaresDeltaB t) +
        leastSquaresCPropagation t (run.leastSquaresDeltaC t)
  solution_link : ∀ t,
    solutionContribution t = solutionPropagation t (run.deltaX t)
  computationPropagation_zero : ∀ t, computationPropagation t 0 = 0
  rhsPropagation_zero : ∀ t, rhsPropagation t 0 = 0
  leastSquaresBPropagation_zero : ∀ t, leastSquaresBPropagation t 0 = 0
  leastSquaresCPropagation_zero : ∀ t, leastSquaresCPropagation t 0 = 0
  solutionPropagation_zero : ∀ t, solutionPropagation t 0 = 0
  error_decomposition : ∀ t,
    run.xHat t - run.xExact =
      computationContribution t + rhsContribution t + gmresContribution t +
        solutionContribution t + remainder t
  computation_bound : ∀ t,
    p19VecNorm2 (computationContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Alpha run MR MRinv quantities t * run.epsilonC t)
  rhs_bound : ∀ t,
    p19VecNorm2 (rhsContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.epsilonB t)
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.ug t)
  solution_bound : ∀ t,
    p19VecNorm2 (solutionContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Lambda run MR MRinv * run.epsilonX t)
  remainder_second_order :
    p19SecondOrderAt l (p19PrecisionScale run)
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 run.xExact)

/-- A complete proof-carrying execution of the hypotheses and intermediate
Appendix-A propagation used by Theorem 3.1. -/
structure P19Theorem31Execution {n : ℕ} {ι : Type*} (l : Filter ι) where
  run : P19ModularGMRESRun (n := n) l
  forwardAnalysis : ∀ (MR MRinv : P19Matrix n),
    p19InversePair MR MRinv → P19ForwardAnalysis run MR MRinv

/-- Static semantics for the source's qualitative first-order notation. The
paper deliberately supplies neither a limiting parameter nor a numerical
smallness threshold, so both predicates remain part of the interpretation. -/
structure P19FirstOrderSemantics where
  small : ℝ → Prop
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

/-- The source relation `lhs lesssim rhs`: an exact inequality after retaining
one term classified as negligible and second order by the chosen semantics. -/
def p19FirstOrderLe (semantics : P19FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

/-- A ratio that remains defined when its reference magnitude is zero. Source
error inequalities force the numerator to vanish in that case. -/
noncomputable def p19SafeRelativeMagnitude (actual reference : ℝ) : ℝ :=
  if reference = 0 then 0 else actual / reference

/-- A dimension admitted by Theorem 3.1. -/
abbrev P19Theorem31Dimension (n : ℕ) :=
  {k : ℕ // 0 < k ∧ k ≤ n}

/-- Static nonsingular linear-system data shared by all Algorithm 2
dimensions. -/
structure P19Theorem31System (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b

/-- The increasing full-rank search-space input from Theorem 3.1. -/
structure P19Theorem31BasisFamily {n : ℕ}
    (system : P19Theorem31System n) where
  basis : (k : ℕ) → P19RectMatrix n k
  full_rank : ∀ k, 0 < k → k ≤ n → p19FullColumnRank (basis k)
  column_prefix : ∀ k, k < n → ∀ i (j : Fin k),
    basis k i j = basis (k + 1) i j.castSucc

/-- Exact left-preconditioned basis product in equation (3.2). -/
noncomputable def p19StaticExactC {n k : ℕ}
    (system : P19Theorem31System n) (Z : P19RectMatrix n k) :
    P19RectMatrix n k :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A Z)

/-- Exact left-preconditioned right-hand side in equation (3.3). -/
noncomputable def p19StaticExactB {n : ℕ}
    (system : P19Theorem31System n) : P19Vector n :=
  p19MatVec system.MLinv system.b

/-- One fixed-precision execution of all four modules of Algorithm 2 at one
positive dimension. No selected key dimension or final error bound is stored. -/
structure P19Algorithm2Iteration {n : ℕ}
    (system : P19Theorem31System n)
    (semantics : P19FirstOrderSemantics)
    (basisFamily : P19Theorem31BasisFamily system)
    (k : P19Theorem31Dimension n) where
  dimensionFactor : ℝ
  dimensionFactor_one_le : 1 ≤ dimensionFactor
  epsilonC : ℝ
  epsilonB : ℝ
  ug : ℝ
  epsilonX : ℝ
  computedC : P19RectMatrix n k.1
  deltaC : P19RectMatrix n k.1
  computation_equation :
    computedC = p19StaticExactC system (basisFamily.basis k.1) + deltaC
  computedB : P19Vector n
  deltaB : P19Vector n
  rhs_equation : computedB = p19StaticExactB system + deltaB
  vHat : P19RectMatrix n k.1
  vHatNext : P19RectMatrix n (k.1 + 1)
  beta : ℝ
  hessenberg : P19RectMatrix (k.1 + 1) k.1
  hessenberg_upper : p19IsUpperHessenberg hessenberg
  mgs_givens_relation :
    p19Augment computedB computedC =
      p19RectMatMul vHatNext
        (p19Augment (p19ScaledFirstBasisVector beta) hessenberg)
  vHat_prefix : ∀ i (j : Fin k.1),
    vHat i j = vHatNext i j.castSucc
  leastSquaresDeltaB : P19Vector n
  leastSquaresDeltaC : P19RectMatrix n k.1
  yHat : P19Vector k.1
  computedCSpectrum : P19SingularValueData computedC
  exactCSpectrum :
    P19SingularValueData
      (p19StaticExactC system (basisFamily.basis k.1))
  xHat : P19Vector n
  deltaX : P19Vector n
  solution_equation :
    xHat = p19RectMatVec (basisFamily.basis k.1) yHat + deltaX
  vHatSpectrum : P19SingularValueData vHat

/-- Equations (3.2)-(3.6) and the MGS/Givens least-squares model at one
specific Algorithm 2 dimension. Theorem 3.1 requires these only at the
dimension selected by the MGS argument. -/
structure P19Algorithm2Conditions {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) where
  accuracy_nonneg :
    0 ≤ iteration.epsilonC ∧ 0 ≤ iteration.epsilonB ∧
      0 ≤ iteration.ug ∧ 0 ≤ iteration.epsilonX
  computation_error_bound :
    p19FrobNorm iteration.deltaC ≤
      iteration.epsilonC *
        p19FrobNorm (p19StaticExactC system (basisFamily.basis k.1))
  rhs_error_bound :
    p19VecNorm2 iteration.deltaB ≤
      iteration.epsilonB * p19VecNorm2 (p19StaticExactB system)
  least_squares_solution :
    p19IsLeastSquaresSolution
      (iteration.computedC + iteration.leastSquaresDeltaC)
      (iteration.computedB + iteration.leastSquaresDeltaB) iteration.yHat
  least_squares_column_bound : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment iteration.leastSquaresDeltaB
            iteration.leastSquaresDeltaC) j) ≤
      iteration.dimensionFactor * iteration.ug *
        p19VecNorm2
          (p19Column
            (p19Augment iteration.computedB iteration.computedC) j)
  computedC_numerically_nonsingular :
    semantics.small
      (iteration.ug *
        p19RectConditionF2 iteration.computedC
          iteration.computedCSpectrum.sigmaMin)
  combined_model_small :
    semantics.small
      ((iteration.epsilonC + iteration.epsilonB + iteration.ug) *
        p19RectConditionF2
          (p19StaticExactC system (basisFamily.basis k.1))
          iteration.exactCSpectrum.sigmaMin)
  solution_error_bound :
    p19VecNorm2 iteration.deltaX ≤
      iteration.epsilonX *
        p19VecNorm2 (p19RectMatVec (basisFamily.basis k.1) iteration.yHat)
  solution_small : semantics.small iteration.epsilonX

/-- The two explicit conditioning inequalities in equation (3.7). -/
def p19IterationWellConditioned {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  1 / iteration.vHatSpectrum.sigmaMin ≤ 4 / 3 ∧
    iteration.vHatSpectrum.sigmaMax ≤ 4 / 3

/-- Witness form of an upper bound on the smallest singular value. -/
def p19NearRankDeficient {m k : ℕ} (A : P19RectMatrix m k)
    (threshold : ℝ) : Prop :=
  ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧
      p19VecNorm2 (p19RectMatVec A x) < threshold

/-- The input-near-dependence alternative (A.1), required only before the
full dimension. -/
def p19MGSNearDependence {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  ∀ phi : ℝ, 0 < phi →
    p19NearRankDeficient
      (p19Augment
        (fun i ↦ p19StaticExactB system i * phi)
        (p19StaticExactC system (basisFamily.basis k.1)))
      (iteration.dimensionFactor * (iteration.ug + iteration.epsilonC) *
        p19FrobNorm
          (p19Augment
            (fun i ↦ p19StaticExactB system i * phi)
            (p19StaticExactC system (basisFamily.basis k.1))))

/-- Static Algorithm 2 executions at every increasing dimension. -/
structure P19Theorem31Family (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  system : P19Theorem31System n
  basisFamily : P19Theorem31BasisFamily system
  iteration : ∀ k : P19Theorem31Dimension n,
    P19Algorithm2Iteration system semantics basisFamily k

/-- The reusable MGS result invoked through [11, equations (5.15)-(5.17)] and
the Paige MGS analysis: the first basis is well conditioned, and loss at the
next dimension forces (A.1) for the current input. It contains no selected
dimension. -/
structure P19MGSSelectionLaw {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  first_dimension_good :
    p19IterationWellConditioned
      (family.iteration
        ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩)
  loss_implies_near_dependence : ∀ (k : ℕ)
      (hkpos : 0 < k) (hklt : k < n),
    let current : P19Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    let next : P19Theorem31Dimension n :=
      ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
    ¬ p19IterationWellConditioned (family.iteration next) →
      p19MGSNearDependence (family.iteration current)

/-- The split-preconditioned operator for the static Theorem 3.1 model. -/
noncomputable def p19StaticSplitOperator {n : ℕ}
    (system : P19Theorem31System n) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A MRinv)

/-- A certified inverse of the static split-preconditioned operator. -/
noncomputable def p19StaticSplitInverse {n : ℕ}
    (system : P19Theorem31System n) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul system.Ainv system.ML)

/-- Singular-value and positivity evidence used to interpret the displayed
`alpha`, `beta`, and `lambda` for one analytical right preconditioner. -/
structure P19StaticRightQuantities {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum :
    P19SingularValueData
      (p19SquareRectMul MR (family.basisFamily.basis k.1))
  mrz_sigmaMin_pos : 0 < mrzSpectrum.sigmaMin
  exactC_norm_pos :
    0 < p19FrobNorm
      (p19StaticExactC family.system (family.basisFamily.basis k.1))
  split_operator_norm_pos :
    0 < p19FrobNorm (p19StaticSplitOperator family.system MRinv)
  mr_condition_pos : 0 < p19ConditionNumberF MR MRinv
  split_condition_pos :
    0 < p19ConditionNumberF
      (p19StaticSplitOperator family.system MRinv)
      (p19StaticSplitInverse family.system MR)

/-- `alpha` below equation (3.8), with the paper-authorized Frobenius
interpretation of unqualified square condition numbers. -/
noncomputable def p19StaticAlpha {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  (p19ConditionNumberF MR MRinv / q.mrzSpectrum.sigmaMin) *
    (p19FrobNorm
        (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
      p19FrobNorm (p19StaticSplitOperator family.system MRinv))

/-- `beta` below equation (3.8). -/
noncomputable def p19StaticBeta {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  max 1
      ((p19FrobNorm
          (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
          p19FrobNorm (p19StaticSplitOperator family.system MRinv)) /
        q.mrzSpectrum.sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- `lambda` below equation (3.8). -/
noncomputable def p19StaticLambda {n : ℕ}
    (system : P19Theorem31System n) (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19StaticSplitOperator system MRinv)
      (p19StaticSplitInverse system MR)

/-- The exact four-source coefficient `xi` in equation (3.8). -/
noncomputable def p19StaticXi {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  let run := family.iteration k
  p19ModularEnvelope (p19StaticAlpha MR MRinv q)
    (p19StaticBeta MR MRinv q)
    (p19StaticLambda family.system MR MRinv)
    run.epsilonC run.epsilonB run.ug run.epsilonX

/-- Raw Appendix-A first-order expansion. Its gain bounds are expressed in
terms of the actual module-relative errors. In particular, none of the four
source epsilons and no final Theorem 3.1 inequality is stored here. -/
structure P19StaticAppendixAExpansion {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) where
  computationContribution : P19Vector n
  rhsContribution : P19Vector n
  gmresContribution : P19Vector n
  solutionContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (family.iteration k).xHat - family.system.xExact =
      computationContribution + rhsContribution + gmresContribution +
        solutionContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 family.system.xExact)
  computation_gain_bound :
    p19VecNorm2 computationContribution /
          p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticAlpha MR MRinv q *
          p19SafeRelativeMagnitude
            (p19FrobNorm (family.iteration k).deltaC)
            (p19FrobNorm
              (p19StaticExactC family.system
                (family.basisFamily.basis k.1))))
  rhs_gain_bound :
    p19VecNorm2 rhsContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaB)
            (p19VecNorm2 (p19StaticExactB family.system)))
  gmres_gain_bound :
    p19VecNorm2 gmresContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q * (family.iteration k).ug)
  solution_gain_bound :
    p19VecNorm2 solutionContribution /
          p19VecNorm2 family.system.xExact ≤
      p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticLambda family.system MR MRinv *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaX)
            (p19VecNorm2
              (p19RectMatVec (family.basisFamily.basis k.1)
                (family.iteration k).yHat)))

/-- The reusable Appendix-A analysis invoked by Theorem 3.1. It is uniform in
the dimension and right preconditioner and supplies only the raw expansion
above, not a selected dimension or the theorem's collected bound. -/
structure P19StaticAppendixATheory {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  rightQuantities : ∀ (k : P19Theorem31Dimension n)
      (MR MRinv : P19Matrix n), p19InversePair MR MRinv →
    P19StaticRightQuantities family k MR MRinv
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) →
    P19Algorithm2Conditions (family.iteration k) →
    ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
      P19StaticAppendixAExpansion family k MR MRinv
        (rightQuantities k MR MRinv hMR)

/-- Paper-scoped exact matrix operator 2-norm. -/
noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

/-- Paper-scoped condition-number product for a matrix and inverse candidate. -/
noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

/-- The initial residual used when Algorithm 1 is read as Algorithm 2 applied
to the correction equation. -/
noncomputable def p19InitialResidual {n : ℕ} (A : P19Matrix n)
    (b xInitial : P19Vector n) : P19Vector n :=
  b - p19MatVec A xInitial

/-- Componentwise absolute matrix-vector product from equation (3.15). -/
noncomputable def p19AbsRectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, |A i j| * |x j|

/-- A nonsingular system with one fixed, nonsingular, nonidentity right
preconditioner. The product-inverse certificate prevents condition numbers
from being formed from unrelated matrices. -/
structure P19FixedRightSystem (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  MR : P19Matrix n
  MRinv : P19Matrix n
  A_inverse : p19InversePair A Ainv
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul A MRinv) (p19SquareRectMul MR Ainv)
  right_preconditioner_nontrivial : MR ≠ 1
  b : P19Vector n
  xExact : P19Vector n
  xInitial : P19Vector n
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  initial_residual_nonzero : p19InitialResidual A b xInitial ≠ 0

/-- The actual right-preconditioned operator `A M_R^{-1}`. -/
noncomputable def p19RightOperator {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.A system.MRinv

/-- The certified inverse `M_R A^{-1}` of the right-preconditioned operator. -/
noncomputable def p19RightOperatorInverse {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.MR system.Ainv

/-- Induced-2 condition number of `A M_R^{-1}`. -/
noncomputable def p19RightOperatorKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 (p19RightOperator system) (p19RightOperatorInverse system)

/-- Induced-2 condition number of the fixed right preconditioner. -/
noncomputable def p19RightPreconditionerKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.MR system.MRinv

/-- Induced-2 condition number of the original system matrix. -/
noncomputable def p19SystemKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.A system.Ainv

/-- The five-term maximum in condition (3.16). -/
noncomputable def p19Condition316Value {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19RightOperatorKappa2 system)
    (max (ug * p19RightPreconditionerKappa2 system)
      (max (um * etaR * p19RightPreconditionerKappa2 system)
        (max (ua * p19SystemKappa2 system * rhoAR)
          (ua * p19RightOperatorKappa2 system *
            p19RightPreconditionerKappa2 system))))

/-- The three first-order sources in the right-preconditioned bound (3.17). -/
noncomputable def p19RightAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    um * etaR * p19RightPreconditionerKappa2 system +
      ua * p19SystemKappa2 system * rhoAR

/-- The two first-order sources in the flexible-preconditioned bound (3.20). -/
noncomputable def p19FlexibleAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    ua * p19SystemKappa2 system * rhoAR

/-- A computed right-preconditioned MGS-GMRES transcript through the least-
squares stage. It records (3.14), the products with `A`, equation (3.15), and
the complete condition (3.16). -/
structure P19FixedRightGMRESRun {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  ug : ι → ℝ
  um : ι → ℝ
  ua : ι → ℝ
  etaR : ι → ℝ
  rhoAR : ι → ℝ
  parameters_nonneg : ∀ t,
    0 ≤ ug t ∧ 0 ≤ um t ∧ 0 ≤ ua t ∧ 0 ≤ etaR t ∧ 0 ≤ rhoAR t
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  zHat : ι → P19RectMatrix n keyDimension
  computedAZ : ι → P19RectMatrix n keyDimension
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_relation : ∀ t,
    p19Augment (p19InitialResidual system.A system.b system.xInitial)
        (computedAZ t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedAZ t + leastSquaresDeltaC t)
      (p19InitialResidual system.A system.b system.xInitial +
        leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column
            (p19Augment
              (p19InitialResidual system.A system.b system.xInitial)
              (computedAZ t)) j)
  zHat_full_rank : ∀ t, p19FullColumnRank (zHat t)
  preconditionerDelta : ι → Fin keyDimension → P19Matrix n
  preconditioner_application : ∀ t j,
    p19Column (zHat t) j =
      p19MatVec (system.MRinv + preconditionerDelta t j)
        (p19Column (vHat t) j)
  preconditioner_error_bound : ∀ t j,
    p19FrobNorm (preconditionerDelta t j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        um t * etaR t * p19FrobNorm system.MRinv
  matrixDelta : ι → Fin keyDimension → P19Matrix n
  matrix_application : ∀ t j,
    p19Column (computedAZ t) j =
      p19MatVec (system.A + matrixDelta t j) (p19Column (zHat t) j)
  matrix_error_bound : ∀ t j i q,
    |matrixDelta t j i q| ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        ua t * |system.A i q|
  rho_denominator_pos : ∀ t,
    0 < p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  rho_equation : ∀ t,
    rhoAR t =
      p19VecNorm2 (p19AbsRectMatVec (zHat t) (yHat t)) /
        p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  condition316 :
    p19MuchLessThanOneAt l (fun t ↦
      p19Condition316Value system (ug t) (um t) (ua t) (etaR t) (rhoAR t))

/-- Right-preconditioned line 4: form `V_hat y_hat` in precision `u_g` and
then apply the fixed right preconditioner again in precision `u_m`. -/
structure P19RightGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  solutionPreconditionerDelta : ι → P19Matrix n
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.vHat t i j|
  solution_preconditioner_error_bound : ∀ t,
    p19FrobNorm (solutionPreconditionerDelta t) ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.um t * run.etaR t * p19FrobNorm system.MRinv
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19MatVec (system.MRinv + solutionPreconditionerDelta t)
        (p19RectMatVec (run.vHat t + solutionBasisDelta t) (run.yHat t)))

/-- Flexible line 4: reuse the stored preconditioned basis and form
`Z_hat y_hat` directly in precision `u_g`, with no fresh preconditioner
application. -/
structure P19FlexibleGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.zHat t i j|
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19RectMatVec (run.zHat t + solutionBasisDelta t) (run.yHat t))

/-- Appendix-C contribution certificate. Each first-order contribution is
linked to the perturbation family that generates it; the final three-term
forward-error inequality is not stored. -/
structure P19RightForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19RightGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  reapplicationPropagation : ι → P19Matrix n → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  reapplicationContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  reapplication_link : ∀ t,
    reapplicationContribution t =
      reapplicationPropagation t (algorithm.solutionPreconditionerDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  reapplicationPropagation_zero : ∀ t, reapplicationPropagation t 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + reapplicationContribution t +
        matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  reapplication_bound : ∀ t,
    p19VecNorm2 (reapplicationContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.um t * run.etaR t * p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- Appendix-D contribution certificate for flexible GMRES. Its first-order
decomposition has no preconditioner-reapplication contribution. -/
structure P19FlexibleForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19FlexibleGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- A proof-carrying right-preconditioned execution of Theorem 3.3. -/
structure P19RightTheorem33Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19RightGMRESRun run
  analysis : P19RightForwardAnalysis algorithm

/-- A proof-carrying fixed-preconditioner flexible execution of Theorem 3.4. -/
structure P19FlexibleTheorem34Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19FlexibleGMRESRun run
  analysis : P19FlexibleForwardAnalysis algorithm

/-- The two square-matrix condition-number readings that Section 2 explicitly
allows when it subsequently writes an unqualified `kappa`. -/
inductive P19StaticSquareKappaChoice where
  | frobenius
  | inducedTwo

/-- A source-authorized interpretation of an unqualified square condition
number. The inverse argument remains attached to the matrix it inverts. -/
noncomputable def p19StaticKappa (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) : ℝ :=
  match choice with
  | .frobenius => p19ConditionNumberF A Ainv
  | .inducedTwo => p19Kappa2 A Ainv

/-- One fixed nonsingular right preconditioner for a static Algorithm 2
family. The two identity equations express `M_L = I`. -/
structure P19StaticFixedRightPreconditioner {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  MR : P19Matrix n
  MRinv : P19Matrix n
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul family.system.A MRinv)
      (p19SquareRectMul MR family.system.Ainv)
  nontrivial : MR ≠ 1
  left_preconditioner_identity : family.system.ML = 1
  left_preconditioner_inverse_identity : family.system.MLinv = 1

/-- The condition number of the original matrix in Theorems 3.3-3.4. -/
noncomputable def p19StaticSystemKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) : ℝ :=
  p19StaticKappa choice family.system.A family.system.Ainv

/-- The condition number of the fixed right preconditioner. -/
noncomputable def p19StaticRightPreconditionerKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice preconditioner.MR preconditioner.MRinv

/-- The condition number of `A M_R^{-1}`. -/
noncomputable def p19StaticRightOperatorKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice
    (p19SquareRectMul family.system.A preconditioner.MRinv)
    (p19SquareRectMul preconditioner.MR family.system.Ainv)

/-- The complete five-entry maximum in condition (3.16), with no numerical
threshold added to the paper's qualitative smallness notation. -/
noncomputable def p19StaticCondition316Value
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19StaticRightOperatorKappa choice preconditioner)
    (max (ug * p19StaticRightPreconditionerKappa choice preconditioner)
      (max (um * etaR *
          p19StaticRightPreconditionerKappa choice preconditioner)
        (max (ua * p19StaticSystemKappa choice family * rhoAR)
          (ua * p19StaticRightOperatorKappa choice preconditioner *
            p19StaticRightPreconditionerKappa choice preconditioner))))

/-- The three source terms in equation (3.17). -/
noncomputable def p19StaticRightAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    um * etaR * p19StaticRightPreconditionerKappa choice preconditioner +
      ua * p19StaticSystemKappa choice family * rhoAR

/-- The two source terms in equation (3.20). -/
noncomputable def p19StaticFlexibleAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    ua * p19StaticSystemKappa choice family * rhoAR

/-- Raw fixed-preconditioner data shared by the right and flexible paths at
one dimension. The inaccessible basis is linked by (C.2); no error bound or
attainable dimension is stored. -/
structure P19StaticFixedRightCore {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  ug : ℝ
  um : ℝ
  ua : ℝ
  etaR : ℝ
  rhoAR : ℝ
  zHat : P19RectMatrix n k.1
  preconditionerDelta : Fin k.1 → P19Matrix n
  preconditioner_application : ∀ j,
    p19Column zHat j =
      p19MatVec (preconditioner.MRinv + preconditionerDelta j)
        (p19Column (family.iteration k).vHat j)
  matrixDelta : Fin k.1 → P19Matrix n
  matrix_application : ∀ j,
    p19Column (family.iteration k).computedC j =
      p19MatVec (family.system.A + matrixDelta j) (p19Column zHat j)
  search_space_equation : ∀ j,
    p19Column (family.basisFamily.basis k.1) j =
      p19Column zHat j +
        p19MatVec family.system.Ainv
          (p19MatVec (matrixDelta j) (p19Column zHat j))
  computation_exact : (family.iteration k).deltaC = 0
  computation_accuracy_zero : (family.iteration k).epsilonC = 0
  rhs_exact : (family.iteration k).deltaB = 0
  rhs_accuracy_zero : (family.iteration k).epsilonB = 0
  gmresMagnitude : ℝ
  basisPreconditionerMagnitude : ℝ
  matrixMagnitude : ℝ

/-- The source models (3.14), (C.1), (3.15), the MGS/Givens perturbation,
and the full qualitative condition (3.16) at one candidate dimension. These
bound actual perturbations, not propagated forward-error contributions. -/
structure P19StaticFixedRightCoreConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (core : P19StaticFixedRightCore family preconditioner k) where
  parameters_nonneg :
    0 ≤ core.ug ∧ 0 ≤ core.um ∧ 0 ≤ core.ua ∧ 0 ≤ core.etaR ∧
      0 ≤ core.rhoAR
  magnitudes_nonneg :
    0 ≤ core.gmresMagnitude ∧ 0 ≤ core.basisPreconditionerMagnitude ∧
      0 ≤ core.matrixMagnitude
  least_squares_solution :
    p19IsLeastSquaresSolution
      ((family.iteration k).computedC +
        (family.iteration k).leastSquaresDeltaC)
      ((family.iteration k).computedB +
        (family.iteration k).leastSquaresDeltaB)
      (family.iteration k).yHat
  least_squares_error_covered : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment (family.iteration k).leastSquaresDeltaB
            (family.iteration k).leastSquaresDeltaC) j) ≤
      core.gmresMagnitude *
        p19VecNorm2
          (p19Column
            (p19Augment (family.iteration k).computedB
              (family.iteration k).computedC) j)
  basis_preconditioner_error_covered : ∀ j,
    p19FrobNorm (core.preconditionerDelta j) ≤
      core.basisPreconditionerMagnitude * p19FrobNorm preconditioner.MRinv
  matrix_error_covered : ∀ j i q,
    |core.matrixDelta j i q| ≤ core.matrixMagnitude * |family.system.A i q|
  gmres_magnitude_bound :
    core.gmresMagnitude ≤ (family.iteration k).dimensionFactor * core.ug
  basis_preconditioner_magnitude_bound :
    core.basisPreconditionerMagnitude ≤
      (family.iteration k).dimensionFactor * core.um * core.etaR
  matrix_magnitude_bound :
    core.matrixMagnitude ≤ (family.iteration k).dimensionFactor * core.ua
  rho_denominator_pos :
    0 < p19VecNorm2
      (p19RectMatVec core.zHat (family.iteration k).yHat)
  rho_equation :
    core.rhoAR =
      p19VecNorm2 (p19AbsRectMatVec core.zHat (family.iteration k).yHat) /
        p19VecNorm2 (p19RectMatVec core.zHat (family.iteration k).yHat)
  condition316 :
    semantics.small
      (p19StaticCondition316Value choice preconditioner
        core.ug core.um core.ua core.etaR core.rhoAR)

/-- Right-preconditioned solution formation: a product with `V_hat` followed
by a fresh application of `M_R^{-1}`. -/
structure P19StaticRightIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solutionPreconditionerDelta : P19Matrix n
  solution_equation :
    (family.iteration k).xHat =
      p19MatVec (preconditioner.MRinv + solutionPreconditionerDelta)
        (p19RectMatVec
          ((family.iteration k).vHat + solutionBasisDelta)
          (family.iteration k).yHat)
  reapplicationMagnitude : ℝ

/-- Fixed-precision source error bounds for right solution formation. -/
structure P19StaticRightConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticRightIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  reapplication_magnitude_nonneg : 0 ≤ iteration.reapplicationMagnitude
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |(family.iteration k).vHat i j|
  solution_preconditioner_error_covered :
    p19FrobNorm iteration.solutionPreconditionerDelta ≤
      iteration.reapplicationMagnitude * p19FrobNorm preconditioner.MRinv
  reapplication_magnitude_bound :
    iteration.reapplicationMagnitude ≤
      (family.iteration k).dimensionFactor *
        iteration.core.um * iteration.core.etaR

/-- Flexible solution formation: a direct product with the persistently stored
computed basis `Z_hat`, with no fresh preconditioner application. -/
structure P19StaticFlexibleIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solution_equation :
    (family.iteration k).xHat =
      p19RectMatVec (core.zHat + solutionBasisDelta)
        (family.iteration k).yHat

/-- Fixed-precision source error bounds for flexible solution formation. -/
structure P19StaticFlexibleConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticFlexibleIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |iteration.core.zHat i j|

/-- Static right-preconditioned executions at all admissible dimensions. -/
structure P19StaticRightFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticRightIteration family preconditioner k

/-- Static fixed-preconditioner flexible executions at all admissible
dimensions. -/
structure P19StaticFlexibleFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticFlexibleIteration family preconditioner k

/-- Raw Appendix-C propagation at one dimension. The gains multiply actual
source-error magnitudes; neither `c(n,k)` nor (3.17) is stored. -/
structure P19StaticRightAppendixCExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  reapplicationContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (right.family.iteration k).xHat - right.family.system.xExact =
      gmresContribution + reapplicationContribution + matrixContribution +
        remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 right.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice right.preconditioner *
          p19StaticRightPreconditionerKappa choice right.preconditioner
  reapplication_gain_bound :
    p19VecNorm2 reapplicationContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).reapplicationMagnitude *
        p19StaticRightPreconditionerKappa choice right.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR

/-- Raw Appendix-D propagation at one dimension. It has no reapplication
contribution and stores neither `c(n,k)` nor (3.20). -/
structure P19StaticFlexibleAppendixDExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (flexible.family.iteration k).xHat - flexible.family.system.xExact =
      gmresContribution + matrixContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 flexible.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice flexible.preconditioner *
          p19StaticRightPreconditionerKappa choice flexible.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice flexible.family *
          (flexible.iteration k).core.rhoAR

/-- Uniform Appendix-C dependency. It receives the MGS-selected dimension and
the source conditions and supplies only the raw propagation above. -/
structure P19StaticRightAppendixCTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (right.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (right.family.iteration k)) →
    P19StaticRightConditions choice (right.iteration k) →
      P19StaticRightAppendixCExpansion choice right k

/-- Uniform Appendix-D dependency, again without a selected dimension or the
collected theorem bound. -/
structure P19StaticFlexibleAppendixDTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (flexible.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (flexible.family.iteration k)) →
    P19StaticFlexibleConditions choice (flexible.iteration k) →
      P19StaticFlexibleAppendixDExpansion choice flexible k

end HighamBench
```
