# Declaration dossier for P19-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t3_right_flexible_attainable_forward_error
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (system : P19FixedRightSystem n)
    (right : P19RightTheorem33Execution system l)
    (flexible : P19FlexibleTheorem34Execution system l) :
    (∃ k : ℕ,
      k = right.run.keyDimension ∧ 0 < k ∧ k ≤ n ∧
        p19FirstOrderLeAt l
          (fun t ↦ p19Condition316Value system
            (right.run.ug t) (right.run.um t) (right.run.ua t)
            (right.run.etaR t) (right.run.rhoAR t))
          (fun t ↦ p19ForwardError system.xExact (right.algorithm.xHat t))
          (fun t ↦
            p19PolynomialFactorValue right.run.polynomialFactor n k *
              p19RightAttainableEnvelope system
                (right.run.ug t) (right.run.um t) (right.run.ua t)
                (right.run.etaR t) (right.run.rhoAR t))) ∧
      (∃ k : ℕ,
        k = flexible.run.keyDimension ∧ 0 < k ∧ k ≤ n ∧
          p19FirstOrderLeAt l
            (fun t ↦ p19Condition316Value system
              (flexible.run.ug t) (flexible.run.um t) (flexible.run.ua t)
              (flexible.run.etaR t) (flexible.run.rhoAR t))
            (fun t ↦
              p19ForwardError system.xExact (flexible.algorithm.xHat t))
            (fun t ↦
              p19PolynomialFactorValue flexible.run.polynomialFactor n k *
                p19FlexibleAttainableEnvelope system
                  (flexible.run.ug t) (flexible.run.ua t)
                  (flexible.run.rhoAR t))) ∧
        ∀ t,
          p19RightAttainableEnvelope system
              (right.run.ug t) (right.run.um t) (right.run.ua t)
              (right.run.etaR t) (right.run.rhoAR t) =
            p19FlexibleAttainableEnvelope system
                (right.run.ug t) (right.run.ua t) (right.run.rhoAR t) +
              right.run.um t * right.run.etaR t *
                p19RightPreconditionerKappa2 system
```

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (system : HighamBench.P19FixedRightSystem n)
  (right : HighamBench.P19RightTheorem33Execution system l)
  (flexible : HighamBench.P19FlexibleTheorem34Execution system l),
  And
    (Exists fun k =>
      And (Eq k right.run.keyDimension)
        (And (instLTNat.lt 0 k)
          (And (instLENat.le k n)
            (HighamBench.p19FirstOrderLeAt l
              (fun t =>
                HighamBench.p19Condition316Value system (right.run.ug t) (right.run.um t) (right.run.ua t)
                  (right.run.etaR t) (right.run.rhoAR t))
              (fun t => HighamBench.p19ForwardError system.xExact (right.algorithm.xHat t)) fun t =>
              instHMul.hMul (HighamBench.p19PolynomialFactorValue right.run.polynomialFactor n k)
                (HighamBench.p19RightAttainableEnvelope system (right.run.ug t) (right.run.um t) (right.run.ua t)
                  (right.run.etaR t) (right.run.rhoAR t))))))
    (And
      (Exists fun k =>
        And (Eq k flexible.run.keyDimension)
          (And (instLTNat.lt 0 k)
            (And (instLENat.le k n)
              (HighamBench.p19FirstOrderLeAt l
                (fun t =>
                  HighamBench.p19Condition316Value system (flexible.run.ug t) (flexible.run.um t) (flexible.run.ua t)
                    (flexible.run.etaR t) (flexible.run.rhoAR t))
                (fun t => HighamBench.p19ForwardError system.xExact (flexible.algorithm.xHat t)) fun t =>
                instHMul.hMul (HighamBench.p19PolynomialFactorValue flexible.run.polynomialFactor n k)
                  (HighamBench.p19FlexibleAttainableEnvelope system (flexible.run.ug t) (flexible.run.ua t)
                    (flexible.run.rhoAR t))))))
      (∀ (t : ι),
        Eq
          (HighamBench.p19RightAttainableEnvelope system (right.run.ug t) (right.run.um t) (right.run.ua t)
            (right.run.etaR t) (right.run.rhoAR t))
          (instHAdd.hAdd
            (HighamBench.p19FlexibleAttainableEnvelope system (right.run.ug t) (right.run.ua t) (right.run.rhoAR t))
            (instHMul.hMul (instHMul.hMul (right.run.um t) (right.run.etaR t))
              (HighamBench.p19RightPreconditionerKappa2 system)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l] (system : HighamBench.P19FixedRightSystem n)
  (right : @HighamBench.P19RightTheorem33Execution.{u_1} n ι system l)
  (flexible : @HighamBench.P19FlexibleTheorem34Execution.{u_1} n ι system l),
  And
    (@Exists.{1} Nat fun (k : Nat) =>
      And
        (@Eq.{1} Nat k
          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l
            (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right)))
        (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
          (And (@LE.le.{0} Nat instLENat k n)
            (@HighamBench.p19FirstOrderLeAt.{u_1} ι l
              (fun (t : ι) =>
                @HighamBench.p19Condition316Value n system
                  (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t))
              (fun (t : ι) =>
                @HighamBench.p19ForwardError n (@HighamBench.P19FixedRightSystem.xExact n system)
                  (@HighamBench.P19RightGMRESRun.xHat.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right)
                    (@HighamBench.P19RightTheorem33Execution.algorithm.{u_1} n ι system l right) t))
              fun (t : ι) =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.p19PolynomialFactorValue
                  (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right))
                  n k)
                (@HighamBench.p19RightAttainableEnvelope n system
                  (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                  (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
                    (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t))))))
    (And
      (@Exists.{1} Nat fun (k : Nat) =>
        And
          (@Eq.{1} Nat k
            (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l
              (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible)))
          (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (And (@LE.le.{0} Nat instLENat k n)
              (@HighamBench.p19FirstOrderLeAt.{u_1} ι l
                (fun (t : ι) =>
                  @HighamBench.p19Condition316Value n system
                    (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t))
                (fun (t : ι) =>
                  @HighamBench.p19ForwardError n (@HighamBench.P19FixedRightSystem.xExact n system)
                    (@HighamBench.P19FlexibleGMRESRun.xHat.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible)
                      (@HighamBench.P19FlexibleTheorem34Execution.algorithm.{u_1} n ι system l flexible) t))
                fun (t : ι) =>
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (HighamBench.p19PolynomialFactorValue
                    (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible))
                    n k)
                  (@HighamBench.p19FlexibleAttainableEnvelope n system
                    (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t)
                    (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
                      (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l flexible) t))))))
      (∀ (t : ι),
        @Eq.{1} Real
          (@HighamBench.p19RightAttainableEnvelope n system
            (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
              (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
            (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l
              (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
            (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
              (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
            (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l
              (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
            (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
              (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HighamBench.p19FlexibleAttainableEnvelope n system
              (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l
                (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
              (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l
                (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
              (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l
                (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l
                  (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t)
                (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l
                  (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l right) t))
              (@HighamBench.p19RightPreconditionerKappa2 n system)))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P19FixedRightGMRESRun.etaR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bb6b568cad87c0894eb9db3301e79ed27752357b7b6b3ffe9bb1d90546f5e53`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.8
```

### D002: `HighamBench.P19FixedRightGMRESRun.keyDimension`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `60ebe14199e18b46335bad478b8a9b8482c4a370b9bd45c171279354c0e80db3`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} → {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → Nat
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.1
```

### D003: `HighamBench.P19FixedRightGMRESRun.polynomialFactor`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0f646faf759b1dd0c68ad7b902fdc34a6552652322373bd39cf603e1c02e0b3a`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → HighamBench.P19PolynomialFactor
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → HighamBench.P19PolynomialFactor
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.4
```

### D004: `HighamBench.P19FixedRightGMRESRun.rhoAR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `61198c438e00d6f99aeccdfec9f7701e91c49eff3d27c2eb998d39ebd92ec1df`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.9
```

### D005: `HighamBench.P19FixedRightGMRESRun.ua`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0c9f2d8081119fc3127eb3f069dfedd3d90b2da2b41b3f93a4a6180850792475`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.7
```

### D006: `HighamBench.P19FixedRightGMRESRun.ug`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ddc07870aedade0990509321f9f2e034e9811c440f6652ed403e30765869658c`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.5
```

### D007: `HighamBench.P19FixedRightGMRESRun.um`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a04ae25c53e9f26177029627435f85648eda57f8e90a4789a968b3344469637d`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.6
```

### D008: `HighamBench.P19FixedRightSystem`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9c79b1f7a3a87ddba4b71d89eb2a7f7f39a1dba1c1d70e7c0db62e2e88ab137d`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D009: `HighamBench.P19FixedRightSystem.xExact`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9153c78ea5e26ae6132867e7d01d0b24fece3f69e4c21677654db82b0f47f4d5`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D010: `HighamBench.P19FlexibleGMRESRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b580ae1dc4034e9fdd1a4e3202eb8f1aeaa0255cfb2fa03272c2907bfc243d85`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          HighamBench.P19FlexibleGMRESRun run → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (self : @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l run self => self.2
```

### D011: `HighamBench.P19FlexibleTheorem34Execution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `6fa09eadc21044c4b927ac4ce89c69e4ecb3f0d84cc16c0a12fd40629ed975da`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P19FixedRightSystem n → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (system : HighamBench.P19FixedRightSystem n) → (l : Filter.{u_1} ι) → Type u_1
```

### D012: `HighamBench.P19FlexibleTheorem34Execution.algorithm`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9c557c260811c1a7821d2782b76d599a201758471b215ed67f2e7d2a21256253`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (self : HighamBench.P19FlexibleTheorem34Execution system l) → HighamBench.P19FlexibleGMRESRun self.run
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FlexibleTheorem34Execution.{u_1} n ι system l) →
          @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l
            (@HighamBench.P19FlexibleTheorem34Execution.run.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.2
```

### D013: `HighamBench.P19FlexibleTheorem34Execution.run`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bb8f790e523177c8d7a1b832d126b5c657a5b0e7634611c62224dce7f4e3ab5`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FlexibleTheorem34Execution system l → HighamBench.P19FixedRightGMRESRun system l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FlexibleTheorem34Execution.{u_1} n ι system l) →
          @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.1
```

### D014: `HighamBench.P19RightGMRESRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b5de6f15deb47f95052e642cadcd6d820e9441acffe8e1e0ea072f828c6f996f`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          HighamBench.P19RightGMRESRun run → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (self : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l run self => self.3
```

### D015: `HighamBench.P19RightTheorem33Execution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2dc29d99b4d6bc9c7e8d702c1904c92af997d18a5500969bb636d841e894817d`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P19FixedRightSystem n → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (system : HighamBench.P19FixedRightSystem n) → (l : Filter.{u_1} ι) → Type u_1
```

### D016: `HighamBench.P19RightTheorem33Execution.algorithm`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `aa1b124f12a776ba8762dacf0239a2b58f330d22b47256c059cf2134d58a3d41`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → (self : HighamBench.P19RightTheorem33Execution system l) → HighamBench.P19RightGMRESRun self.run
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19RightTheorem33Execution.{u_1} n ι system l) →
          @HighamBench.P19RightGMRESRun.{u_1} n ι system l
            (@HighamBench.P19RightTheorem33Execution.run.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.2
```

### D017: `HighamBench.P19RightTheorem33Execution.run`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d45387b3ef6b54d31b635dcf6dfbb8ad00fc6b657054f0da205a85046aaa866c`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19RightTheorem33Execution system l → HighamBench.P19FixedRightGMRESRun system l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19RightTheorem33Execution.{u_1} n ι system l) →
          @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.1
```

### D018: `HighamBench.p19Condition316Value`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6bfbe331fe2095d80118922861f801903b91c4ca09e7a5974e602fdad3f539dd`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → (ug um ua etaR rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system ug um ua etaR rhoAR =>
  Real.instMax.max (instHMul.hMul ug (HighamBench.p19RightOperatorKappa2 system))
    (Real.instMax.max (instHMul.hMul ug (HighamBench.p19RightPreconditionerKappa2 system))
      (Real.instMax.max (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19RightPreconditionerKappa2 system))
        (Real.instMax.max (instHMul.hMul (instHMul.hMul ua (HighamBench.p19SystemKappa2 system)) rhoAR)
          (instHMul.hMul (instHMul.hMul ua (HighamBench.p19RightOperatorKappa2 system))
            (HighamBench.p19RightPreconditionerKappa2 system)))))
```

### D019: `HighamBench.p19FirstOrderLeAt`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `762c7d3a1b43802433562110427d7f354a4212f105bf0df6b4094874cda3499e`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale lhs rhs : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (HighamBench.p19SecondOrderAt l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D020: `HighamBench.p19FlexibleAttainableEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `17170d61398ef538ce230a790ef08a324a031e3b0209a5859e757a7716c3775c`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real → Real → Real → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → (ug ua rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system ug ua rhoAR =>
  instHAdd.hAdd
    (instHMul.hMul (instHMul.hMul ug (HighamBench.p19RightOperatorKappa2 system))
      (HighamBench.p19RightPreconditionerKappa2 system))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19SystemKappa2 system)) rhoAR)
```

### D021: `HighamBench.p19ForwardError`

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

### D022: `HighamBench.p19PolynomialFactorValue`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e32297e66203da021d9ce43ebf603a182f9ddfad04cfab209bfb4f1246022f1d`

Type:

```lean
HighamBench.P19PolynomialFactor → Nat → Nat → Real
```

Fully explicit type:

```lean
(c : HighamBench.P19PolynomialFactor) → (n k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun c n k =>
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      instHMul.hMul (instHMul.hMul (c.coefficient i j) (instHPow.hPow n.cast i.val)) (instHPow.hPow k.cast j.val)
```

### D023: `HighamBench.p19RightAttainableEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `615c27648878318b90048d28c32aae073402922d6a5d83afa9e5bcc173c4d86e`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → (ug um ua etaR rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system ug um ua etaR rhoAR =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHMul.hMul (instHMul.hMul ug (HighamBench.p19RightOperatorKappa2 system))
        (HighamBench.p19RightPreconditionerKappa2 system))
      (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19RightPreconditionerKappa2 system)))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19SystemKappa2 system)) rhoAR)
```

### D024: `HighamBench.p19RightPreconditionerKappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `71ccf5c8d2d90720829c680b4fcfb0993e9eeee9d78778b8650408c0971e1ad4`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19Kappa2 system.MR system.MRinv
```

### D025: `HighamBench.P19FixedRightGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cb1ee14be982ad9cdadc1075c203108445f60511680d2c75800c000e60a3192f`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P19FixedRightSystem n → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (system : HighamBench.P19FixedRightSystem n) → (l : Filter.{u_1} ι) → Type u_1
```

### D026: `HighamBench.P19FixedRightSystem.MR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8657d968051855c860c30b1ef64a8b39b82cfb12295b32535e7ca77043cd2c76`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D027: `HighamBench.P19FixedRightSystem.MRinv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9bfb6d215b5c5cb15ac786f3574be24e060995864ec155526b76f2065db5bc8d`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D028: `HighamBench.P19FixedRightSystem.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `b760f6fe4b8c6436c7b711d0624adc050b9bf8d16fde5f49d437ffed5a90b316`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv MR MRinv : HighamBench.P19Matrix n) →
      HighamBench.p19InversePair A Ainv →
        HighamBench.p19InversePair MR MRinv →
          HighamBench.p19InversePair (HighamBench.p19SquareRectMul A MRinv) (HighamBench.p19SquareRectMul MR Ainv) →
            Ne MR 1 →
              (b xExact xInitial : HighamBench.P19Vector n) →
                Ne b 0 →
                  Eq (HighamBench.p19MatVec A xExact) b →
                    Ne (HighamBench.p19InitialResidual A b xInitial) 0 → HighamBench.P19FixedRightSystem n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (A Ainv MR MRinv : HighamBench.P19Matrix n) →
      (A_inverse : @HighamBench.p19InversePair n A Ainv) →
        (MR_inverse : @HighamBench.p19InversePair n MR MRinv) →
          (right_operator_inverse :
              @HighamBench.p19InversePair n (@HighamBench.p19SquareRectMul n n A MRinv)
                (@HighamBench.p19SquareRectMul n n MR Ainv)) →
            (right_preconditioner_nontrivial :
                @Ne.{1} (HighamBench.P19Matrix n) MR
                  (@OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 1)
                    (@One.toOfNat1.{0} (HighamBench.P19Matrix n)
                      (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne)))) →
              (b xExact xInitial : HighamBench.P19Vector n) →
                (b_nonzero :
                    @Ne.{1} (HighamBench.P19Vector n) b
                      (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                        (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                          (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero)))) →
                  (exact_solution : @Eq.{1} (HighamBench.P19Vector n) (@HighamBench.p19MatVec n A xExact) b) →
                    (initial_residual_nonzero :
                        @Ne.{1} (HighamBench.P19Vector n) (@HighamBench.p19InitialResidual n A b xInitial)
                          (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                              (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                Real.instZero)))) →
                      HighamBench.P19FixedRightSystem n
```

### D029: `HighamBench.P19FlexibleGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `50e9ac82f18dc0b6024f82ef225988bf00bdb173245b09a63358500912aa8adc`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → Type u_1
```

### D030: `HighamBench.P19FlexibleTheorem34Execution.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `eb0e3f73ee3ef8586659739c292260b39ee73526b30daa3aeb2d96d305a5e715`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (run : HighamBench.P19FixedRightGMRESRun system l) →
          (algorithm : HighamBench.P19FlexibleGMRESRun run) →
            HighamBench.P19FlexibleForwardAnalysis algorithm → HighamBench.P19FlexibleTheorem34Execution system l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          (algorithm : @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run) →
            (analysis : @HighamBench.P19FlexibleForwardAnalysis.{u_1} n ι system l run algorithm) →
              @HighamBench.P19FlexibleTheorem34Execution.{u_1} n ι system l
```

### D031: `HighamBench.P19PolynomialFactor`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a277c56923b73b8cbd2ff65bc6ad14878794606b603837ef0396952b58e944d9`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D032: `HighamBench.P19PolynomialFactor.coefficient`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9621c065f238974bb2a7f1cd1fe45a52c03304d6ef88994300d1147e3391dbdc`

Type:

```lean
(self : HighamBench.P19PolynomialFactor) →
  Fin (instHAdd.hAdd self.degreeN 1) → Fin (instHAdd.hAdd self.degreeK 1) → Real
```

Fully explicit type:

```lean
(self : HighamBench.P19PolynomialFactor) →
  Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (HighamBench.P19PolynomialFactor.degreeN self)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (HighamBench.P19PolynomialFactor.degreeK self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D033: `HighamBench.P19PolynomialFactor.degreeK`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a01c1f807284de44bbe07bbd3a2d026399a18a1fbba970fb07b404a97a078f97`

Type:

```lean
HighamBench.P19PolynomialFactor → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P19PolynomialFactor) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D034: `HighamBench.P19PolynomialFactor.degreeN`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `747b227a49e80a41dfe67147163421d6a73f878c21d1a01b7b51e6c425ff7a6f`

Type:

```lean
HighamBench.P19PolynomialFactor → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P19PolynomialFactor) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D035: `HighamBench.P19RightGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `b7dfbb385e5c06452c0d643c848f305a8920f6b8aeabf85f65718329c92f83df`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} → (run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → Type u_1
```

### D036: `HighamBench.P19RightTheorem33Execution.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `942f8743948675f00fa39713c9ddd2ecc8fb5a1ec9487e9d9386366ab8ea90e1`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (run : HighamBench.P19FixedRightGMRESRun system l) →
          (algorithm : HighamBench.P19RightGMRESRun run) →
            HighamBench.P19RightForwardAnalysis algorithm → HighamBench.P19RightTheorem33Execution system l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          (algorithm : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run) →
            (analysis : @HighamBench.P19RightForwardAnalysis.{u_1} n ι system l run algorithm) →
              @HighamBench.P19RightTheorem33Execution.{u_1} n ι system l
```

### D037: `HighamBench.P19Vector`

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

### D038: `HighamBench.p19Kappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b9e5fd26e72448c1ee9298822e9b5726faff2cf4d27bb54e9c9330a2aa739b35`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (HighamBench.p19OpNorm2 A) (HighamBench.p19OpNorm2 Ainv)
```

### D039: `HighamBench.p19RightOperatorKappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1c56f91ff7c0c40463f6e34f856e2821660d939d7e468b721157407cc091d642`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system =>
  HighamBench.p19Kappa2 (HighamBench.p19RightOperator system) (HighamBench.p19RightOperatorInverse system)
```

### D040: `HighamBench.p19SecondOrderAt`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `be18d1baa6a2642eef71fd1188d02fbf532849ff793b47048d71b3ff31a20335`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale remainder : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
```

### D041: `HighamBench.p19SystemKappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cf2a13576c0b95fb31efdf4663667b5f81c859bbf2da2b2c3364daa0f6c583ad`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → Real
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19Kappa2 system.A system.Ainv
```

### D042: `HighamBench.p19VecNorm2`

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

### D043: `HighamBench.P19FixedRightGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7c1511e05ca0c640ba4879d7be96714d86570c3eee6d750e6828d9da17506ee7`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (keyDimension : Nat) →
          instLTNat.lt 0 keyDimension →
            instLENat.le keyDimension n →
              (polynomialFactor : HighamBench.P19PolynomialFactor) →
                (ug um ua etaR rhoAR : ι → Real) →
                  (∀ (t : ι),
                      And (Real.instLE.le 0 (ug t))
                        (And (Real.instLE.le 0 (um t))
                          (And (Real.instLE.le 0 (ua t))
                            (And (Real.instLE.le 0 (etaR t)) (Real.instLE.le 0 (rhoAR t)))))) →
                    (vHat : ι → HighamBench.P19RectMatrix n keyDimension) →
                      (vHatNext : ι → HighamBench.P19RectMatrix n (instHAdd.hAdd keyDimension 1)) →
                        (zHat computedAZ : ι → HighamBench.P19RectMatrix n keyDimension) →
                          (beta : ι → Real) →
                            (hessenberg : ι → HighamBench.P19RectMatrix (instHAdd.hAdd keyDimension 1) keyDimension) →
                              (∀ (t : ι), HighamBench.p19IsUpperHessenberg (hessenberg t)) →
                                (∀ (t : ι),
                                    Eq
                                      (HighamBench.p19Augment
                                        (HighamBench.p19InitialResidual system.A system.b system.xInitial)
                                        (computedAZ t))
                                      (HighamBench.p19RectMatMul (vHatNext t)
                                        (HighamBench.p19Augment (HighamBench.p19ScaledFirstBasisVector (beta t))
                                          (hessenberg t)))) →
                                  (∀ (t : ι) (i : Fin n) (j : Fin keyDimension),
                                      Eq (vHat t i j) (vHatNext t i j.castSucc)) →
                                    (leastSquaresDeltaB : ι → HighamBench.P19Vector n) →
                                      (leastSquaresDeltaC : ι → HighamBench.P19RectMatrix n keyDimension) →
                                        (yHat : ι → HighamBench.P19Vector keyDimension) →
                                          (∀ (t : ι),
                                              HighamBench.p19IsLeastSquaresSolution
                                                (instHAdd.hAdd (computedAZ t) (leastSquaresDeltaC t))
                                                (instHAdd.hAdd
                                                  (HighamBench.p19InitialResidual system.A system.b system.xInitial)
                                                  (leastSquaresDeltaB t))
                                                (yHat t)) →
                                            (∀ (t : ι) (j : Fin (instHAdd.hAdd keyDimension 1)),
                                                Real.instLE.le
                                                  (HighamBench.p19VecNorm2
                                                    (HighamBench.p19Column
                                                      (HighamBench.p19Augment (leastSquaresDeltaB t)
                                                        (leastSquaresDeltaC t))
                                                      j))
                                                  (instHMul.hMul
                                                    (instHMul.hMul
                                                      (HighamBench.p19PolynomialFactorValue polynomialFactor n
                                                        keyDimension)
                                                      (ug t))
                                                    (HighamBench.p19VecNorm2
                                                      (HighamBench.p19Column
                                                        (HighamBench.p19Augment
                                                          (HighamBench.p19InitialResidual system.A system.b
                                                            system.xInitial)
                                                          (computedAZ t))
                                                        j)))) →
                                              (∀ (t : ι), HighamBench.p19FullColumnRank (zHat t)) →
                                                (preconditionerDelta : ι → Fin keyDimension → HighamBench.P19Matrix n) →
                                                  (∀ (t : ι) (j : Fin keyDimension),
                                                      Eq (HighamBench.p19Column (zHat t) j)
                                                        (HighamBench.p19MatVec
                                                          (instHAdd.hAdd system.MRinv (preconditionerDelta t j))
                                                          (HighamBench.p19Column (vHat t) j))) →
                                                    (∀ (t : ι) (j : Fin keyDimension),
                                                        Real.instLE.le
                                                          (HighamBench.p19FrobNorm (preconditionerDelta t j))
                                                          (instHMul.hMul
                                                            (instHMul.hMul
                                                              (instHMul.hMul
                                                                (HighamBench.p19PolynomialFactorValue polynomialFactor n
                                                                  keyDimension)
                                                                (um t))
                                                              (etaR t))
                                                            (HighamBench.p19FrobNorm system.MRinv))) →
                                                      (matrixDelta : ι → Fin keyDimension → HighamBench.P19Matrix n) →
                                                        (∀ (t : ι) (j : Fin keyDimension),
                                                            Eq (HighamBench.p19Column (computedAZ t) j)
                                                              (HighamBench.p19MatVec
                                                                (instHAdd.hAdd system.A (matrixDelta t j))
                                                                (HighamBench.p19Column (zHat t) j))) →
                                                          (∀ (t : ι) (j : Fin keyDimension) (i q : Fin n),
                                                              Real.instLE.le (abs (matrixDelta t j i q))
                                                                (instHMul.hMul
                                                                  (instHMul.hMul
                                                                    (HighamBench.p19PolynomialFactorValue
                                                                      polynomialFactor n keyDimension)
                                                                    (ua t))
                                                                  (abs (system.A i q)))) →
                                                            (∀ (t : ι),
                                                                Real.instLT.lt 0
                                                                  (HighamBench.p19VecNorm2
                                                                    (HighamBench.p19RectMatVec (zHat t) (yHat t)))) →
                                                              (∀ (t : ι),
                                                                  Eq (rhoAR t)
                                                                    (instHDiv.hDiv
                                                                      (HighamBench.p19VecNorm2
                                                                        (HighamBench.p19AbsRectMatVec (zHat t)
                                                                          (yHat t)))
                                                                      (HighamBench.p19VecNorm2
                                                                        (HighamBench.p19RectMatVec (zHat t)
                                                                          (yHat t))))) →
                                                                (HighamBench.p19MuchLessThanOneAt l fun t =>
                                                                    HighamBench.p19Condition316Value system (ug t)
                                                                      (um t) (ua t) (etaR t) (rhoAR t)) →
                                                                  HighamBench.P19FixedRightGMRESRun system l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (keyDimension : Nat) →
          (keyDimension_pos :
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) keyDimension) →
            (keyDimension_le : @LE.le.{0} Nat instLENat keyDimension n) →
              (polynomialFactor : HighamBench.P19PolynomialFactor) →
                (ug um ua etaR rhoAR : ι → Real) →
                  (parameters_nonneg :
                      ∀ (t : ι),
                        And
                          (@LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (ug t))
                          (And
                            (@LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (um t))
                            (And
                              (@LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (ua t))
                              (And
                                (@LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (etaR t))
                                (@LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (rhoAR t)))))) →
                    (vHat : ι → HighamBench.P19RectMatrix n keyDimension) →
                      (vHatNext :
                          ι →
                            HighamBench.P19RectMatrix n
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        (zHat computedAZ : ι → HighamBench.P19RectMatrix n keyDimension) →
                          (beta : ι → Real) →
                            (hessenberg :
                                ι →
                                  HighamBench.P19RectMatrix
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    keyDimension) →
                              (hessenberg_upper :
                                  ∀ (t : ι), @HighamBench.p19IsUpperHessenberg keyDimension (hessenberg t)) →
                                (mgs_relation :
                                    ∀ (t : ι),
                                      @Eq.{1}
                                        (HighamBench.P19RectMatrix n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@HighamBench.p19Augment n keyDimension
                                          (@HighamBench.p19InitialResidual n
                                            (@HighamBench.P19FixedRightSystem.A n system)
                                            (@HighamBench.P19FixedRightSystem.b n system)
                                            (@HighamBench.P19FixedRightSystem.xInitial n system))
                                          (computedAZ t))
                                        (@HighamBench.p19RectMatMul n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (vHatNext t)
                                          (@HighamBench.p19Augment
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              keyDimension
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            keyDimension (@HighamBench.p19ScaledFirstBasisVector keyDimension (beta t))
                                            (hessenberg t)))) →
                                  (vHat_prefix :
                                      ∀ (t : ι) (i : Fin n) (j : Fin keyDimension),
                                        @Eq.{1} Real (vHat t i j) (vHatNext t i (@Fin.castSucc keyDimension j))) →
                                    (leastSquaresDeltaB : ι → HighamBench.P19Vector n) →
                                      (leastSquaresDeltaC : ι → HighamBench.P19RectMatrix n keyDimension) →
                                        (yHat : ι → HighamBench.P19Vector keyDimension) →
                                          (least_squares_solution :
                                              ∀ (t : ι),
                                                @HighamBench.p19IsLeastSquaresSolution n keyDimension
                                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19RectMatrix n keyDimension)
                                                    (HighamBench.P19RectMatrix n keyDimension)
                                                    (HighamBench.P19RectMatrix n keyDimension)
                                                    (@instHAdd.{0} (HighamBench.P19RectMatrix n keyDimension)
                                                      (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real
                                                        Real.instAdd))
                                                    (computedAZ t) (leastSquaresDeltaC t))
                                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                    (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                    (@instHAdd.{0} (HighamBench.P19Vector n)
                                                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                        fun (i : Fin n) => Real.instAdd))
                                                    (@HighamBench.p19InitialResidual n
                                                      (@HighamBench.P19FixedRightSystem.A n system)
                                                      (@HighamBench.P19FixedRightSystem.b n system)
                                                      (@HighamBench.P19FixedRightSystem.xInitial n system))
                                                    (leastSquaresDeltaB t))
                                                  (yHat t)) →
                                            (least_squares_column_bound :
                                                ∀ (t : ι)
                                                  (j :
                                                    Fin
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        keyDimension
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@HighamBench.p19VecNorm2 n
                                                      (@HighamBench.p19Column n
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          keyDimension
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        (@HighamBench.p19Augment n keyDimension (leastSquaresDeltaB t)
                                                          (leastSquaresDeltaC t))
                                                        j))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (HighamBench.p19PolynomialFactorValue polynomialFactor n
                                                          keyDimension)
                                                        (ug t))
                                                      (@HighamBench.p19VecNorm2 n
                                                        (@HighamBench.p19Column n
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) keyDimension
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))
                                                          (@HighamBench.p19Augment n keyDimension
                                                            (@HighamBench.p19InitialResidual n
                                                              (@HighamBench.P19FixedRightSystem.A n system)
                                                              (@HighamBench.P19FixedRightSystem.b n system)
                                                              (@HighamBench.P19FixedRightSystem.xInitial n system))
                                                            (computedAZ t))
                                                          j)))) →
                                              (zHat_full_rank :
                                                  ∀ (t : ι), @HighamBench.p19FullColumnRank n keyDimension (zHat t)) →
                                                (preconditionerDelta : ι → Fin keyDimension → HighamBench.P19Matrix n) →
                                                  (preconditioner_application :
                                                      ∀ (t : ι) (j : Fin keyDimension),
                                                        @Eq.{1} (HighamBench.P19Vector n)
                                                          (@HighamBench.p19Column n keyDimension (zHat t) j)
                                                          (@HighamBench.p19MatVec n
                                                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n)
                                                              (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                                                              (@instHAdd.{0} (HighamBench.P19Matrix n)
                                                                (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real
                                                                  Real.instAdd))
                                                              (@HighamBench.P19FixedRightSystem.MRinv n system)
                                                              (preconditionerDelta t j))
                                                            (@HighamBench.p19Column n keyDimension (vHat t) j))) →
                                                    (preconditioner_error_bound :
                                                        ∀ (t : ι) (j : Fin keyDimension),
                                                          @LE.le.{0} Real Real.instLE
                                                            (@HighamBench.p19FrobNorm n n (preconditionerDelta t j))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                (@instHMul.{0} Real Real.instMul)
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (HighamBench.p19PolynomialFactorValue polynomialFactor
                                                                    n keyDimension)
                                                                  (um t))
                                                                (etaR t))
                                                              (@HighamBench.p19FrobNorm n n
                                                                (@HighamBench.P19FixedRightSystem.MRinv n system)))) →
                                                      (matrixDelta : ι → Fin keyDimension → HighamBench.P19Matrix n) →
                                                        (matrix_application :
                                                            ∀ (t : ι) (j : Fin keyDimension),
                                                              @Eq.{1} (HighamBench.P19Vector n)
                                                                (@HighamBench.p19Column n keyDimension (computedAZ t) j)
                                                                (@HighamBench.p19MatVec n
                                                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n)
                                                                    (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                                                                    (@instHAdd.{0} (HighamBench.P19Matrix n)
                                                                      (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real
                                                                        Real.instAdd))
                                                                    (@HighamBench.P19FixedRightSystem.A n system)
                                                                    (matrixDelta t j))
                                                                  (@HighamBench.p19Column n keyDimension (zHat t) j))) →
                                                          (matrix_error_bound :
                                                              ∀ (t : ι) (j : Fin keyDimension) (i q : Fin n),
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    (matrixDelta t j i q))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul)
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul)
                                                                      (HighamBench.p19PolynomialFactorValue
                                                                        polynomialFactor n keyDimension)
                                                                      (ua t))
                                                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                      (@HighamBench.P19FixedRightSystem.A n system i
                                                                        q)))) →
                                                            (rho_denominator_pos :
                                                                ∀ (t : ι),
                                                                  @LT.lt.{0} Real Real.instLT
                                                                    (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                      (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                    (@HighamBench.p19VecNorm2 n
                                                                      (@HighamBench.p19RectMatVec n keyDimension
                                                                        (zHat t) (yHat t)))) →
                                                              (rho_equation :
                                                                  ∀ (t : ι),
                                                                    @Eq.{1} Real (rhoAR t)
                                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                        (@instHDiv.{0} Real
                                                                          (@DivInvMonoid.toDiv.{0} Real
                                                                            Real.instDivInvMonoid))
                                                                        (@HighamBench.p19VecNorm2 n
                                                                          (@HighamBench.p19AbsRectMatVec n keyDimension
                                                                            (zHat t) (yHat t)))
                                                                        (@HighamBench.p19VecNorm2 n
                                                                          (@HighamBench.p19RectMatVec n keyDimension
                                                                            (zHat t) (yHat t))))) →
                                                                (condition316 :
                                                                    @HighamBench.p19MuchLessThanOneAt.{u_1} ι l
                                                                      fun (t : ι) =>
                                                                      @HighamBench.p19Condition316Value n system (ug t)
                                                                        (um t) (ua t) (etaR t) (rhoAR t)) →
                                                                  @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l
```

### D044: `HighamBench.P19FixedRightSystem.A`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4fc51f9715a39e73fbce0d1d5327b06bb1194c29b6aabb76716348777b2b7925`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D045: `HighamBench.P19FixedRightSystem.Ainv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2f61d63a62140c0ee8c5a9b26ac463ad9537227b8ca103b2ad08c1076926d850`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D046: `HighamBench.P19FlexibleForwardAnalysis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `cb6d739879436b21ef069304a470b11291cc1299c5ed53df17ee0ef0f2b34704`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} → HighamBench.P19FlexibleGMRESRun run → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (algorithm : @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run) → Type u_1
```

### D047: `HighamBench.P19FlexibleGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7632c6b96c7c3bcc269cbba4171aa6df62a100c3f3097dfd976e95fbd3b5bfc2`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          (solutionBasisDelta : ι → HighamBench.P19RectMatrix n run.keyDimension) →
            (xHat : ι → HighamBench.P19Vector n) →
              (∀ (t : ι) (i : Fin n) (j : Fin run.keyDimension),
                  Real.instLE.le (abs (solutionBasisDelta t i j))
                    (instHMul.hMul
                      (instHMul.hMul (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension)
                        (run.ug t))
                      (abs (run.zHat t i j)))) →
                (∀ (t : ι),
                    Eq (xHat t)
                      (HighamBench.p19Add system.xInitial
                        (HighamBench.p19RectMatVec (instHAdd.hAdd (run.zHat t) (solutionBasisDelta t)) (run.yHat t)))) →
                  HighamBench.P19FlexibleGMRESRun run
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (solutionBasisDelta :
              ι →
                HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)) →
            (xHat : ι → HighamBench.P19Vector n) →
              (solution_basis_error_bound :
                  ∀ (t : ι) (i : Fin n)
                    (j : Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)),
                    @LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup (solutionBasisDelta t i j))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (HighamBench.p19PolynomialFactorValue
                            (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l run) n
                            (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                          (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t))
                        (@abs.{0} Real Real.lattice Real.instAddGroup
                          (@HighamBench.P19FixedRightGMRESRun.zHat.{u_1} n ι system l run t i j)))) →
                (solution_equation :
                    ∀ (t : ι),
                      @Eq.{1} (HighamBench.P19Vector n) (xHat t)
                        (@HighamBench.p19Add n (@HighamBench.P19FixedRightSystem.xInitial n system)
                          (@HighamBench.p19RectMatVec n
                            (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)
                            (@HAdd.hAdd.{0, 0, 0}
                              (HighamBench.P19RectMatrix n
                                (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                              (HighamBench.P19RectMatrix n
                                (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                              (HighamBench.P19RectMatrix n
                                (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                              (@instHAdd.{0}
                                (HighamBench.P19RectMatrix n
                                  (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                (@Matrix.add.{0, 0, 0} (Fin n)
                                  (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)) Real
                                  Real.instAdd))
                              (@HighamBench.P19FixedRightGMRESRun.zHat.{u_1} n ι system l run t) (solutionBasisDelta t))
                            (@HighamBench.P19FixedRightGMRESRun.yHat.{u_1} n ι system l run t)))) →
                  @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run
```

### D048: `HighamBench.P19Matrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D049: `HighamBench.P19PolynomialFactor.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `d58684bdda1ea68b662f7a64d90373af65ef0a9d2ae7c566f7f577b882df1bbb`

Type:

```lean
(degreeN degreeK : Nat) →
  (coefficient : Fin (instHAdd.hAdd degreeN 1) → Fin (instHAdd.hAdd degreeK 1) → Real) →
    (∀ (i : Fin (instHAdd.hAdd degreeN 1)) (j : Fin (instHAdd.hAdd degreeK 1)), Real.instLE.le 0 (coefficient i j)) →
      HighamBench.P19PolynomialFactor
```

Fully explicit type:

```lean
(degreeN degreeK : Nat) →
  (coefficient :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeN
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeK
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
    (coefficient_nonneg :
        ∀
          (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeN
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (j :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) degreeK
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (coefficient i j)) →
      HighamBench.P19PolynomialFactor
```

### D050: `HighamBench.P19RightForwardAnalysis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `65e9cb59a5fef34a3f2e2999da4979db438ca782ab055abd5048b1a67a52abc1`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → {run : HighamBench.P19FixedRightGMRESRun system l} → HighamBench.P19RightGMRESRun run → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (algorithm : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run) → Type u_1
```

### D051: `HighamBench.P19RightGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1a0e1951e0bda26ce8cd6b530c8ae12824da0e55d538cdb76c1dc38621406c6e`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          (solutionBasisDelta : ι → HighamBench.P19RectMatrix n run.keyDimension) →
            (solutionPreconditionerDelta : ι → HighamBench.P19Matrix n) →
              (xHat : ι → HighamBench.P19Vector n) →
                (∀ (t : ι) (i : Fin n) (j : Fin run.keyDimension),
                    Real.instLE.le (abs (solutionBasisDelta t i j))
                      (instHMul.hMul
                        (instHMul.hMul (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension)
                          (run.ug t))
                        (abs (run.vHat t i j)))) →
                  (∀ (t : ι),
                      Real.instLE.le (HighamBench.p19FrobNorm (solutionPreconditionerDelta t))
                        (instHMul.hMul
                          (instHMul.hMul
                            (instHMul.hMul
                              (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension) (run.um t))
                            (run.etaR t))
                          (HighamBench.p19FrobNorm system.MRinv))) →
                    (∀ (t : ι),
                        Eq (xHat t)
                          (HighamBench.p19Add system.xInitial
                            (HighamBench.p19MatVec (instHAdd.hAdd system.MRinv (solutionPreconditionerDelta t))
                              (HighamBench.p19RectMatVec (instHAdd.hAdd (run.vHat t) (solutionBasisDelta t))
                                (run.yHat t))))) →
                      HighamBench.P19RightGMRESRun run
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (solutionBasisDelta :
              ι →
                HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)) →
            (solutionPreconditionerDelta : ι → HighamBench.P19Matrix n) →
              (xHat : ι → HighamBench.P19Vector n) →
                (solution_basis_error_bound :
                    ∀ (t : ι) (i : Fin n)
                      (j : Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)),
                      @LE.le.{0} Real Real.instLE
                        (@abs.{0} Real Real.lattice Real.instAddGroup (solutionBasisDelta t i j))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (HighamBench.p19PolynomialFactorValue
                              (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l run) n
                              (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                            (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t))
                          (@abs.{0} Real Real.lattice Real.instAddGroup
                            (@HighamBench.P19FixedRightGMRESRun.vHat.{u_1} n ι system l run t i j)))) →
                  (solution_preconditioner_error_bound :
                      ∀ (t : ι),
                        @LE.le.{0} Real Real.instLE (@HighamBench.p19FrobNorm n n (solutionPreconditionerDelta t))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (HighamBench.p19PolynomialFactorValue
                                  (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l run) n
                                  (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l run t))
                              (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l run t))
                            (@HighamBench.p19FrobNorm n n (@HighamBench.P19FixedRightSystem.MRinv n system)))) →
                    (solution_equation :
                        ∀ (t : ι),
                          @Eq.{1} (HighamBench.P19Vector n) (xHat t)
                            (@HighamBench.p19Add n (@HighamBench.P19FixedRightSystem.xInitial n system)
                              (@HighamBench.p19MatVec n
                                (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                                  (HighamBench.P19Matrix n)
                                  (@instHAdd.{0} (HighamBench.P19Matrix n)
                                    (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                  (@HighamBench.P19FixedRightSystem.MRinv n system) (solutionPreconditionerDelta t))
                                (@HighamBench.p19RectMatVec n
                                  (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)
                                  (@HAdd.hAdd.{0, 0, 0}
                                    (HighamBench.P19RectMatrix n
                                      (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                    (HighamBench.P19RectMatrix n
                                      (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                    (HighamBench.P19RectMatrix n
                                      (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                    (@instHAdd.{0}
                                      (HighamBench.P19RectMatrix n
                                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      (@Matrix.add.{0, 0, 0} (Fin n)
                                        (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                        Real Real.instAdd))
                                    (@HighamBench.P19FixedRightGMRESRun.vHat.{u_1} n ι system l run t)
                                    (solutionBasisDelta t))
                                  (@HighamBench.P19FixedRightGMRESRun.yHat.{u_1} n ι system l run t))))) →
                      @HighamBench.P19RightGMRESRun.{u_1} n ι system l run
```

### D052: `HighamBench.p19InitialResidual`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `42b694964760f3236be9e08c7ac9ecc87fd7c86b7e9bd1831029e0d42c33f85c`

Type:

```lean
{n : Nat} → HighamBench.P19Matrix n → HighamBench.P19Vector n → HighamBench.P19Vector n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P19Matrix n) → (b xInitial : HighamBench.P19Vector n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xInitial => instHSub.hSub b (HighamBench.p19MatVec A xInitial)
```

### D053: `HighamBench.p19InversePair`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D054: `HighamBench.p19MatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D055: `HighamBench.p19OpNorm2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `32c1a2b57edb3d01327a9830854f615bd5cdaf06ad34d12929712c0b11ac6fc8`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D056: `HighamBench.p19RightOperator`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5dba27f3c2cc81e48a12311c505e26b659c7092e89c61246eee2463f4b519628`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19SquareRectMul system.A system.MRinv
```

### D057: `HighamBench.p19RightOperatorInverse`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `10a6adaa9a930235b6b24bcac98a6c2b1bc9792eab2cc4e47ba94aa5f7d96dd8`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19FixedRightSystem n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19SquareRectMul system.MR system.Ainv
```

### D058: `HighamBench.p19SquareRectMul`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D059: `HighamBench.p19VecNorm2Sq`

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

### D060: `HighamBench.P19FixedRightGMRESRun.vHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `a5bea81d4044c6eaf4d239e58a7f99edc8bef3aa9b7822fe2faa73cbdae63cb8`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (self : HighamBench.P19FixedRightGMRESRun system l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          ι → HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.11
```

### D061: `HighamBench.P19FixedRightGMRESRun.yHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cc5bca60d852aaafb58b05e07efde1e69b2c5add9634c75a785eaeb322f6fc83`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → (self : HighamBench.P19FixedRightGMRESRun system l) → ι → HighamBench.P19Vector self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          ι → HighamBench.P19Vector (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.22
```

### D062: `HighamBench.P19FixedRightGMRESRun.zHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `1f744b2f600adc30ddee2e00716d0100a742711ead8b9ef7741dd84a3e499960`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (self : HighamBench.P19FixedRightGMRESRun system l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          ι → HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.13
```

### D063: `HighamBench.P19FixedRightSystem.b`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `044b4dddd03bc433444e32ab99bbb3bb3cbb99bef9c48cb86d492a1326a7cb7b`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.10
```

### D064: `HighamBench.P19FixedRightSystem.xInitial`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `5a05f665c6aaeccdd295e8e66a0d368a557a00be2c0f10599535189c2bc23ba3`

Type:

```lean
{n : Nat} → HighamBench.P19FixedRightSystem n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19FixedRightSystem n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.12
```

### D065: `HighamBench.P19FlexibleForwardAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `02bbe1dc0726c6ee1c3438cbaf8693fef5418549511b48f7b035628e02fea1b3`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          {algorithm : HighamBench.P19FlexibleGMRESRun run} →
            (gmresPropagation :
                ι →
                  HighamBench.P19Vector n →
                    HighamBench.P19RectMatrix n run.keyDimension →
                      HighamBench.P19RectMatrix n run.keyDimension → HighamBench.P19Vector n) →
              (matrixPropagation : ι → (Fin run.keyDimension → HighamBench.P19Matrix n) → HighamBench.P19Vector n) →
                (gmresContribution matrixContribution remainder : ι → HighamBench.P19Vector n) →
                  (∀ (t : ι),
                      Eq (gmresContribution t)
                        (gmresPropagation t (run.leastSquaresDeltaB t) (run.leastSquaresDeltaC t)
                          (algorithm.solutionBasisDelta t))) →
                    (∀ (t : ι), Eq (matrixContribution t) (matrixPropagation t (run.matrixDelta t))) →
                      (∀ (t : ι), Eq (gmresPropagation t 0 0 0) 0) →
                        (∀ (t : ι), Eq (matrixPropagation t fun x => 0) 0) →
                          (∀ (t : ι),
                              Eq (instHSub.hSub (algorithm.xHat t) system.xExact)
                                (instHAdd.hAdd (instHAdd.hAdd (gmresContribution t) (matrixContribution t))
                                  (remainder t))) →
                            (∀ (t : ι),
                                Real.instLE.le
                                  (instHDiv.hDiv (HighamBench.p19VecNorm2 (gmresContribution t))
                                    (HighamBench.p19VecNorm2 system.xExact))
                                  (instHMul.hMul
                                    (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension)
                                    (instHMul.hMul
                                      (instHMul.hMul (run.ug t) (HighamBench.p19RightOperatorKappa2 system))
                                      (HighamBench.p19RightPreconditionerKappa2 system)))) →
                              (∀ (t : ι),
                                  Real.instLE.le
                                    (instHDiv.hDiv (HighamBench.p19VecNorm2 (matrixContribution t))
                                      (HighamBench.p19VecNorm2 system.xExact))
                                    (instHMul.hMul
                                      (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension)
                                      (instHMul.hMul (instHMul.hMul (run.ua t) (HighamBench.p19SystemKappa2 system))
                                        (run.rhoAR t)))) →
                                (HighamBench.p19SecondOrderAt l
                                    (fun t =>
                                      HighamBench.p19Condition316Value system (run.ug t) (run.um t) (run.ua t)
                                        (run.etaR t) (run.rhoAR t))
                                    fun t =>
                                    instHDiv.hDiv (HighamBench.p19VecNorm2 (remainder t))
                                      (HighamBench.p19VecNorm2 system.xExact)) →
                                  HighamBench.P19FlexibleForwardAnalysis algorithm
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          {algorithm : @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run} →
            (gmresPropagation :
                ι →
                  HighamBench.P19Vector n →
                    HighamBench.P19RectMatrix n
                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                      HighamBench.P19RectMatrix n
                          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                        HighamBench.P19Vector n) →
              (matrixPropagation :
                  ι →
                    (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                        HighamBench.P19Matrix n) →
                      HighamBench.P19Vector n) →
                (gmresContribution matrixContribution remainder : ι → HighamBench.P19Vector n) →
                  (gmres_link :
                      ∀ (t : ι),
                        @Eq.{1} (HighamBench.P19Vector n) (gmresContribution t)
                          (gmresPropagation t
                            (@HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaB.{u_1} n ι system l run t)
                            (@HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaC.{u_1} n ι system l run t)
                            (@HighamBench.P19FlexibleGMRESRun.solutionBasisDelta.{u_1} n ι system l run algorithm t))) →
                    (matrix_link :
                        ∀ (t : ι),
                          @Eq.{1} (HighamBench.P19Vector n) (matrixContribution t)
                            (matrixPropagation t
                              (@HighamBench.P19FixedRightGMRESRun.matrixDelta.{u_1} n ι system l run t))) →
                      (gmresPropagation_zero :
                          ∀ (t : ι),
                            @Eq.{1} (HighamBench.P19Vector n)
                              (gmresPropagation t
                                (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                  (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                    (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instZero)))
                                (@OfNat.ofNat.{0}
                                  (HighamBench.P19RectMatrix n
                                    (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                  (nat_lit 0)
                                  (@Zero.toOfNat0.{0}
                                    (HighamBench.P19RectMatrix n
                                      (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                    (@Matrix.zero.{0, 0, 0} (Fin n)
                                      (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      Real Real.instZero)))
                                (@OfNat.ofNat.{0}
                                  (HighamBench.P19RectMatrix n
                                    (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                  (nat_lit 0)
                                  (@Zero.toOfNat0.{0}
                                    (HighamBench.P19RectMatrix n
                                      (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                    (@Matrix.zero.{0, 0, 0} (Fin n)
                                      (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      Real Real.instZero))))
                              (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                  (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instZero)))) →
                        (matrixPropagation_zero :
                            ∀ (t : ι),
                              @Eq.{1} (HighamBench.P19Vector n)
                                (matrixPropagation t
                                  fun
                                    (x :
                                      Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)) =>
                                  @OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 0)
                                    (@Zero.toOfNat0.{0} (HighamBench.P19Matrix n)
                                      (@Matrix.zero.{0, 0, 0} (Fin n) (Fin n) Real Real.instZero)))
                                (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                  (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                    (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instZero)))) →
                          (error_decomposition :
                              ∀ (t : ι),
                                @Eq.{1} (HighamBench.P19Vector n)
                                  (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                    (HighamBench.P19Vector n)
                                    (@instHSub.{0} (HighamBench.P19Vector n)
                                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        Real.instSub))
                                    (@HighamBench.P19FlexibleGMRESRun.xHat.{u_1} n ι system l run algorithm t)
                                    (@HighamBench.P19FixedRightSystem.xExact n system))
                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                    (HighamBench.P19Vector n)
                                    (@instHAdd.{0} (HighamBench.P19Vector n)
                                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        Real.instAdd))
                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                      (HighamBench.P19Vector n)
                                      (@instHAdd.{0} (HighamBench.P19Vector n)
                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                          Real.instAdd))
                                      (gmresContribution t) (matrixContribution t))
                                    (remainder t))) →
                            (gmres_bound :
                                ∀ (t : ι),
                                  @LE.le.{0} Real Real.instLE
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (@HighamBench.p19VecNorm2 n (gmresContribution t))
                                      (@HighamBench.p19VecNorm2 n (@HighamBench.P19FixedRightSystem.xExact n system)))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (HighamBench.p19PolynomialFactorValue
                                        (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l run) n
                                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t)
                                          (@HighamBench.p19RightOperatorKappa2 n system))
                                        (@HighamBench.p19RightPreconditionerKappa2 n system)))) →
                              (matrix_bound :
                                  ∀ (t : ι),
                                    @LE.le.{0} Real Real.instLE
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@HighamBench.p19VecNorm2 n (matrixContribution t))
                                        (@HighamBench.p19VecNorm2 n (@HighamBench.P19FixedRightSystem.xExact n system)))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (HighamBench.p19PolynomialFactorValue
                                          (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l run) n
                                          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l run t)
                                            (@HighamBench.p19SystemKappa2 n system))
                                          (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l run t)))) →
                                (remainder_second_order :
                                    @HighamBench.p19SecondOrderAt.{u_1} ι l
                                      (fun (t : ι) =>
                                        @HighamBench.p19Condition316Value n system
                                          (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t)
                                          (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l run t)
                                          (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l run t)
                                          (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l run t)
                                          (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l run t))
                                      fun (t : ι) =>
                                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@HighamBench.p19VecNorm2 n (remainder t))
                                        (@HighamBench.p19VecNorm2 n
                                          (@HighamBench.P19FixedRightSystem.xExact n system))) →
                                  @HighamBench.P19FlexibleForwardAnalysis.{u_1} n ι system l run algorithm
```

### D066: `HighamBench.P19RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D067: `HighamBench.P19RightForwardAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `26ee95be6c7d97b26e9ff1b0be345566076bf892d462e19173f0689f538c7cd7`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          {algorithm : HighamBench.P19RightGMRESRun run} →
            (gmresPropagation :
                ι →
                  HighamBench.P19Vector n →
                    HighamBench.P19RectMatrix n run.keyDimension →
                      HighamBench.P19RectMatrix n run.keyDimension → HighamBench.P19Vector n) →
              (reapplicationPropagation : ι → HighamBench.P19Matrix n → HighamBench.P19Vector n) →
                (matrixPropagation : ι → (Fin run.keyDimension → HighamBench.P19Matrix n) → HighamBench.P19Vector n) →
                  (gmresContribution reapplicationContribution matrixContribution remainder :
                      ι → HighamBench.P19Vector n) →
                    (∀ (t : ι),
                        Eq (gmresContribution t)
                          (gmresPropagation t (run.leastSquaresDeltaB t) (run.leastSquaresDeltaC t)
                            (algorithm.solutionBasisDelta t))) →
                      (∀ (t : ι),
                          Eq (reapplicationContribution t)
                            (reapplicationPropagation t (algorithm.solutionPreconditionerDelta t))) →
                        (∀ (t : ι), Eq (matrixContribution t) (matrixPropagation t (run.matrixDelta t))) →
                          (∀ (t : ι), Eq (gmresPropagation t 0 0 0) 0) →
                            (∀ (t : ι), Eq (reapplicationPropagation t 0) 0) →
                              (∀ (t : ι), Eq (matrixPropagation t fun x => 0) 0) →
                                (∀ (t : ι),
                                    Eq (instHSub.hSub (algorithm.xHat t) system.xExact)
                                      (instHAdd.hAdd
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd (gmresContribution t) (reapplicationContribution t))
                                          (matrixContribution t))
                                        (remainder t))) →
                                  (∀ (t : ι),
                                      Real.instLE.le
                                        (instHDiv.hDiv (HighamBench.p19VecNorm2 (gmresContribution t))
                                          (HighamBench.p19VecNorm2 system.xExact))
                                        (instHMul.hMul
                                          (HighamBench.p19PolynomialFactorValue run.polynomialFactor n run.keyDimension)
                                          (instHMul.hMul
                                            (instHMul.hMul (run.ug t) (HighamBench.p19RightOperatorKappa2 system))
                                            (HighamBench.p19RightPreconditionerKappa2 system)))) →
                                    (∀ (t : ι),
                                        Real.instLE.le
                                          (instHDiv.hDiv (HighamBench.p19VecNorm2 (reapplicationContribution t))
                                            (HighamBench.p19VecNorm2 system.xExact))
                                          (instHMul.hMul
                                            (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                              run.keyDimension)
                                            (instHMul.hMul (instHMul.hMul (run.um t) (run.etaR t))
                                              (HighamBench.p19RightPreconditionerKappa2 system)))) →
                                      (∀ (t : ι),
                                          Real.instLE.le
                                            (instHDiv.hDiv (HighamBench.p19VecNorm2 (matrixContribution t))
                                              (HighamBench.p19VecNorm2 system.xExact))
                                            (instHMul.hMul
                                              (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                                run.keyDimension)
                                              (instHMul.hMul
                                                (instHMul.hMul (run.ua t) (HighamBench.p19SystemKappa2 system))
                                                (run.rhoAR t)))) →
                                        (HighamBench.p19SecondOrderAt l
                                            (fun t =>
                                              HighamBench.p19Condition316Value system (run.ug t) (run.um t) (run.ua t)
                                                (run.etaR t) (run.rhoAR t))
                                            fun t =>
                                            instHDiv.hDiv (HighamBench.p19VecNorm2 (remainder t))
                                              (HighamBench.p19VecNorm2 system.xExact)) →
                                          HighamBench.P19RightForwardAnalysis algorithm
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          {algorithm : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run} →
            (gmresPropagation :
                ι →
                  HighamBench.P19Vector n →
                    HighamBench.P19RectMatrix n
                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                      HighamBench.P19RectMatrix n
                          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                        HighamBench.P19Vector n) →
              (reapplicationPropagation : ι → HighamBench.P19Matrix n → HighamBench.P19Vector n) →
                (matrixPropagation :
                    ι →
                      (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run) →
                          HighamBench.P19Matrix n) →
                        HighamBench.P19Vector n) →
                  (gmresContribution reapplicationContribution matrixContribution remainder :
                      ι → HighamBench.P19Vector n) →
                    (gmres_link :
                        ∀ (t : ι),
                          @Eq.{1} (HighamBench.P19Vector n) (gmresContribution t)
                            (gmresPropagation t
                              (@HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaB.{u_1} n ι system l run t)
                              (@HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaC.{u_1} n ι system l run t)
                              (@HighamBench.P19RightGMRESRun.solutionBasisDelta.{u_1} n ι system l run algorithm t))) →
                      (reapplication_link :
                          ∀ (t : ι),
                            @Eq.{1} (HighamBench.P19Vector n) (reapplicationContribution t)
                              (reapplicationPropagation t
                                (@HighamBench.P19RightGMRESRun.solutionPreconditionerDelta.{u_1} n ι system l run
                                  algorithm t))) →
                        (matrix_link :
                            ∀ (t : ι),
                              @Eq.{1} (HighamBench.P19Vector n) (matrixContribution t)
                                (matrixPropagation t
                                  (@HighamBench.P19FixedRightGMRESRun.matrixDelta.{u_1} n ι system l run t))) →
                          (gmresPropagation_zero :
                              ∀ (t : ι),
                                @Eq.{1} (HighamBench.P19Vector n)
                                  (gmresPropagation t
                                    (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                      (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                        (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                          Real.instZero)))
                                    (@OfNat.ofNat.{0}
                                      (HighamBench.P19RectMatrix n
                                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      (nat_lit 0)
                                      (@Zero.toOfNat0.{0}
                                        (HighamBench.P19RectMatrix n
                                          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                        (@Matrix.zero.{0, 0, 0} (Fin n)
                                          (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                          Real Real.instZero)))
                                    (@OfNat.ofNat.{0}
                                      (HighamBench.P19RectMatrix n
                                        (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                      (nat_lit 0)
                                      (@Zero.toOfNat0.{0}
                                        (HighamBench.P19RectMatrix n
                                          (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                        (@Matrix.zero.{0, 0, 0} (Fin n)
                                          (Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                          Real Real.instZero))))
                                  (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                    (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                      (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        Real.instZero)))) →
                            (reapplicationPropagation_zero :
                                ∀ (t : ι),
                                  @Eq.{1} (HighamBench.P19Vector n)
                                    (reapplicationPropagation t
                                      (@OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 0)
                                        (@Zero.toOfNat0.{0} (HighamBench.P19Matrix n)
                                          (@Matrix.zero.{0, 0, 0} (Fin n) (Fin n) Real Real.instZero))))
                                    (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                      (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                        (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                          Real.instZero)))) →
                              (matrixPropagation_zero :
                                  ∀ (t : ι),
                                    @Eq.{1} (HighamBench.P19Vector n)
                                      (matrixPropagation t
                                        fun
                                          (x :
                                            Fin
                                              (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l
                                                run)) =>
                                        @OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 0)
                                          (@Zero.toOfNat0.{0} (HighamBench.P19Matrix n)
                                            (@Matrix.zero.{0, 0, 0} (Fin n) (Fin n) Real Real.instZero)))
                                      (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                        (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                          (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                            Real.instZero)))) →
                                (error_decomposition :
                                    ∀ (t : ι),
                                      @Eq.{1} (HighamBench.P19Vector n)
                                        (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                          (HighamBench.P19Vector n)
                                          (@instHSub.{0} (HighamBench.P19Vector n)
                                            (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                              Real.instSub))
                                          (@HighamBench.P19RightGMRESRun.xHat.{u_1} n ι system l run algorithm t)
                                          (@HighamBench.P19FixedRightSystem.xExact n system))
                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                          (HighamBench.P19Vector n)
                                          (@instHAdd.{0} (HighamBench.P19Vector n)
                                            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                              Real.instAdd))
                                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                            (HighamBench.P19Vector n)
                                            (@instHAdd.{0} (HighamBench.P19Vector n)
                                              (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                Real.instAdd))
                                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                              (HighamBench.P19Vector n)
                                              (@instHAdd.{0} (HighamBench.P19Vector n)
                                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                  Real.instAdd))
                                              (gmresContribution t) (reapplicationContribution t))
                                            (matrixContribution t))
                                          (remainder t))) →
                                  (gmres_bound :
                                      ∀ (t : ι),
                                        @LE.le.{0} Real Real.instLE
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            (@HighamBench.p19VecNorm2 n (gmresContribution t))
                                            (@HighamBench.p19VecNorm2 n
                                              (@HighamBench.P19FixedRightSystem.xExact n system)))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (HighamBench.p19PolynomialFactorValue
                                              (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l
                                                run)
                                              n
                                              (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t)
                                                (@HighamBench.p19RightOperatorKappa2 n system))
                                              (@HighamBench.p19RightPreconditionerKappa2 n system)))) →
                                    (reapplication_bound :
                                        ∀ (t : ι),
                                          @LE.le.{0} Real Real.instLE
                                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                              (@HighamBench.p19VecNorm2 n (reapplicationContribution t))
                                              (@HighamBench.p19VecNorm2 n
                                                (@HighamBench.P19FixedRightSystem.xExact n system)))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (HighamBench.p19PolynomialFactorValue
                                                (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system l
                                                  run)
                                                n
                                                (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l
                                                  run))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l run t)
                                                  (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l run t))
                                                (@HighamBench.p19RightPreconditionerKappa2 n system)))) →
                                      (matrix_bound :
                                          ∀ (t : ι),
                                            @LE.le.{0} Real Real.instLE
                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                (@HighamBench.p19VecNorm2 n (matrixContribution t))
                                                (@HighamBench.p19VecNorm2 n
                                                  (@HighamBench.P19FixedRightSystem.xExact n system)))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (HighamBench.p19PolynomialFactorValue
                                                  (@HighamBench.P19FixedRightGMRESRun.polynomialFactor.{u_1} n ι system
                                                    l run)
                                                  n
                                                  (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l
                                                    run))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l run t)
                                                    (@HighamBench.p19SystemKappa2 n system))
                                                  (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l run
                                                    t)))) →
                                        (remainder_second_order :
                                            @HighamBench.p19SecondOrderAt.{u_1} ι l
                                              (fun (t : ι) =>
                                                @HighamBench.p19Condition316Value n system
                                                  (@HighamBench.P19FixedRightGMRESRun.ug.{u_1} n ι system l run t)
                                                  (@HighamBench.P19FixedRightGMRESRun.um.{u_1} n ι system l run t)
                                                  (@HighamBench.P19FixedRightGMRESRun.ua.{u_1} n ι system l run t)
                                                  (@HighamBench.P19FixedRightGMRESRun.etaR.{u_1} n ι system l run t)
                                                  (@HighamBench.P19FixedRightGMRESRun.rhoAR.{u_1} n ι system l run t))
                                              fun (t : ι) =>
                                              @HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                (@HighamBench.p19VecNorm2 n (remainder t))
                                                (@HighamBench.p19VecNorm2 n
                                                  (@HighamBench.P19FixedRightSystem.xExact n system))) →
                                          @HighamBench.P19RightForwardAnalysis.{u_1} n ι system l run algorithm
```

### D068: `HighamBench.p19AbsRectMatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `1d5e840823958a7a00f483b0b70ee1122991bd46bae53c5f8981c0aa0826e62c`

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
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (abs (A i j)) (abs (x j))
```

### D069: `HighamBench.p19Add`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `312c3e2303d89086bfc91423334bf696f5e51c2415a0575fd2d077d7c4f7d7d6`

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

### D070: `HighamBench.p19Augment`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D071: `HighamBench.p19Column`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D072: `HighamBench.p19FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D073: `HighamBench.p19FullColumnRank`

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

### D074: `HighamBench.p19IsLeastSquaresSolution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D075: `HighamBench.p19IsUpperHessenberg`

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

### D076: `HighamBench.p19MuchLessThanOneAt`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `94328ed94fae4c0bd138ee6906d87a85bd518264114896318c738e9c53ae1bf3`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (theta : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l theta =>
  And (Filter.Tendsto theta l (nhds 0))
    (Filter.Eventually (fun t => And (Real.instLE.le 0 (theta t)) (Real.instLT.lt (theta t) 1)) l)
```

### D077: `HighamBench.p19RectMatMul`

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

### D078: `HighamBench.p19RectMatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D079: `HighamBench.p19ScaledFirstBasisVector`

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

### D080: `HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `2a7adfbadb9d6dfb22aecc1ef43b2b1149f5621bef548083fc71e779c02e9b9d`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} → HighamBench.P19FixedRightGMRESRun system l → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.20
```

### D081: `HighamBench.P19FixedRightGMRESRun.leastSquaresDeltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `54d79f41b982b9d86e97d80bc1bb6934aee111434d5afdfdb3770c53ad81616a`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (self : HighamBench.P19FixedRightGMRESRun system l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          ι → HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.21
```

### D082: `HighamBench.P19FixedRightGMRESRun.matrixDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `17aa606b5143b97dd03f479a643c68c851889ef09f2f5e069c92bff63ff571a6`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        (self : HighamBench.P19FixedRightGMRESRun system l) → ι → Fin self.keyDimension → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        (self : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l) →
          ι → Fin (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l self) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l self => self.29
```

### D083: `HighamBench.P19FlexibleGMRESRun.solutionBasisDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1295f9d799715abb51bd8662d5cb4267940c7131f99166bec7dc8926e83837be`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          HighamBench.P19FlexibleGMRESRun run → ι → HighamBench.P19RectMatrix n run.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (self : @HighamBench.P19FlexibleGMRESRun.{u_1} n ι system l run) →
            ι → HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l run self => self.1
```

### D084: `HighamBench.P19RightGMRESRun.solutionBasisDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c5bb9354b9c184cd8956bd809757efd239cfa19501ca519f19db9cd811bdd189`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          HighamBench.P19RightGMRESRun run → ι → HighamBench.P19RectMatrix n run.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (self : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run) →
            ι → HighamBench.P19RectMatrix n (@HighamBench.P19FixedRightGMRESRun.keyDimension.{u_1} n ι system l run)
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l run self => self.1
```

### D085: `HighamBench.P19RightGMRESRun.solutionPreconditionerDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `b7b91b9ad3f509d31d20b67febff7d9c5f05bc0c12a0934c6e7290cd068065d8`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter ι} →
        {run : HighamBench.P19FixedRightGMRESRun system l} →
          HighamBench.P19RightGMRESRun run → ι → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {system : HighamBench.P19FixedRightSystem n} →
      {l : Filter.{u_1} ι} →
        {run : @HighamBench.P19FixedRightGMRESRun.{u_1} n ι system l} →
          (self : @HighamBench.P19RightGMRESRun.{u_1} n ι system l run) → ι → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι system l run self => self.2
```

### D086: `And`

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

### D087: `Eq`

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

### D088: `Exists`

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

Fully explicit type:

```lean
(α : Type u_1) → Type u_1
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

Fully explicit type:

```lean
{α : Type u_1} → (f : Filter.{u_1} α) → Prop
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HAdd.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D092: `HMul.hMul`

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

### D093: `LE.le`

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

### D094: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D095: `Nat`

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

### D096: `OfNat.ofNat`

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

### D097: `Real`

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

### D098: `Real.instAdd`

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

### D099: `Real.instMul`

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

Fully explicit type:

```lean
{α : Type u_1} → [Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
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

### D102: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D103: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D104: `instOfNatNat`

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

### D105: `DivInvMonoid.toDiv`

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

### D106: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → (p : α → Prop) → (f : Filter.{u_1} α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D107: `Fin`

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

### D108: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D109: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D110: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D111: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D112: `HDiv.hDiv`

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

### D113: `HPow.hPow`

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

### D114: `HSub.hSub`

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

### D115: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D116: `Monoid.toNatPow`

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

### D117: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D118: `Pi.instSub`

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

### D119: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D120: `Real.instAddGroup`

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

### D121: `Real.instDivInvMonoid`

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

### D122: `Real.instLE`

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

### D123: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D124: `Real.instMonoid`

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

### D125: `Real.instNatCast`

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

### D126: `Real.instSub`

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

### D127: `Real.lattice`

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

### D128: `abs`

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

### D129: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D130: `instHDiv`

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

### D131: `instHPow`

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

### D132: `instHSub`

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

### D133: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Fully explicit type:

```lean
{α : Type u_18} →
  {E : Type u_19} →
    {F : Type u_20} → [Norm.{u_19} E] → [Norm.{u_20} F] → (l : Filter.{u_18} α) → (f : α → E) → (g : α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D134: `Matrix.one`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b68e4dde96dc7da148aa68eb622604137a0c2dec462b5c39bdd02d8b07d2a59d`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → [One α] → One (Matrix n n α)
```

Fully explicit type:

```lean
{n : Type u_3} →
  {α : Type v} → [DecidableEq.{u_3 + 1} n] → [Zero.{v} α] → [One.{v} α] → One.{max v u_3} (Matrix.{u_3, u_3, v} n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] [One α] => { one := Matrix.diagonal fun x => 1 }
```

### D135: `Ne`

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

### D136: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D137: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D138: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D139: `Real.instZero`

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

### D140: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Fully explicit type:

```lean
Norm.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```

### D141: `Real.sqrt`

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

### D142: `Zero.toOfNat0`

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

### D143: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → DecidableEq.{1} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D144: `Fin.castSucc`

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

### D145: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D146: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D147: `Matrix.instL2OpNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.CStarAlgebra.Matrix`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `dc6ff9e1f662ed3b176ef586f3e0ff253c161538742e908216485822af6e00c3`

Type:

```lean
{𝕜 : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} → [RCLike 𝕜] → [Fintype m] → [Fintype n] → [DecidableEq n] → NormedAddCommGroup (Matrix m n 𝕜)
```

Fully explicit type:

```lean
{𝕜 : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      [RCLike.{u_1} 𝕜] →
        [Fintype.{u_2} m] →
          [Fintype.{u_3} n] →
            [DecidableEq.{u_3 + 1} n] → NormedAddCommGroup.{max (max u_1 u_3) u_2} (Matrix.{u_2, u_3, u_1} m n 𝕜)
```

Definition body (one-level semantic boundary):

```lean
fun {𝕜} {m} {n} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n] =>
  { toNorm := Matrix.l2OpNormedAddCommGroupAux.toNorm, toAddCommGroup := Matrix.addCommGroup,
    toMetricSpace := Matrix.instL2OpMetricSpace, dist_eq := ⋯ }
```

### D148: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D149: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D150: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D151: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D152: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`

Type:

```lean
RCLike Real
```

Fully explicit type:

```lean
RCLike.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toDenselyNormedField := Real.denselyNormedField, toStarRing := instStarRingReal,
  toNormedAlgebra := NormedAlgebra.id Real, toCompleteSpace := Real.instCompleteSpace, re := AddMonoidHom.id Real,
  im := 0, I := 0, I_re_ax := Real.instRCLike._proof_1, I_mul_I_ax := Real.instRCLike._proof_8, re_add_im_ax := ⋯,
  ofReal_re_ax := Real.instRCLike._proof_11, ofReal_im_ax := Real.instRCLike._proof_12, mul_re_ax := ⋯, mul_im_ax := ⋯,
  conj_re_ax := ⋯, conj_im_ax := ⋯, conj_I_ax := Real.instRCLike._proof_7, norm_sq_eq_def_ax := ⋯, mul_im_I_ax := ⋯,
  toPartialOrder := Real.partialOrder, le_iff_re_im := @Real.instRCLike._proof_13, toDecidableEq := Real.decidableEq }
```

### D153: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → (f : α → β) → (l₁ : Filter.{u_1} α) → (l₂ : Filter.{u_2} β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D154: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D155: `Function.Injective`

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

### D156: `Matrix.frobeniusNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D157: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero.{v} α] → Zero.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D158: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : PseudoMetricSpace.{u} α] → UniformSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D159: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D160: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `9c0d1d56a04dd3ae3fce36b5fb3c2f4fe632c2bdaed84b5667c1a60a03491a3e`

Type:

```lean
PseudoMetricSpace Real
```

Fully explicit type:

```lean
PseudoMetricSpace.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ dist := fun x y => abs (instHSub.hSub x y), dist_self := Real.pseudoMetricSpace._proof_1, dist_comm := ⋯,
  dist_triangle := ⋯, edist_dist := Real.pseudoMetricSpace._proof_2, uniformity_dist := Real.pseudoMetricSpace._proof_3,
  cobounded_sets := Real.pseudoMetricSpace._proof_4 }
```

### D161: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : UniformSpace.{u} α] → TopologicalSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D162: `instDecidableEqNat`

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

### D163: `ite`

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

### D164: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Fully explicit type:

```lean
{X : Type u_3} → [TopologicalSpace.{u_3} X] → (x : X) → Filter.{u_3} X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```
