# Declaration dossier for P19-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t2_modular_gmres_forward_error
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (execution : P19Theorem31Execution (n := n) l) :
    ∃ k : ℕ,
      k = execution.run.keyDimension ∧
        0 < k ∧ k ≤ n ∧
          (∀ᶠ t in l,
            1 / (execution.run.vHatSpectrum t).sigmaMin ≤ 4 / 3 ∧
              (execution.run.vHatSpectrum t).sigmaMax ≤ 4 / 3) ∧
          ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
            let analysis := execution.forwardAnalysis MR MRinv hMR
            p19FirstOrderLeAt l (p19PrecisionScale execution.run)
              (fun t ↦ p19ForwardError execution.run.xExact (execution.run.xHat t))
              (fun t ↦
                p19PolynomialFactorValue execution.run.polynomialFactor n k *
                  p19Xi execution.run MR MRinv analysis.quantities t *
                  p19ConditionNumberF
                    (p19SplitOperator execution.run MRinv)
                    (p19SplitInverse execution.run MR))
```

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (execution : HighamBench.P19Theorem31Execution l),
  Exists fun k =>
    And (Eq k execution.run.keyDimension)
      (And (instLTNat.lt 0 k)
        (And (instLENat.le k n)
          (And
            (Filter.Eventually
              (fun t =>
                And (Real.instLE.le (instHDiv.hDiv 1 (execution.run.vHatSpectrum t).sigmaMin) (4 / 3))
                  (Real.instLE.le (execution.run.vHatSpectrum t).sigmaMax (4 / 3)))
              l)
            (∀ (MR MRinv : HighamBench.P19Matrix n) (hMR : HighamBench.p19InversePair MR MRinv),
              have analysis := execution.forwardAnalysis MR MRinv hMR;
              HighamBench.p19FirstOrderLeAt l (HighamBench.p19PrecisionScale execution.run)
                (fun t => HighamBench.p19ForwardError execution.run.xExact (execution.run.xHat t)) fun t =>
                instHMul.hMul
                  (instHMul.hMul (HighamBench.p19PolynomialFactorValue execution.run.polynomialFactor n k)
                    (HighamBench.p19Xi execution.run MR MRinv analysis.quantities t))
                  (HighamBench.p19ConditionNumberF (HighamBench.p19SplitOperator execution.run MRinv)
                    (HighamBench.p19SplitInverse execution.run MR))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (execution : @HighamBench.P19Theorem31Execution.{u_1} n ι l),
  @Exists.{1} Nat fun (k : Nat) =>
    And
      (@Eq.{1} Nat k
        (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
          (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution)))
      (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        (And (@LE.le.{0} Nat instLENat k n)
          (And
            (@Filter.Eventually.{u_1} ι
              (fun (t : ι) =>
                And
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HighamBench.P19SingularValueData.sigmaMin n
                        (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
                          (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution))
                        (@HighamBench.P19ModularGMRESRun.vHat.{u_1} n ι l
                          (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) t)
                        (@HighamBench.P19ModularGMRESRun.vHatSpectrum.{u_1} n ι l
                          (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) t)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@LE.le.{0} Real Real.instLE
                    (@HighamBench.P19SingularValueData.sigmaMax n
                      (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
                        (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution))
                      (@HighamBench.P19ModularGMRESRun.vHat.{u_1} n ι l
                        (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) t)
                      (@HighamBench.P19ModularGMRESRun.vHatSpectrum.{u_1} n ι l
                        (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) t))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
              l)
            (∀ (MR MRinv : HighamBench.P19Matrix n) (hMR : @HighamBench.p19InversePair n MR MRinv),
              have analysis :
                @HighamBench.P19ForwardAnalysis.{u_1} n ι l
                  (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) MR MRinv :=
                @HighamBench.P19Theorem31Execution.forwardAnalysis.{u_1} n ι l execution MR MRinv hMR;
              @HighamBench.p19FirstOrderLeAt.{u_1} ι l
                (@HighamBench.p19PrecisionScale.{u_1} n ι l
                  (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution))
                (fun (t : ι) =>
                  @HighamBench.p19ForwardError n
                    (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l
                      (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution))
                    (@HighamBench.P19ModularGMRESRun.xHat.{u_1} n ι l
                      (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) t))
                fun (t : ι) =>
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (HighamBench.p19PolynomialFactorValue
                      (@HighamBench.P19ModularGMRESRun.polynomialFactor.{u_1} n ι l
                        (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution))
                      n k)
                    (@HighamBench.p19Xi.{u_1} n ι l (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) MR
                      MRinv
                      (@HighamBench.P19ForwardAnalysis.quantities.{u_1} n ι l
                        (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) MR MRinv analysis)
                      t))
                  (@HighamBench.p19ConditionNumberF n
                    (@HighamBench.p19SplitOperator.{u_1} n ι l
                      (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) MRinv)
                    (@HighamBench.p19SplitInverse.{u_1} n ι l
                      (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l execution) MR))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P19ForwardAnalysis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9ac83a09bfd7bab55e17ae5c7fc00b601ce16d2b27a44f15a85ddee2cb21891`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → (MR MRinv : HighamBench.P19Matrix n) → Type u_1
```

### D002: `HighamBench.P19ForwardAnalysis.quantities`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0b438ee8658c81f0e84c7639a3f4e9c6775ef1bef01c5a58c2a3dc11dac2c356`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : HighamBench.P19ModularGMRESRun l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          HighamBench.P19ForwardAnalysis run MR MRinv → HighamBench.P19RightPreconditionedQuantities run MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (self : @HighamBench.P19ForwardAnalysis.{u_1} n ι l run MR MRinv) →
            @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n ι l run MR MRinv self => self.1
```

### D003: `HighamBench.P19Matrix`

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

### D004: `HighamBench.P19ModularGMRESRun.keyDimension`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `767f69e4769c4c0becd2befca856b405e9162005c29c09510ea257270525ec38`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → Nat
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.13
```

### D005: `HighamBench.P19ModularGMRESRun.polynomialFactor`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `553771567bab00d42d3938d46e9b207922460f90b77e05070799f49270fe1140`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19PolynomialFactor
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19PolynomialFactor
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.16
```

### D006: `HighamBench.P19ModularGMRESRun.vHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4ac504c95889845aa9c51165baec4964b1578a4c41ec218261e98f1d6e05954b`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : HighamBench.P19ModularGMRESRun l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        ι → HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.31
```

### D007: `HighamBench.P19ModularGMRESRun.vHatSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `14279e80ea4d996a83bca8b47cd3e87afc7ca5416e052d656cb43d2fe52058e0`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (self : HighamBench.P19ModularGMRESRun l) → (t : ι) → HighamBench.P19SingularValueData (self.vHat t)
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (t : ι) →
          @HighamBench.P19SingularValueData n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l self)
            (@HighamBench.P19ModularGMRESRun.vHat.{u_1} n ι l self t)
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.52
```

### D008: `HighamBench.P19ModularGMRESRun.xExact`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cc197682e9da3daeb8ee25b764ecc2be7634b595dbf390f0b556c107ac5399c0`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.7
```

### D009: `HighamBench.P19ModularGMRESRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2324897d125aa383706a0f450a66a8a3717e5ab91749b471f1b1311eeb85e105`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.47
```

### D010: `HighamBench.P19SingularValueData.sigmaMax`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D011: `HighamBench.P19SingularValueData.sigmaMin`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D012: `HighamBench.P19Theorem31Execution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `5b717643c51c82887357e2b74e5fa20e19cb0901d113af9598f0354a6996fd66`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (l : Filter.{u_1} ι) → Type u_1
```

### D013: `HighamBench.P19Theorem31Execution.forwardAnalysis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e1b834f84752ac6d0222710bc13db30a366a5efd6161ae03c36f2945c568a341`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (self : HighamBench.P19Theorem31Execution l) →
        (MR MRinv : HighamBench.P19Matrix n) →
          HighamBench.p19InversePair MR MRinv → HighamBench.P19ForwardAnalysis self.run MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19Theorem31Execution.{u_1} n ι l) →
        (MR MRinv : HighamBench.P19Matrix n) →
          @HighamBench.p19InversePair n MR MRinv →
            @HighamBench.P19ForwardAnalysis.{u_1} n ι l (@HighamBench.P19Theorem31Execution.run.{u_1} n ι l self) MR
              MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D014: `HighamBench.P19Theorem31Execution.run`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a13cc3e797365b0c4a89dfb8193b07af59cf5be5cc83ee580f94bd18113eb0ee`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19Theorem31Execution l → HighamBench.P19ModularGMRESRun l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19Theorem31Execution.{u_1} n ι l) → @HighamBench.P19ModularGMRESRun.{u_1} n ι l
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.1
```

### D015: `HighamBench.p19ConditionNumberF`

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

### D016: `HighamBench.p19FirstOrderLeAt`

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

### D017: `HighamBench.p19ForwardError`

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

### D018: `HighamBench.p19InversePair`

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

### D019: `HighamBench.p19PolynomialFactorValue`

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

### D020: `HighamBench.p19PrecisionScale`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fad5b1a69feb7a1d2c4461019923c00ea4539e608602c407f6db7cbeb1f645a2`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHAdd.hAdd (instHAdd.hAdd (instHAdd.hAdd (run.epsilonC t) (run.epsilonB t)) (run.ug t)) (run.epsilonX t)
```

### D021: `HighamBench.p19SplitInverse`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9477aec818a5cb51663615169812c4e799cb323f77050999d8483829388a05be`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → (MR : HighamBench.P19Matrix n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR => HighamBench.p19SquareRectMul MR (HighamBench.p19SquareRectMul run.Ainv run.ML)
```

### D022: `HighamBench.p19SplitOperator`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4865bff1cf8cab324d5e100bf3645aa19c2a7d74b2d0f8fe3be2945b09440241`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → (MRinv : HighamBench.P19Matrix n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MRinv => HighamBench.p19SquareRectMul run.MLinv (HighamBench.p19SquareRectMul run.A MRinv)
```

### D023: `HighamBench.p19Xi`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe707534cb683a4ab207547ffb88e334426fe75e025851328be68292e8485852`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : HighamBench.P19ModularGMRESRun l) →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19RightPreconditionedQuantities run MR MRinv → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  HighamBench.p19ModularEnvelope (HighamBench.p19Alpha run MR MRinv q t) (HighamBench.p19Beta run MR MRinv q t)
    (HighamBench.p19Lambda run MR MRinv) (run.epsilonC t) (run.epsilonB t) (run.ug t) (run.epsilonX t)
```

### D024: `HighamBench.P19ForwardAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `f65902c46b4d8ef84c868f62ccb61d08728a331e93f2c6a1cbcc883f46c9603e`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : HighamBench.P19ModularGMRESRun l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (quantities : HighamBench.P19RightPreconditionedQuantities run MR MRinv) →
            (computationPropagation : ι → HighamBench.P19RectMatrix n run.keyDimension → HighamBench.P19Vector n) →
              (rhsPropagation leastSquaresBPropagation : ι → HighamBench.P19Vector n → HighamBench.P19Vector n) →
                (leastSquaresCPropagation :
                    ι → HighamBench.P19RectMatrix n run.keyDimension → HighamBench.P19Vector n) →
                  (solutionPropagation : ι → HighamBench.P19Vector n → HighamBench.P19Vector n) →
                    (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                        ι → HighamBench.P19Vector n) →
                      (∀ (t : ι), Eq (computationContribution t) (computationPropagation t (run.deltaC t))) →
                        (∀ (t : ι), Eq (rhsContribution t) (rhsPropagation t (run.deltaB t))) →
                          (∀ (t : ι),
                              Eq (gmresContribution t)
                                (instHAdd.hAdd (leastSquaresBPropagation t (run.leastSquaresDeltaB t))
                                  (leastSquaresCPropagation t (run.leastSquaresDeltaC t)))) →
                            (∀ (t : ι), Eq (solutionContribution t) (solutionPropagation t (run.deltaX t))) →
                              (∀ (t : ι), Eq (computationPropagation t 0) 0) →
                                (∀ (t : ι), Eq (rhsPropagation t 0) 0) →
                                  (∀ (t : ι), Eq (leastSquaresBPropagation t 0) 0) →
                                    (∀ (t : ι), Eq (leastSquaresCPropagation t 0) 0) →
                                      (∀ (t : ι), Eq (solutionPropagation t 0) 0) →
                                        (∀ (t : ι),
                                            Eq (instHSub.hSub (run.xHat t) run.xExact)
                                              (instHAdd.hAdd
                                                (instHAdd.hAdd
                                                  (instHAdd.hAdd
                                                    (instHAdd.hAdd (computationContribution t) (rhsContribution t))
                                                    (gmresContribution t))
                                                  (solutionContribution t))
                                                (remainder t))) →
                                          (∀ (t : ι),
                                              Real.instLE.le
                                                (instHDiv.hDiv (HighamBench.p19VecNorm2 (computationContribution t))
                                                  (HighamBench.p19VecNorm2 run.xExact))
                                                (instHMul.hMul
                                                  (instHMul.hMul
                                                    (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                                      run.keyDimension)
                                                    (HighamBench.p19ConditionNumberF
                                                      (HighamBench.p19SplitOperator run MRinv)
                                                      (HighamBench.p19SplitInverse run MR)))
                                                  (instHMul.hMul (HighamBench.p19Alpha run MR MRinv quantities t)
                                                    (run.epsilonC t)))) →
                                            (∀ (t : ι),
                                                Real.instLE.le
                                                  (instHDiv.hDiv (HighamBench.p19VecNorm2 (rhsContribution t))
                                                    (HighamBench.p19VecNorm2 run.xExact))
                                                  (instHMul.hMul
                                                    (instHMul.hMul
                                                      (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                                        run.keyDimension)
                                                      (HighamBench.p19ConditionNumberF
                                                        (HighamBench.p19SplitOperator run MRinv)
                                                        (HighamBench.p19SplitInverse run MR)))
                                                    (instHMul.hMul (HighamBench.p19Beta run MR MRinv quantities t)
                                                      (run.epsilonB t)))) →
                                              (∀ (t : ι),
                                                  Real.instLE.le
                                                    (instHDiv.hDiv (HighamBench.p19VecNorm2 (gmresContribution t))
                                                      (HighamBench.p19VecNorm2 run.xExact))
                                                    (instHMul.hMul
                                                      (instHMul.hMul
                                                        (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                                          run.keyDimension)
                                                        (HighamBench.p19ConditionNumberF
                                                          (HighamBench.p19SplitOperator run MRinv)
                                                          (HighamBench.p19SplitInverse run MR)))
                                                      (instHMul.hMul (HighamBench.p19Beta run MR MRinv quantities t)
                                                        (run.ug t)))) →
                                                (∀ (t : ι),
                                                    Real.instLE.le
                                                      (instHDiv.hDiv (HighamBench.p19VecNorm2 (solutionContribution t))
                                                        (HighamBench.p19VecNorm2 run.xExact))
                                                      (instHMul.hMul
                                                        (instHMul.hMul
                                                          (HighamBench.p19PolynomialFactorValue run.polynomialFactor n
                                                            run.keyDimension)
                                                          (HighamBench.p19ConditionNumberF
                                                            (HighamBench.p19SplitOperator run MRinv)
                                                            (HighamBench.p19SplitInverse run MR)))
                                                        (instHMul.hMul (HighamBench.p19Lambda run MR MRinv)
                                                          (run.epsilonX t)))) →
                                                  (HighamBench.p19SecondOrderAt l (HighamBench.p19PrecisionScale run)
                                                      fun t =>
                                                      instHDiv.hDiv (HighamBench.p19VecNorm2 (remainder t))
                                                        (HighamBench.p19VecNorm2 run.xExact)) →
                                                    HighamBench.P19ForwardAnalysis run MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (quantities : @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv) →
            (computationPropagation :
                ι →
                  HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) →
                    HighamBench.P19Vector n) →
              (rhsPropagation leastSquaresBPropagation : ι → HighamBench.P19Vector n → HighamBench.P19Vector n) →
                (leastSquaresCPropagation :
                    ι →
                      HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) →
                        HighamBench.P19Vector n) →
                  (solutionPropagation : ι → HighamBench.P19Vector n → HighamBench.P19Vector n) →
                    (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                        ι → HighamBench.P19Vector n) →
                      (computation_link :
                          ∀ (t : ι),
                            @Eq.{1} (HighamBench.P19Vector n) (computationContribution t)
                              (computationPropagation t (@HighamBench.P19ModularGMRESRun.deltaC.{u_1} n ι l run t))) →
                        (rhs_link :
                            ∀ (t : ι),
                              @Eq.{1} (HighamBench.P19Vector n) (rhsContribution t)
                                (rhsPropagation t (@HighamBench.P19ModularGMRESRun.deltaB.{u_1} n ι l run t))) →
                          (gmres_link :
                              ∀ (t : ι),
                                @Eq.{1} (HighamBench.P19Vector n) (gmresContribution t)
                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                    (HighamBench.P19Vector n)
                                    (@instHAdd.{0} (HighamBench.P19Vector n)
                                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        Real.instAdd))
                                    (leastSquaresBPropagation t
                                      (@HighamBench.P19ModularGMRESRun.leastSquaresDeltaB.{u_1} n ι l run t))
                                    (leastSquaresCPropagation t
                                      (@HighamBench.P19ModularGMRESRun.leastSquaresDeltaC.{u_1} n ι l run t)))) →
                            (solution_link :
                                ∀ (t : ι),
                                  @Eq.{1} (HighamBench.P19Vector n) (solutionContribution t)
                                    (solutionPropagation t
                                      (@HighamBench.P19ModularGMRESRun.deltaX.{u_1} n ι l run t))) →
                              (computationPropagation_zero :
                                  ∀ (t : ι),
                                    @Eq.{1} (HighamBench.P19Vector n)
                                      (computationPropagation t
                                        (@OfNat.ofNat.{0}
                                          (HighamBench.P19RectMatrix n
                                            (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                          (nat_lit 0)
                                          (@Zero.toOfNat0.{0}
                                            (HighamBench.P19RectMatrix n
                                              (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                            (@Matrix.zero.{0, 0, 0} (Fin n)
                                              (Fin (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run)) Real
                                              Real.instZero))))
                                      (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                        (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                          (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                            Real.instZero)))) →
                                (rhsPropagation_zero :
                                    ∀ (t : ι),
                                      @Eq.{1} (HighamBench.P19Vector n)
                                        (rhsPropagation t
                                          (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                            (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                              (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                Real.instZero))))
                                        (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                          (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                            (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                              Real.instZero)))) →
                                  (leastSquaresBPropagation_zero :
                                      ∀ (t : ι),
                                        @Eq.{1} (HighamBench.P19Vector n)
                                          (leastSquaresBPropagation t
                                            (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                              (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                                (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                  fun (i : Fin n) => Real.instZero))))
                                          (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                            (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                              (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                Real.instZero)))) →
                                    (leastSquaresCPropagation_zero :
                                        ∀ (t : ι),
                                          @Eq.{1} (HighamBench.P19Vector n)
                                            (leastSquaresCPropagation t
                                              (@OfNat.ofNat.{0}
                                                (HighamBench.P19RectMatrix n
                                                  (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                                (nat_lit 0)
                                                (@Zero.toOfNat0.{0}
                                                  (HighamBench.P19RectMatrix n
                                                    (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                                  (@Matrix.zero.{0, 0, 0} (Fin n)
                                                    (Fin (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                                    Real Real.instZero))))
                                            (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                              (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                                (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                  fun (i : Fin n) => Real.instZero)))) →
                                      (solutionPropagation_zero :
                                          ∀ (t : ι),
                                            @Eq.{1} (HighamBench.P19Vector n)
                                              (solutionPropagation t
                                                (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                                    (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                      fun (i : Fin n) => Real.instZero))))
                                              (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                                (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                                  (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                    fun (i : Fin n) => Real.instZero)))) →
                                        (error_decomposition :
                                            ∀ (t : ι),
                                              @Eq.{1} (HighamBench.P19Vector n)
                                                (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n)
                                                  (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                  (@instHSub.{0} (HighamBench.P19Vector n)
                                                    (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                      fun (i : Fin n) => Real.instSub))
                                                  (@HighamBench.P19ModularGMRESRun.xHat.{u_1} n ι l run t)
                                                  (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run))
                                                (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                  (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                  (@instHAdd.{0} (HighamBench.P19Vector n)
                                                    (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                      fun (i : Fin n) => Real.instAdd))
                                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                    (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                    (@instHAdd.{0} (HighamBench.P19Vector n)
                                                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                        fun (i : Fin n) => Real.instAdd))
                                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                      (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                      (@instHAdd.{0} (HighamBench.P19Vector n)
                                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                          fun (i : Fin n) => Real.instAdd))
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                        (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                        (@instHAdd.{0} (HighamBench.P19Vector n)
                                                          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                            fun (i : Fin n) => Real.instAdd))
                                                        (computationContribution t) (rhsContribution t))
                                                      (gmresContribution t))
                                                    (solutionContribution t))
                                                  (remainder t))) →
                                          (computation_bound :
                                              ∀ (t : ι),
                                                @LE.le.{0} Real Real.instLE
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@HighamBench.p19VecNorm2 n (computationContribution t))
                                                    (@HighamBench.p19VecNorm2 n
                                                      (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run)))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (HighamBench.p19PolynomialFactorValue
                                                        (@HighamBench.P19ModularGMRESRun.polynomialFactor.{u_1} n ι l
                                                          run)
                                                        n
                                                        (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run))
                                                      (@HighamBench.p19ConditionNumberF n
                                                        (@HighamBench.p19SplitOperator.{u_1} n ι l run MRinv)
                                                        (@HighamBench.p19SplitInverse.{u_1} n ι l run MR)))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HighamBench.p19Alpha.{u_1} n ι l run MR MRinv quantities t)
                                                      (@HighamBench.P19ModularGMRESRun.epsilonC.{u_1} n ι l run t)))) →
                                            (rhs_bound :
                                                ∀ (t : ι),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                      (@instHDiv.{0} Real
                                                        (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                      (@HighamBench.p19VecNorm2 n (rhsContribution t))
                                                      (@HighamBench.p19VecNorm2 n
                                                        (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run)))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (HighamBench.p19PolynomialFactorValue
                                                          (@HighamBench.P19ModularGMRESRun.polynomialFactor.{u_1} n ι l
                                                            run)
                                                          n
                                                          (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
                                                            run))
                                                        (@HighamBench.p19ConditionNumberF n
                                                          (@HighamBench.p19SplitOperator.{u_1} n ι l run MRinv)
                                                          (@HighamBench.p19SplitInverse.{u_1} n ι l run MR)))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HighamBench.p19Beta.{u_1} n ι l run MR MRinv quantities t)
                                                        (@HighamBench.P19ModularGMRESRun.epsilonB.{u_1} n ι l run
                                                          t)))) →
                                              (gmres_bound :
                                                  ∀ (t : ι),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@HighamBench.p19VecNorm2 n (gmresContribution t))
                                                        (@HighamBench.p19VecNorm2 n
                                                          (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run)))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (HighamBench.p19PolynomialFactorValue
                                                            (@HighamBench.P19ModularGMRESRun.polynomialFactor.{u_1} n ι
                                                              l run)
                                                            n
                                                            (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
                                                              run))
                                                          (@HighamBench.p19ConditionNumberF n
                                                            (@HighamBench.p19SplitOperator.{u_1} n ι l run MRinv)
                                                            (@HighamBench.p19SplitInverse.{u_1} n ι l run MR)))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (@HighamBench.p19Beta.{u_1} n ι l run MR MRinv quantities t)
                                                          (@HighamBench.P19ModularGMRESRun.ug.{u_1} n ι l run t)))) →
                                                (solution_bound :
                                                    ∀ (t : ι),
                                                      @LE.le.{0} Real Real.instLE
                                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                          (@instHDiv.{0} Real
                                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                          (@HighamBench.p19VecNorm2 n (solutionContribution t))
                                                          (@HighamBench.p19VecNorm2 n
                                                            (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run)))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (HighamBench.p19PolynomialFactorValue
                                                              (@HighamBench.P19ModularGMRESRun.polynomialFactor.{u_1} n
                                                                ι l run)
                                                              n
                                                              (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l
                                                                run))
                                                            (@HighamBench.p19ConditionNumberF n
                                                              (@HighamBench.p19SplitOperator.{u_1} n ι l run MRinv)
                                                              (@HighamBench.p19SplitInverse.{u_1} n ι l run MR)))
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (@HighamBench.p19Lambda.{u_1} n ι l run MR MRinv)
                                                            (@HighamBench.P19ModularGMRESRun.epsilonX.{u_1} n ι l run
                                                              t)))) →
                                                  (remainder_second_order :
                                                      @HighamBench.p19SecondOrderAt.{u_1} ι l
                                                        (@HighamBench.p19PrecisionScale.{u_1} n ι l run) fun (t : ι) =>
                                                        @HDiv.hDiv.{0, 0, 0} Real Real Real
                                                          (@instHDiv.{0} Real
                                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                          (@HighamBench.p19VecNorm2 n (remainder t))
                                                          (@HighamBench.p19VecNorm2 n
                                                            (@HighamBench.P19ModularGMRESRun.xExact.{u_1} n ι l run))) →
                                                    @HighamBench.P19ForwardAnalysis.{u_1} n ι l run MR MRinv
```

### D025: `HighamBench.P19ModularGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6c5961570fb514c1634dc4e0e0a4185d234ac058cd3dfb106326004fc13fdbda`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (l : Filter.{u_1} ι) → Type u_1
```

### D026: `HighamBench.P19ModularGMRESRun.A`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0ce3a906eed62528020a8c781eb29417572547dfafaeed377c4b63b4562b14c2`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D027: `HighamBench.P19ModularGMRESRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `71cdba8088718feb6bf0c74041ed1089da00356008a16b896dfe855d1e95a6a7`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.3
```

### D028: `HighamBench.P19ModularGMRESRun.ML`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b481783919dde74d3043e6900772f3a93ea4e0ed28802a1668d3238d6fa50ecd`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.4
```

### D029: `HighamBench.P19ModularGMRESRun.MLinv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f770cefa03e5dfb30cbeaa365932555ca4822ad26ee0dee8f64159af97cb8696`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.5
```

### D030: `HighamBench.P19ModularGMRESRun.epsilonB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `432a7da4065c28bef283f93899aa0e147a4eb1d543ceeee6de6da6304d8df53c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.18
```

### D031: `HighamBench.P19ModularGMRESRun.epsilonC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bcc2a28e246363fff15906f5bf38b406f655185faac9565c2d08ec471ceab3ce`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.17
```

### D032: `HighamBench.P19ModularGMRESRun.epsilonX`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a79118e51524a23c26ab3bf88605cc5ad6b9dbc9e6867e9eca95f0f3a4250ba5`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.20
```

### D033: `HighamBench.P19ModularGMRESRun.ug`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d1fafdb6c4a35d493154f8a360635ed5256777015c8239006ace146575fc2161`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.19
```

### D034: `HighamBench.P19PolynomialFactor`

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

### D035: `HighamBench.P19PolynomialFactor.coefficient`

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

### D036: `HighamBench.P19PolynomialFactor.degreeK`

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

### D037: `HighamBench.P19PolynomialFactor.degreeN`

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

### D038: `HighamBench.P19RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D039: `HighamBench.P19RightPreconditionedQuantities`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ecfe7f38d457064664c1e9d39d7e4ce312574c629a9618863967a345704ba3d4`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → (MR MRinv : HighamBench.P19Matrix n) → Type u_1
```

### D040: `HighamBench.P19SingularValueData`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Type
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → Type
```

### D041: `HighamBench.P19Theorem31Execution.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `9ad26490b78040e4a2cce78f162e37d95460fd67371e05744ce5b9388396fd19`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : HighamBench.P19ModularGMRESRun l) →
        ((MR MRinv : HighamBench.P19Matrix n) →
            HighamBench.p19InversePair MR MRinv → HighamBench.P19ForwardAnalysis run MR MRinv) →
          HighamBench.P19Theorem31Execution l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (forwardAnalysis :
            (MR MRinv : HighamBench.P19Matrix n) →
              @HighamBench.p19InversePair n MR MRinv → @HighamBench.P19ForwardAnalysis.{u_1} n ι l run MR MRinv) →
          @HighamBench.P19Theorem31Execution.{u_1} n ι l
```

### D042: `HighamBench.P19Vector`

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

### D043: `HighamBench.p19Alpha`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a56cbd7beb408e81cc0a8e5a16bd3803326cbca2db7a8b5f7df6483ee236b456`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : HighamBench.P19ModularGMRESRun l) →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19RightPreconditionedQuantities run MR MRinv → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  instHMul.hMul (instHDiv.hDiv (HighamBench.p19ConditionNumberF MR MRinv) (q.mrzSpectrum t).sigmaMin)
    (instHDiv.hDiv (HighamBench.p19FrobNorm (HighamBench.p19ExactC run t))
      (HighamBench.p19FrobNorm (HighamBench.p19SplitOperator run MRinv)))
```

### D044: `HighamBench.p19Beta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ccf45d1b3776c1251f48b362abde5d03cc4fc98635c4acddcfa679d206528bed`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : HighamBench.P19ModularGMRESRun l) →
        (MR MRinv : HighamBench.P19Matrix n) → HighamBench.P19RightPreconditionedQuantities run MR MRinv → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (MR MRinv : HighamBench.P19Matrix n) →
          (q : @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  instHMul.hMul
    (Real.instMax.max 1
      (instHDiv.hDiv
        (instHDiv.hDiv (HighamBench.p19FrobNorm (HighamBench.p19ExactC run t))
          (HighamBench.p19FrobNorm (HighamBench.p19SplitOperator run MRinv)))
        (q.mrzSpectrum t).sigmaMin))
    (HighamBench.p19ConditionNumberF MR MRinv)
```

### D045: `HighamBench.p19FrobNorm`

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

### D046: `HighamBench.p19Lambda`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a4138ec36bd4cba05513fd06dbc017aea3f59e262d7bde78e234fcd23b2326b0`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → (MR MRinv : HighamBench.P19Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv =>
  instHDiv.hDiv 1
    (HighamBench.p19ConditionNumberF (HighamBench.p19SplitOperator run MRinv) (HighamBench.p19SplitInverse run MR))
```

### D047: `HighamBench.p19MatVec`

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

### D048: `HighamBench.p19ModularEnvelope`

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

### D049: `HighamBench.p19SecondOrderAt`

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

### D050: `HighamBench.p19SquareRectMul`

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

### D051: `HighamBench.p19VecNorm2`

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

### D052: `HighamBench.P19IncreasingBasisFamily.basis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ea70ac01cbc08de52a454d21e6f55d67e23415834c4fb2a7940ceb5c80c625ea`

Type:

```lean
{n : Nat} → {ι : Type u_1} → HighamBench.P19IncreasingBasisFamily n ι → (k : Nat) → ι → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (self : HighamBench.P19IncreasingBasisFamily.{u_1} n ι) → (k : Nat) → ι → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun n ι self => self.1
```

### D053: `HighamBench.P19ModularGMRESRun.basisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `feda3a60d7050f57efdd50df71f0c36c7444163064341d357a47344c0d29e661`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → HighamBench.P19IncreasingBasisFamily n ι
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → HighamBench.P19IncreasingBasisFamily.{u_1} n ι
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.12
```

### D054: `HighamBench.P19ModularGMRESRun.deltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d22832f89b0e15884606c8362a4d72a1625e89283cd8ce30c1f839cba9a7a703`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.28
```

### D055: `HighamBench.P19ModularGMRESRun.deltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `429a7a1f66277b258a86c83b66387d1fc1c862f79b8dd9fc6dd9d157051262f5`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : HighamBench.P19ModularGMRESRun l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        ι → HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.24
```

### D056: `HighamBench.P19ModularGMRESRun.deltaX`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a6637cee9f79cabbed0a9d377c77096d77165a541c22205e8316c5ed64a4a9c5`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.48
```

### D057: `HighamBench.P19ModularGMRESRun.leastSquaresDeltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e74dc228173db84ea616b718ea11d8b43e0f7fbd545bbaab8e4a92662285f8ac`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P19ModularGMRESRun l → ι → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) → ι → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.38
```

### D058: `HighamBench.P19ModularGMRESRun.leastSquaresDeltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9a0e064298849ae0d2110809ff753ce1bcbf99b53936f5efd4d91874308b9ed9`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : HighamBench.P19ModularGMRESRun l) → ι → HighamBench.P19RectMatrix n self.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        ι → HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l self)
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.39
```

### D059: `HighamBench.P19ModularGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `8b3be08a29236a310e5547e060c838db69a40536fc680c23a42640826bd2af54`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      instLTNat.lt 0 n →
        (A Ainv ML MLinv : HighamBench.P19Matrix n) →
          (b xExact : HighamBench.P19Vector n) →
            HighamBench.p19InversePair A Ainv →
              HighamBench.p19InversePair ML MLinv →
                Ne b 0 →
                  Eq (HighamBench.p19MatVec A xExact) b →
                    (basisFamily : HighamBench.P19IncreasingBasisFamily n ι) →
                      (keyDimension : Nat) →
                        instLTNat.lt 0 keyDimension →
                          instLENat.le keyDimension n →
                            (polynomialFactor : HighamBench.P19PolynomialFactor) →
                              (epsilonC epsilonB ug epsilonX : ι → Real) →
                                (∀ (t : ι),
                                    And (Real.instLE.le 0 (epsilonC t))
                                      (And (Real.instLE.le 0 (epsilonB t))
                                        (And (Real.instLE.le 0 (ug t)) (Real.instLE.le 0 (epsilonX t))))) →
                                  And (Filter.Tendsto epsilonC l (nhds 0))
                                      (And (Filter.Tendsto epsilonB l (nhds 0))
                                        (And (Filter.Tendsto ug l (nhds 0)) (Filter.Tendsto epsilonX l (nhds 0)))) →
                                    (computedC deltaC : ι → HighamBench.P19RectMatrix n keyDimension) →
                                      (∀ (t : ι),
                                          Eq (computedC t)
                                            (instHAdd.hAdd
                                              (HighamBench.p19SquareRectMul MLinv
                                                (HighamBench.p19SquareRectMul A (basisFamily.basis keyDimension t)))
                                              (deltaC t))) →
                                        (∀ (t : ι),
                                            Real.instLE.le (HighamBench.p19FrobNorm (deltaC t))
                                              (instHMul.hMul (epsilonC t)
                                                (HighamBench.p19FrobNorm
                                                  (HighamBench.p19SquareRectMul MLinv
                                                    (HighamBench.p19SquareRectMul A
                                                      (basisFamily.basis keyDimension t)))))) →
                                          (computedB deltaB : ι → HighamBench.P19Vector n) →
                                            (∀ (t : ι),
                                                Eq (computedB t)
                                                  (instHAdd.hAdd (HighamBench.p19MatVec MLinv b) (deltaB t))) →
                                              (∀ (t : ι),
                                                  Real.instLE.le (HighamBench.p19VecNorm2 (deltaB t))
                                                    (instHMul.hMul (epsilonB t)
                                                      (HighamBench.p19VecNorm2 (HighamBench.p19MatVec MLinv b)))) →
                                                (vHat : ι → HighamBench.P19RectMatrix n keyDimension) →
                                                  (vHatNext :
                                                      ι → HighamBench.P19RectMatrix n (instHAdd.hAdd keyDimension 1)) →
                                                    (beta : ι → Real) →
                                                      (hessenberg :
                                                          ι →
                                                            HighamBench.P19RectMatrix (instHAdd.hAdd keyDimension 1)
                                                              keyDimension) →
                                                        (∀ (t : ι), HighamBench.p19IsUpperHessenberg (hessenberg t)) →
                                                          (∀ (t : ι),
                                                              Eq (HighamBench.p19Augment (computedB t) (computedC t))
                                                                (HighamBench.p19RectMatMul (vHatNext t)
                                                                  (HighamBench.p19Augment
                                                                    (HighamBench.p19ScaledFirstBasisVector (beta t))
                                                                    (hessenberg t)))) →
                                                            (∀ (t : ι) (i : Fin n) (j : Fin keyDimension),
                                                                Eq (vHat t i j) (vHatNext t i j.castSucc)) →
                                                              (leastSquaresDeltaB : ι → HighamBench.P19Vector n) →
                                                                (leastSquaresDeltaC :
                                                                    ι → HighamBench.P19RectMatrix n keyDimension) →
                                                                  (yHat : ι → HighamBench.P19Vector keyDimension) →
                                                                    (∀ (t : ι),
                                                                        HighamBench.p19IsLeastSquaresSolution
                                                                          (instHAdd.hAdd (computedC t)
                                                                            (leastSquaresDeltaC t))
                                                                          (instHAdd.hAdd (computedB t)
                                                                            (leastSquaresDeltaB t))
                                                                          (yHat t)) →
                                                                      (∀ (t : ι)
                                                                          (j : Fin (instHAdd.hAdd keyDimension 1)),
                                                                          Real.instLE.le
                                                                            (HighamBench.p19VecNorm2
                                                                              (HighamBench.p19Column
                                                                                (HighamBench.p19Augment
                                                                                  (leastSquaresDeltaB t)
                                                                                  (leastSquaresDeltaC t))
                                                                                j))
                                                                            (instHMul.hMul
                                                                              (instHMul.hMul
                                                                                (HighamBench.p19PolynomialFactorValue
                                                                                  polynomialFactor n keyDimension)
                                                                                (ug t))
                                                                              (HighamBench.p19VecNorm2
                                                                                (HighamBench.p19Column
                                                                                  (HighamBench.p19Augment (computedB t)
                                                                                    (computedC t))
                                                                                  j)))) →
                                                                        (computedCSpectrum :
                                                                            (t : ι) →
                                                                              HighamBench.P19SingularValueData
                                                                                (computedC t)) →
                                                                          (HighamBench.p19MuchLessThanOneAt l fun t =>
                                                                              instHMul.hMul (ug t)
                                                                                (HighamBench.p19RectConditionF2
                                                                                  (computedC t)
                                                                                  (computedCSpectrum t).sigmaMin)) →
                                                                            (exactCSpectrum :
                                                                                (t : ι) →
                                                                                  HighamBench.P19SingularValueData
                                                                                    (HighamBench.p19SquareRectMul MLinv
                                                                                      (HighamBench.p19SquareRectMul A
                                                                                        (basisFamily.basis keyDimension
                                                                                          t)))) →
                                                                              (HighamBench.p19MuchLessThanOneAt l
                                                                                  fun t =>
                                                                                  instHMul.hMul
                                                                                    (instHAdd.hAdd
                                                                                      (instHAdd.hAdd (epsilonC t)
                                                                                        (epsilonB t))
                                                                                      (ug t))
                                                                                    (HighamBench.p19RectConditionF2
                                                                                      (HighamBench.p19SquareRectMul
                                                                                        MLinv
                                                                                        (HighamBench.p19SquareRectMul A
                                                                                          (basisFamily.basis
                                                                                            keyDimension t)))
                                                                                      (exactCSpectrum t).sigmaMin)) →
                                                                                (xHat deltaX :
                                                                                    ι → HighamBench.P19Vector n) →
                                                                                  (∀ (t : ι),
                                                                                      Eq (xHat t)
                                                                                        (instHAdd.hAdd
                                                                                          (HighamBench.p19RectMatVec
                                                                                            (basisFamily.basis
                                                                                              keyDimension t)
                                                                                            (yHat t))
                                                                                          (deltaX t))) →
                                                                                    (∀ (t : ι),
                                                                                        Real.instLE.le
                                                                                          (HighamBench.p19VecNorm2
                                                                                            (deltaX t))
                                                                                          (instHMul.hMul (epsilonX t)
                                                                                            (HighamBench.p19VecNorm2
                                                                                              (HighamBench.p19RectMatVec
                                                                                                (basisFamily.basis
                                                                                                  keyDimension t)
                                                                                                (yHat t))))) →
                                                                                      HighamBench.p19MuchLessThanOneAt l
                                                                                          epsilonX →
                                                                                        (vHatSpectrum :
                                                                                            (t : ι) →
                                                                                              HighamBench.P19SingularValueData
                                                                                                (vHat t)) →
                                                                                          (mgsOrthogonalityDefect :
                                                                                              ι → Real) →
                                                                                            (∀ (t : ι),
                                                                                                Real.instLE.le 0
                                                                                                  (mgsOrthogonalityDefect
                                                                                                    t)) →
                                                                                              Filter.Eventually
                                                                                                  (fun t =>
                                                                                                    Real.instLE.le
                                                                                                      (mgsOrthogonalityDefect
                                                                                                        t)
                                                                                                      (7 / 16))
                                                                                                  l →
                                                                                                (∀ (t : ι),
                                                                                                    Real.instLE.le
                                                                                                      (instHSub.hSub 1
                                                                                                        (mgsOrthogonalityDefect
                                                                                                          t))
                                                                                                      (instHPow.hPow
                                                                                                        (vHatSpectrum
                                                                                                            t).sigmaMin
                                                                                                        2)) →
                                                                                                  (∀ (t : ι),
                                                                                                      Real.instLE.le
                                                                                                        (instHPow.hPow
                                                                                                          (vHatSpectrum
                                                                                                              t).sigmaMax
                                                                                                          2)
                                                                                                        (instHAdd.hAdd 1
                                                                                                          (mgsOrthogonalityDefect
                                                                                                            t))) →
                                                                                                    HighamBench.P19ModularGMRESRun
                                                                                                      l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
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
                    (basisFamily : HighamBench.P19IncreasingBasisFamily.{u_1} n ι) →
                      (keyDimension : Nat) →
                        (keyDimension_pos :
                            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              keyDimension) →
                          (keyDimension_le : @LE.le.{0} Nat instLENat keyDimension n) →
                            (polynomialFactor : HighamBench.P19PolynomialFactor) →
                              (epsilonC epsilonB ug epsilonX : ι → Real) →
                                (accuracy_nonneg :
                                    ∀ (t : ι),
                                      And
                                        (@LE.le.{0} Real Real.instLE
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          (epsilonC t))
                                        (And
                                          (@LE.le.{0} Real Real.instLE
                                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                            (epsilonB t))
                                          (And
                                            (@LE.le.{0} Real Real.instLE
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                              (ug t))
                                            (@LE.le.{0} Real Real.instLE
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                              (epsilonX t))))) →
                                  (accuracy_tendsto_zero :
                                      And
                                        (@Filter.Tendsto.{u_1, 0} ι Real epsilonC l
                                          (@nhds.{0} Real
                                            (@UniformSpace.toTopologicalSpace.{0} Real
                                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                              (@Zero.toOfNat0.{0} Real Real.instZero))))
                                        (And
                                          (@Filter.Tendsto.{u_1, 0} ι Real epsilonB l
                                            (@nhds.{0} Real
                                              (@UniformSpace.toTopologicalSpace.{0} Real
                                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero))))
                                          (And
                                            (@Filter.Tendsto.{u_1, 0} ι Real ug l
                                              (@nhds.{0} Real
                                                (@UniformSpace.toTopologicalSpace.{0} Real
                                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero))))
                                            (@Filter.Tendsto.{u_1, 0} ι Real epsilonX l
                                              (@nhds.{0} Real
                                                (@UniformSpace.toTopologicalSpace.{0} Real
                                                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero))))))) →
                                    (computedC deltaC : ι → HighamBench.P19RectMatrix n keyDimension) →
                                      (computation_equation :
                                          ∀ (t : ι),
                                            @Eq.{1} (HighamBench.P19RectMatrix n keyDimension) (computedC t)
                                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19RectMatrix n keyDimension)
                                                (HighamBench.P19RectMatrix n keyDimension)
                                                (HighamBench.P19RectMatrix n keyDimension)
                                                (@instHAdd.{0} (HighamBench.P19RectMatrix n keyDimension)
                                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real Real.instAdd))
                                                (@HighamBench.p19SquareRectMul n keyDimension MLinv
                                                  (@HighamBench.p19SquareRectMul n keyDimension A
                                                    (@HighamBench.P19IncreasingBasisFamily.basis.{u_1} n ι basisFamily
                                                      keyDimension t)))
                                                (deltaC t))) →
                                        (computation_error_bound :
                                            ∀ (t : ι),
                                              @LE.le.{0} Real Real.instLE
                                                (@HighamBench.p19FrobNorm n keyDimension (deltaC t))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (epsilonC t)
                                                  (@HighamBench.p19FrobNorm n keyDimension
                                                    (@HighamBench.p19SquareRectMul n keyDimension MLinv
                                                      (@HighamBench.p19SquareRectMul n keyDimension A
                                                        (@HighamBench.P19IncreasingBasisFamily.basis.{u_1} n ι
                                                          basisFamily keyDimension t)))))) →
                                          (computedB deltaB : ι → HighamBench.P19Vector n) →
                                            (rhs_equation :
                                                ∀ (t : ι),
                                                  @Eq.{1} (HighamBench.P19Vector n) (computedB t)
                                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                      (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                      (@instHAdd.{0} (HighamBench.P19Vector n)
                                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                          fun (i : Fin n) => Real.instAdd))
                                                      (@HighamBench.p19MatVec n MLinv b) (deltaB t))) →
                                              (rhs_error_bound :
                                                  ∀ (t : ι),
                                                    @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 n (deltaB t))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) (epsilonB t)
                                                        (@HighamBench.p19VecNorm2 n
                                                          (@HighamBench.p19MatVec n MLinv b)))) →
                                                (vHat : ι → HighamBench.P19RectMatrix n keyDimension) →
                                                  (vHatNext :
                                                      ι →
                                                        HighamBench.P19RectMatrix n
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) keyDimension
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) →
                                                    (beta : ι → Real) →
                                                      (hessenberg :
                                                          ι →
                                                            HighamBench.P19RectMatrix
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) keyDimension
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              keyDimension) →
                                                        (hessenberg_upper :
                                                            ∀ (t : ι),
                                                              @HighamBench.p19IsUpperHessenberg keyDimension
                                                                (hessenberg t)) →
                                                          (mgs_givens_relation :
                                                              ∀ (t : ι),
                                                                @Eq.{1}
                                                                  (HighamBench.P19RectMatrix n
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) keyDimension
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1)))))
                                                                  (@HighamBench.p19Augment n keyDimension (computedB t)
                                                                    (computedC t))
                                                                  (@HighamBench.p19RectMatMul n
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) keyDimension
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) keyDimension
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))
                                                                    (vHatNext t)
                                                                    (@HighamBench.p19Augment
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) keyDimension
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1))))
                                                                      keyDimension
                                                                      (@HighamBench.p19ScaledFirstBasisVector
                                                                        keyDimension (beta t))
                                                                      (hessenberg t)))) →
                                                            (vHat_prefix :
                                                                ∀ (t : ι) (i : Fin n) (j : Fin keyDimension),
                                                                  @Eq.{1} Real (vHat t i j)
                                                                    (vHatNext t i (@Fin.castSucc keyDimension j))) →
                                                              (leastSquaresDeltaB : ι → HighamBench.P19Vector n) →
                                                                (leastSquaresDeltaC :
                                                                    ι → HighamBench.P19RectMatrix n keyDimension) →
                                                                  (yHat : ι → HighamBench.P19Vector keyDimension) →
                                                                    (least_squares_solution :
                                                                        ∀ (t : ι),
                                                                          @HighamBench.p19IsLeastSquaresSolution n
                                                                            keyDimension
                                                                            (@HAdd.hAdd.{0, 0, 0}
                                                                              (HighamBench.P19RectMatrix n keyDimension)
                                                                              (HighamBench.P19RectMatrix n keyDimension)
                                                                              (HighamBench.P19RectMatrix n keyDimension)
                                                                              (@instHAdd.{0}
                                                                                (HighamBench.P19RectMatrix n
                                                                                  keyDimension)
                                                                                (@Matrix.add.{0, 0, 0} (Fin n)
                                                                                  (Fin keyDimension) Real Real.instAdd))
                                                                              (computedC t) (leastSquaresDeltaC t))
                                                                            (@HAdd.hAdd.{0, 0, 0}
                                                                              (HighamBench.P19Vector n)
                                                                              (HighamBench.P19Vector n)
                                                                              (HighamBench.P19Vector n)
                                                                              (@instHAdd.{0} (HighamBench.P19Vector n)
                                                                                (@Pi.instAdd.{0, 0} (Fin n)
                                                                                  (fun (a : Fin n) => Real)
                                                                                  fun (i : Fin n) => Real.instAdd))
                                                                              (computedB t) (leastSquaresDeltaB t))
                                                                            (yHat t)) →
                                                                      (least_squares_column_bound :
                                                                          ∀ (t : ι)
                                                                            (j :
                                                                              Fin
                                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                                  keyDimension
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                    (instOfNatNat (nat_lit 1))))),
                                                                            @LE.le.{0} Real Real.instLE
                                                                              (@HighamBench.p19VecNorm2 n
                                                                                (@HighamBench.p19Column n
                                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                                    keyDimension
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                      (instOfNatNat (nat_lit 1))))
                                                                                  (@HighamBench.p19Augment n
                                                                                    keyDimension (leastSquaresDeltaB t)
                                                                                    (leastSquaresDeltaC t))
                                                                                  j))
                                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                (@instHMul.{0} Real Real.instMul)
                                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul)
                                                                                  (HighamBench.p19PolynomialFactorValue
                                                                                    polynomialFactor n keyDimension)
                                                                                  (ug t))
                                                                                (@HighamBench.p19VecNorm2 n
                                                                                  (@HighamBench.p19Column n
                                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                                      keyDimension
                                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                        (instOfNatNat (nat_lit 1))))
                                                                                    (@HighamBench.p19Augment n
                                                                                      keyDimension (computedB t)
                                                                                      (computedC t))
                                                                                    j)))) →
                                                                        (computedCSpectrum :
                                                                            (t : ι) →
                                                                              @HighamBench.P19SingularValueData n
                                                                                keyDimension (computedC t)) →
                                                                          (computedC_numerically_nonsingular :
                                                                              @HighamBench.p19MuchLessThanOneAt.{u_1} ι
                                                                                l fun (t : ι) =>
                                                                                @HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul)
                                                                                  (ug t)
                                                                                  (@HighamBench.p19RectConditionF2 n
                                                                                    keyDimension (computedC t)
                                                                                    (@HighamBench.P19SingularValueData.sigmaMin
                                                                                      n keyDimension (computedC t)
                                                                                      (computedCSpectrum t)))) →
                                                                            (exactCSpectrum :
                                                                                (t : ι) →
                                                                                  @HighamBench.P19SingularValueData n
                                                                                    keyDimension
                                                                                    (@HighamBench.p19SquareRectMul n
                                                                                      keyDimension MLinv
                                                                                      (@HighamBench.p19SquareRectMul n
                                                                                        keyDimension A
                                                                                        (@HighamBench.P19IncreasingBasisFamily.basis.{u_1}
                                                                                          n ι basisFamily keyDimension
                                                                                          t)))) →
                                                                              (combined_model_small :
                                                                                  @HighamBench.p19MuchLessThanOneAt.{u_1}
                                                                                    ι l fun (t : ι) =>
                                                                                    @HMul.hMul.{0, 0, 0} Real Real Real
                                                                                      (@instHMul.{0} Real Real.instMul)
                                                                                      (@HAdd.hAdd.{0, 0, 0} Real Real
                                                                                        Real
                                                                                        (@instHAdd.{0} Real
                                                                                          Real.instAdd)
                                                                                        (@HAdd.hAdd.{0, 0, 0} Real Real
                                                                                          Real
                                                                                          (@instHAdd.{0} Real
                                                                                            Real.instAdd)
                                                                                          (epsilonC t) (epsilonB t))
                                                                                        (ug t))
                                                                                      (@HighamBench.p19RectConditionF2 n
                                                                                        keyDimension
                                                                                        (@HighamBench.p19SquareRectMul n
                                                                                          keyDimension MLinv
                                                                                          (@HighamBench.p19SquareRectMul
                                                                                            n keyDimension A
                                                                                            (@HighamBench.P19IncreasingBasisFamily.basis.{u_1}
                                                                                              n ι basisFamily
                                                                                              keyDimension t)))
                                                                                        (@HighamBench.P19SingularValueData.sigmaMin
                                                                                          n keyDimension
                                                                                          (@HighamBench.p19SquareRectMul
                                                                                            n keyDimension MLinv
                                                                                            (@HighamBench.p19SquareRectMul
                                                                                              n keyDimension A
                                                                                              (@HighamBench.P19IncreasingBasisFamily.basis.{u_1}
                                                                                                n ι basisFamily
                                                                                                keyDimension t)))
                                                                                          (exactCSpectrum t)))) →
                                                                                (xHat deltaX :
                                                                                    ι → HighamBench.P19Vector n) →
                                                                                  (solution_equation :
                                                                                      ∀ (t : ι),
                                                                                        @Eq.{1}
                                                                                          (HighamBench.P19Vector n)
                                                                                          (xHat t)
                                                                                          (@HAdd.hAdd.{0, 0, 0}
                                                                                            (HighamBench.P19Vector n)
                                                                                            (HighamBench.P19Vector n)
                                                                                            (HighamBench.P19Vector n)
                                                                                            (@instHAdd.{0}
                                                                                              (HighamBench.P19Vector n)
                                                                                              (@Pi.instAdd.{0, 0}
                                                                                                (Fin n)
                                                                                                (fun (a : Fin n) =>
                                                                                                  Real)
                                                                                                fun (i : Fin n) =>
                                                                                                Real.instAdd))
                                                                                            (@HighamBench.p19RectMatVec
                                                                                              n keyDimension
                                                                                              (@HighamBench.P19IncreasingBasisFamily.basis.{u_1}
                                                                                                n ι basisFamily
                                                                                                keyDimension t)
                                                                                              (yHat t))
                                                                                            (deltaX t))) →
                                                                                    (solution_error_bound :
                                                                                        ∀ (t : ι),
                                                                                          @LE.le.{0} Real Real.instLE
                                                                                            (@HighamBench.p19VecNorm2 n
                                                                                              (deltaX t))
                                                                                            (@HMul.hMul.{0, 0, 0} Real
                                                                                              Real Real
                                                                                              (@instHMul.{0} Real
                                                                                                Real.instMul)
                                                                                              (epsilonX t)
                                                                                              (@HighamBench.p19VecNorm2
                                                                                                n
                                                                                                (@HighamBench.p19RectMatVec
                                                                                                  n keyDimension
                                                                                                  (@HighamBench.P19IncreasingBasisFamily.basis.{u_1}
                                                                                                    n ι basisFamily
                                                                                                    keyDimension t)
                                                                                                  (yHat t))))) →
                                                                                      (solution_small :
                                                                                          @HighamBench.p19MuchLessThanOneAt.{u_1}
                                                                                            ι l epsilonX) →
                                                                                        (vHatSpectrum :
                                                                                            (t : ι) →
                                                                                              @HighamBench.P19SingularValueData
                                                                                                n keyDimension
                                                                                                (vHat t)) →
                                                                                          (mgsOrthogonalityDefect :
                                                                                              ι → Real) →
                                                                                            (mgs_defect_nonneg :
                                                                                                ∀ (t : ι),
                                                                                                  @LE.le.{0} Real
                                                                                                    Real.instLE
                                                                                                    (@OfNat.ofNat.{0}
                                                                                                      Real (nat_lit 0)
                                                                                                      (@Zero.toOfNat0.{0}
                                                                                                        Real
                                                                                                        Real.instZero))
                                                                                                    (mgsOrthogonalityDefect
                                                                                                      t)) →
                                                                                              (mgs_defect_small :
                                                                                                  @Filter.Eventually.{u_1}
                                                                                                    ι
                                                                                                    (fun (t : ι) =>
                                                                                                      @LE.le.{0} Real
                                                                                                        Real.instLE
                                                                                                        (mgsOrthogonalityDefect
                                                                                                          t)
                                                                                                        (@HDiv.hDiv.{0,
                                                                                                              0, 0}
                                                                                                          Real Real Real
                                                                                                          (@instHDiv.{0}
                                                                                                            Real
                                                                                                            (@DivInvMonoid.toDiv.{0}
                                                                                                              Real
                                                                                                              Real.instDivInvMonoid))
                                                                                                          (@OfNat.ofNat.{0}
                                                                                                            Real
                                                                                                            (nat_lit 7)
                                                                                                            (@instOfNatAtLeastTwo.{0}
                                                                                                              Real
                                                                                                              (nat_lit
                                                                                                                7)
                                                                                                              Real.instNatCast
                                                                                                              (@Nat.instAtLeastTwoHAddOfNat
                                                                                                                (@OfNat.ofNat.{0}
                                                                                                                  Nat
                                                                                                                  (nat_lit
                                                                                                                    6)
                                                                                                                  (instOfNatNat
                                                                                                                    (nat_lit
                                                                                                                      6)))
                                                                                                                (@Nat.instNeZeroSucc
                                                                                                                  (@OfNat.ofNat.{0}
                                                                                                                    Nat
                                                                                                                    (nat_lit
                                                                                                                      5)
                                                                                                                    (instOfNatNat
                                                                                                                      (nat_lit
                                                                                                                        5)))))))
                                                                                                          (@OfNat.ofNat.{0}
                                                                                                            Real
                                                                                                            (nat_lit 16)
                                                                                                            (@instOfNatAtLeastTwo.{0}
                                                                                                              Real
                                                                                                              (nat_lit
                                                                                                                16)
                                                                                                              Real.instNatCast
                                                                                                              (@Nat.instAtLeastTwoHAddOfNat
                                                                                                                (@OfNat.ofNat.{0}
                                                                                                                  Nat
                                                                                                                  (nat_lit
                                                                                                                    15)
                                                                                                                  (instOfNatNat
                                                                                                                    (nat_lit
                                                                                                                      15)))
                                                                                                                (@Nat.instNeZeroSucc
                                                                                                                  (@OfNat.ofNat.{0}
                                                                                                                    Nat
                                                                                                                    (nat_lit
                                                                                                                      14)
                                                                                                                    (instOfNatNat
                                                                                                                      (nat_lit
                                                                                                                        14)))))))))
                                                                                                    l) →
                                                                                                (mgs_sigmaMin_sq_lower :
                                                                                                    ∀ (t : ι),
                                                                                                      @LE.le.{0} Real
                                                                                                        Real.instLE
                                                                                                        (@HSub.hSub.{0,
                                                                                                              0, 0}
                                                                                                          Real Real Real
                                                                                                          (@instHSub.{0}
                                                                                                            Real
                                                                                                            Real.instSub)
                                                                                                          (@OfNat.ofNat.{0}
                                                                                                            Real
                                                                                                            (nat_lit 1)
                                                                                                            (@One.toOfNat1.{0}
                                                                                                              Real
                                                                                                              Real.instOne))
                                                                                                          (mgsOrthogonalityDefect
                                                                                                            t))
                                                                                                        (@HPow.hPow.{0,
                                                                                                              0, 0}
                                                                                                          Real Nat Real
                                                                                                          (@instHPow.{0,
                                                                                                                0}
                                                                                                            Real Nat
                                                                                                            (@Monoid.toNatPow.{0}
                                                                                                              Real
                                                                                                              Real.instMonoid))
                                                                                                          (@HighamBench.P19SingularValueData.sigmaMin
                                                                                                            n
                                                                                                            keyDimension
                                                                                                            (vHat t)
                                                                                                            (vHatSpectrum
                                                                                                              t))
                                                                                                          (@OfNat.ofNat.{0}
                                                                                                            Nat
                                                                                                            (nat_lit 2)
                                                                                                            (instOfNatNat
                                                                                                              (nat_lit
                                                                                                                2))))) →
                                                                                                  (mgs_sigmaMax_sq_upper :
                                                                                                      ∀ (t : ι),
                                                                                                        @LE.le.{0} Real
                                                                                                          Real.instLE
                                                                                                          (@HPow.hPow.{0,
                                                                                                                0, 0}
                                                                                                            Real Nat
                                                                                                            Real
                                                                                                            (@instHPow.{0,
                                                                                                                  0}
                                                                                                              Real Nat
                                                                                                              (@Monoid.toNatPow.{0}
                                                                                                                Real
                                                                                                                Real.instMonoid))
                                                                                                            (@HighamBench.P19SingularValueData.sigmaMax
                                                                                                              n
                                                                                                              keyDimension
                                                                                                              (vHat t)
                                                                                                              (vHatSpectrum
                                                                                                                t))
                                                                                                            (@OfNat.ofNat.{0}
                                                                                                              Nat
                                                                                                              (nat_lit
                                                                                                                2)
                                                                                                              (instOfNatNat
                                                                                                                (nat_lit
                                                                                                                  2))))
                                                                                                          (@HAdd.hAdd.{0,
                                                                                                                0, 0}
                                                                                                            Real Real
                                                                                                            Real
                                                                                                            (@instHAdd.{0}
                                                                                                              Real
                                                                                                              Real.instAdd)
                                                                                                            (@OfNat.ofNat.{0}
                                                                                                              Real
                                                                                                              (nat_lit
                                                                                                                1)
                                                                                                              (@One.toOfNat1.{0}
                                                                                                                Real
                                                                                                                Real.instOne))
                                                                                                            (mgsOrthogonalityDefect
                                                                                                              t))) →
                                                                                                    @HighamBench.P19ModularGMRESRun.{u_1}
                                                                                                      n ι l
```

### D060: `HighamBench.P19PolynomialFactor.mk`

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

### D061: `HighamBench.P19RightPreconditionedQuantities.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `0c3f47600c05b183f7722f41b79ef5c4b7faff9a6900372e65146ed02e54da98`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : HighamBench.P19ModularGMRESRun l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (mrzSpectrum :
              (t : ι) →
                HighamBench.P19SingularValueData
                  (HighamBench.p19SquareRectMul MR (run.basisFamily.basis run.keyDimension t))) →
            (∀ (t : ι), Real.instLT.lt 0 (mrzSpectrum t).sigmaMin) →
              HighamBench.P19RightPreconditionedQuantities run MR MRinv
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (mrzSpectrum :
              (t : ι) →
                @HighamBench.P19SingularValueData n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run)
                  (@HighamBench.p19SquareRectMul n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) MR
                    (@HighamBench.P19IncreasingBasisFamily.basis.{u_1} n ι
                      (@HighamBench.P19ModularGMRESRun.basisFamily.{u_1} n ι l run)
                      (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) t))) →
            (mrz_sigmaMin_pos :
                ∀ (t : ι),
                  @LT.lt.{0} Real Real.instLT
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (@HighamBench.P19SingularValueData.sigmaMin n
                      (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run)
                      (@HighamBench.p19SquareRectMul n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) MR
                        (@HighamBench.P19IncreasingBasisFamily.basis.{u_1} n ι
                          (@HighamBench.P19ModularGMRESRun.basisFamily.{u_1} n ι l run)
                          (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) t))
                      (mrzSpectrum t))) →
              @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv
```

### D062: `HighamBench.P19RightPreconditionedQuantities.mrzSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fa4d18c7380daa3f66d2f771770298f12d6c9d2b454bd697a6fdf28177e01cfe`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : HighamBench.P19ModularGMRESRun l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          HighamBench.P19RightPreconditionedQuantities run MR MRinv →
            (t : ι) →
              HighamBench.P19SingularValueData
                (HighamBench.p19SquareRectMul MR (run.basisFamily.basis run.keyDimension t))
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l} →
        {MR MRinv : HighamBench.P19Matrix n} →
          (self : @HighamBench.P19RightPreconditionedQuantities.{u_1} n ι l run MR MRinv) →
            (t : ι) →
              @HighamBench.P19SingularValueData n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run)
                (@HighamBench.p19SquareRectMul n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) MR
                  (@HighamBench.P19IncreasingBasisFamily.basis.{u_1} n ι
                    (@HighamBench.P19ModularGMRESRun.basisFamily.{u_1} n ι l run)
                    (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run) t))
```

Definition body (one-level semantic boundary):

```lean
fun n ι l run MR MRinv self => self.1
```

### D063: `HighamBench.P19SingularValueData.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
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

### D064: `HighamBench.p19ExactC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d53169450812b017abdf4df9c66e1a9b6df67cc41fa03b150e209b66934af9ab`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (run : HighamBench.P19ModularGMRESRun l) → ι → HighamBench.P19RectMatrix n run.keyDimension
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : @HighamBench.P19ModularGMRESRun.{u_1} n ι l) →
        (t : ι) → HighamBench.P19RectMatrix n (@HighamBench.P19ModularGMRESRun.keyDimension.{u_1} n ι l run)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  HighamBench.p19SquareRectMul run.MLinv (HighamBench.p19SquareRectMul run.A (run.basisFamily.basis run.keyDimension t))
```

### D065: `HighamBench.p19VecNorm2Sq`

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

### D066: `HighamBench.P19IncreasingBasisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `7964a4dd38133453ceffb7b7c9c982dc1c8ac2e6beb707f90bc36f96a00f0897`

Type:

```lean
Nat → Type u_1 → Type u_1
```

Fully explicit type:

```lean
(n : Nat) → (ι : Type u_1) → Type u_1
```

### D067: `HighamBench.p19Augment`

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

### D068: `HighamBench.p19Column`

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

### D069: `HighamBench.p19IsLeastSquaresSolution`

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

### D070: `HighamBench.p19IsUpperHessenberg`

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

### D071: `HighamBench.p19MuchLessThanOneAt`

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

### D072: `HighamBench.p19RectConditionF2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D073: `HighamBench.p19RectMatMul`

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

### D074: `HighamBench.p19RectMatVec`

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

### D075: `HighamBench.p19ScaledFirstBasisVector`

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

### D076: `HighamBench.P19IncreasingBasisFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `26222588e9ab394aa206f7d4ca98e516b1b333815c6d509644d3f2240ed3816f`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (basis : (k : Nat) → ι → HighamBench.P19RectMatrix n k) →
      (∀ (k : Nat), instLENat.le k n → ∀ (t : ι), HighamBench.p19FullColumnRank (basis k t)) →
        (∀ (k : Nat) (t : ι) (i : Fin n) (j : Fin k),
            instLTNat.lt k n → Eq (basis k t i j) (basis (instHAdd.hAdd k 1) t i j.castSucc)) →
          HighamBench.P19IncreasingBasisFamily n ι
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (basis : (k : Nat) → ι → HighamBench.P19RectMatrix n k) →
      (full_rank :
          ∀ (k : Nat), @LE.le.{0} Nat instLENat k n → ∀ (t : ι), @HighamBench.p19FullColumnRank n k (basis k t)) →
        (column_prefix :
            ∀ (k : Nat) (t : ι) (i : Fin n) (j : Fin k),
              @LT.lt.{0} Nat instLTNat k n →
                @Eq.{1} Real (basis k t i j)
                  (basis
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    t i (@Fin.castSucc k j))) →
          HighamBench.P19IncreasingBasisFamily.{u_1} n ι
```

### D077: `HighamBench.p19FullColumnRank`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
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

Fully explicit type:

```lean
(a b : Prop) → Prop
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

Fully explicit type:

```lean
{G : Type u} → [self : DivInvMonoid.{u} G] → Div.{u} G
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

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D081: `Exists`

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

### D082: `Filter`

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

### D083: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D084: `Filter.NeBot`

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

### D085: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D086: `HMul.hMul`

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

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
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

Fully explicit type:

```lean
{α : Type u} → [self : LT.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D089: `Nat`

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

### D090: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

Fully explicit type:

```lean
∀ (n : Nat) [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n],
  Nat.AtLeastTwo
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D091: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ {n : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D092: `OfNat.ofNat`

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

### D093: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D094: `Real`

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

### D096: `Real.instLE`

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

Fully explicit type:

```lean
Mul.{0} Real
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

Fully explicit type:

```lean
NatCast.{0} Real
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

Fully explicit type:

```lean
One.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D100: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D104: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D105: `instOfNatNat`

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

### D106: `Fin`

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

### D107: `Fin.fintype`

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

### D108: `Fin.val`

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

### D109: `Finset.sum`

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

### D110: `Finset.univ`

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

### D111: `HAdd.hAdd`

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

### D112: `HPow.hPow`

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

### D113: `HSub.hSub`

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

### D114: `Matrix`

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

### D115: `Monoid.toNatPow`

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

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D117: `Pi.instSub`

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

### D118: `Real.instAdd`

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

### D121: `Real.instMonoid`

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

### D122: `Real.instSub`

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

### D123: `Real.lattice`

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

### D125: `instAddNat`

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

### D126: `instHAdd`

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

### D127: `instHPow`

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

### D128: `instHSub`

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

### D130: `Matrix.frobeniusNormedAddCommGroup`

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

### D131: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D132: `Max.max`

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

### D133: `Norm.norm`

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

### D134: `NormedAddCommGroup.toNorm`

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

### D135: `Pi.instAdd`

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

### D136: `Pi.instZero`

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

### D137: `Real.instMax`

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

### D138: `Real.instZero`

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

### D139: `Real.norm`

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

### D140: `Real.normedAddCommGroup`

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

### D143: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D145: `Matrix.add`

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

### D146: `Ne`

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

### D147: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D148: `Real.instLT`

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

### D149: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D150: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D151: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D152: `Fin.cases`

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

### D153: `instDecidableEqNat`

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

### D154: `ite`

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

### D155: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `7`
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
