# Declaration dossier for P06-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p06_t1_columnwise_to_frobenius
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (DeltaA : ℝ → Fin m → Fin n → ℝ)
    (columnRemainder : Fin n → ℝ → ℝ)
    (c6 : ℕ) (lambda : ℝ) (_hc6 : 0 < c6) (hlambda : 0 < lambda)
    (hsecondOrder : ∀ j,
      p06SecondOrderAtZeroRight (columnRemainder j))
    (hcolumn :
      ∀ᶠ u in nhdsWithin 0 (Set.Ioo (0 : ℝ) 1),
        ∀ j : Fin n,
          p06VecNorm2 (fun i ↦ DeltaA u i j) ≤
            p06QRLeadingCoefficient c6 lambda m n u *
                p06VecNorm2 (fun i ↦ A i j) +
              |columnRemainder j u|) :
    ∃ normwiseRemainder : ℝ → ℝ,
      p06SecondOrderAtZeroRight normwiseRemainder ∧
        ∀ᶠ u in nhdsWithin 0 (Set.Ioo (0 : ℝ) 1),
          p06FrobNorm (DeltaA u) ≤
            p06QRLeadingCoefficient c6 lambda m n u * p06FrobNorm A +
              |normwiseRemainder u|
```

## Elaborated target type

```lean
∀ {m n : Nat} (A : Fin m → Fin n → Real) (DeltaA : Real → Fin m → Fin n → Real) (columnRemainder : Fin n → Real → Real)
  (c6 : Nat) (lambda : Real),
  instLTNat.lt 0 c6 →
    Real.instLT.lt 0 lambda →
      (∀ (j : Fin n), HighamBench.p06SecondOrderAtZeroRight (columnRemainder j)) →
        Filter.Eventually
            (fun u =>
              ∀ (j : Fin n),
                Real.instLE.le (HighamBench.p06VecNorm2 fun i => DeltaA u i j)
                  (instHAdd.hAdd
                    (instHMul.hMul (HighamBench.p06QRLeadingCoefficient c6 lambda m n u)
                      (HighamBench.p06VecNorm2 fun i => A i j))
                    (abs (columnRemainder j u))))
            (nhdsWithin 0 (Set.Ioo 0 1)) →
          Exists fun normwiseRemainder =>
            And (HighamBench.p06SecondOrderAtZeroRight normwiseRemainder)
              (Filter.Eventually
                (fun u =>
                  Real.instLE.le (HighamBench.p06FrobNorm (DeltaA u))
                    (instHAdd.hAdd
                      (instHMul.hMul (HighamBench.p06QRLeadingCoefficient c6 lambda m n u) (HighamBench.p06FrobNorm A))
                      (abs (normwiseRemainder u))))
                (nhdsWithin 0 (Set.Ioo 0 1)))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (A : Fin m → Fin n → Real) (DeltaA : Real → Fin m → Fin n → Real) (columnRemainder : Fin n → Real → Real)
  (c6 : Nat) (lambda : Real)
  (_hc6 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) c6)
  (hlambda :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lambda)
  (hsecondOrder : ∀ (j : Fin n), HighamBench.p06SecondOrderAtZeroRight (columnRemainder j))
  (hcolumn :
    @Filter.Eventually.{0} Real
      (fun (u : Real) =>
        ∀ (j : Fin n),
          @LE.le.{0} Real Real.instLE (@HighamBench.p06VecNorm2 m fun (i : Fin m) => DeltaA u i j)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.p06QRLeadingCoefficient c6 lambda m n u)
                (@HighamBench.p06VecNorm2 m fun (i : Fin m) => A i j))
              (@abs.{0} Real Real.lattice Real.instAddGroup (columnRemainder j u))))
      (@nhdsWithin.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))),
  @Exists.{1} (Real → Real) fun (normwiseRemainder : Real → Real) =>
    And (HighamBench.p06SecondOrderAtZeroRight normwiseRemainder)
      (@Filter.Eventually.{0} Real
        (fun (u : Real) =>
          @LE.le.{0} Real Real.instLE (@HighamBench.p06FrobNorm m n (DeltaA u))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.p06QRLeadingCoefficient c6 lambda m n u) (@HighamBench.p06FrobNorm m n A))
              (@abs.{0} Real Real.lattice Real.instAddGroup (normwiseRemainder u))))
        (@nhdsWithin.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@Set.Ioo.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P06Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P06Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Measure.Real`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p06FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `08a7a98ec9aaf56bb917d8e75f7592c843a1eb612b9bbe59de6b7e8bccf2bf1b`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D002: `HighamBench.p06QRLeadingCoefficient`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ca209c3ff3588c6030974ec05bd7b361e2d9d68c597d2f8d8245e2a5ce597826`

Type:

```lean
Nat → Real → Nat → Nat → Real → Real
```

Fully explicit type:

```lean
(c6 : Nat) → (lambda : Real) → (m n : Nat) → (u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun c6 lambda m n u =>
  instHMul.hMul (instHMul.hMul (instHMul.hMul c6.cast lambda) n.cast.sqrt) (HighamBench.p06GammaTilde m lambda u)
```

### D003: `HighamBench.p06SecondOrderAtZeroRight`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `186c197af0a6615229b1561d41b9e3a7f3cd1ef9a858131f727b900518e93ff1`

Type:

```lean
(Real → Real) → Prop
```

Fully explicit type:

```lean
(remainder : Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder => Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioo 0 1)) remainder fun u => instHPow.hPow u 2
```

### D004: `HighamBench.p06VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `641a08c9509bcfec9f54c8dcf330d38cf5a97f59688d88c388269019be35f39d`

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
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D005: `HighamBench.p06GammaTilde`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `eb3c5cdb87252caeb2361d4b462375f2c9798d3c399f9a0be7d368fbcdb85286`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(k : Nat) → (lambda u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun k lambda u =>
  instHSub.hSub
    (Real.exp
      (instHDiv.hDiv
        (instHAdd.hAdd (instHMul.hMul (instHMul.hMul lambda k.cast.sqrt) u) (instHMul.hMul k.cast (instHPow.hPow u 2)))
        (instHSub.hSub 1 u)))
    1
```

### D006: `And`

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

### D007: `Exists`

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

### D008: `Filter.Eventually`

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

### D009: `Fin`

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

### D010: `HAdd.hAdd`

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

### D011: `HMul.hMul`

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

### D012: `LE.le`

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

### D013: `LT.lt`

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

### D014: `Nat`

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

### D015: `OfNat.ofNat`

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

### D016: `One.toOfNat1`

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

### D017: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D018: `Real`

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

### D019: `Real.instAdd`

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

### D020: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D021: `Real.instLE`

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

### D022: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D023: `Real.instMul`

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

### D024: `Real.instOne`

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

### D025: `Real.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `896bb94fc15867c0df82ea0f639eb6116e90a24819a66a54db9442e47cba7274`

Type:

```lean
Preorder Real
```

Fully explicit type:

```lean
Preorder.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D026: `Real.instZero`

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

### D027: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D028: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D029: `Set.Ioo`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Interval.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1d5dd7f79ccc67083f800bd888bed811c7863a5a94357817d52020d0d704414d`

Type:

```lean
{α : Type u_1} → [Preorder α] → α → α → Set α
```

Fully explicit type:

```lean
{α : Type u_1} → [Preorder.{u_1} α] → (a b : α) → Set.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Preorder α] a b => setOf fun x => And (inst.lt a x) (inst.lt x b)
```

### D030: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D031: `Zero.toOfNat0`

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

### D032: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D033: `instHAdd`

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

### D034: `instHMul`

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

### D035: `instLTNat`

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

### D036: `instOfNatNat`

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

### D037: `nhdsWithin`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ae7b5c1971244e63e32407fed747da989ad9fef3a4d9c3a64643427eaf071f05`

Type:

```lean
{X : Type u_1} → [TopologicalSpace X] → X → Set X → Filter X
```

Fully explicit type:

```lean
{X : Type u_1} → [TopologicalSpace.{u_1} X] → (x : X) → (s : Set.{u_1} X) → Filter.{u_1} X
```

Definition body (one-level semantic boundary):

```lean
fun {X} [TopologicalSpace X] x s => Filter.instInf.min (nhds x) (Filter.principal s)
```

### D038: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D039: `Fin.fintype`

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

### D040: `Finset.sum`

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

### D041: `Finset.univ`

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

### D042: `HPow.hPow`

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

### D043: `Monoid.toNatPow`

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

### D044: `Nat.cast`

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

### D045: `Real.instAddCommMonoid`

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

### D046: `Real.instMonoid`

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

### D047: `Real.instNatCast`

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

### D048: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D049: `Real.sqrt`

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

### D050: `instHPow`

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

### D051: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D052: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D053: `HSub.hSub`

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

### D054: `Real.exp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Exponential`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `69806b1af98b09fabed435ccc47a9f2f0840f9c5c140fb62cccc81a80761a984`

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
fun x => (Complex.exp (Complex.ofReal x)).re
```

### D055: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D056: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D057: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D058: `instHSub`

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

### `HighamBench.P06Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P06Definitions.lean`
SHA-256: `e9a3986f76f3bc6364fce9d245e0606e87aea9970763506b926eeaa2ec55697a`

```lean
import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P06. -/
noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular Frobenius norm in P06's finite matrix notation. -/
noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Identity matrix on an arbitrary finite decidable index type. -/
noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Matrix multiplication for an `m`-by-`m` matrix acting on an
`m`-by-`n` matrix. -/
noncomputable def p06RectMatMul {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin m, Q i k * R k j

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The homogeneous rectangular operator-2 upper-bound predicate. -/
def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

/-- The Householder matrix `I - vvᵀ` in the normalization `vᵀv = 2`
used in section 4 of P06. -/
noncomputable def p06HouseholderMatrix {m : ℕ}
    (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ p06FiniteId i j - v i * v j

/-- Exact orthogonality, written as `QᵀQ = I`. -/
def p06Orthogonal {m : ℕ} (Q : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, (∑ k : Fin m, Q k i * Q k j) = p06FiniteId i j

/-- An `m`-by-`n` matrix is upper trapezoidal when all entries strictly
below its main diagonal are zero. -/
def p06UpperTrapezoidal {m n : ℕ}
    (R : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

/-- The probabilistic accumulated-error constant in P06 equation (1.6). -/
noncomputable def p06GammaTilde (k : ℕ) (lambda u : ℝ) : ℝ :=
  Real.exp
      ((lambda * Real.sqrt (k : ℝ) * u + (k : ℝ) * u ^ 2) /
        (1 - u)) -
    1

/-- The leading coefficient in Theorem 4.4 and equation (4.20). -/
noncomputable def p06QRLeadingCoefficient
    (c6 : ℕ) (lambda : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  (c6 : ℝ) * lambda * Real.sqrt (n : ℝ) *
    p06GammaTilde m lambda u

/-- The probability lower bound `p₄(lambda,m,n)` attached to the simultaneous
columnwise event in Theorem 4.4. It is intentionally allowed to be negative
for small `lambda`, exactly as in the paper. -/
noncomputable def p06P4 (lambda : ℝ) (m n : ℕ) : ℝ :=
  1 - 2 * (m : ℝ) * (n : ℝ) * Real.exp (-lambda ^ 2)

/-- A scalar remainder of order `u²` as unit roundoff tends to zero. The
definition deliberately does not choose an input-norm scale or uniformity in
the dimensions, neither of which is specified by equation (4.20). -/
def p06SecondOrderAtZero (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhds 0] fun u : ℝ ↦ u ^ 2

/-- The one-sided `O(u²)` interpretation used when unit roundoff ranges over
strictly positive values below one. -/
def p06SecondOrderAtZeroRight (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] fun u : ℝ ↦ u ^ 2

/-- A second-order remainder whose asymptotic witness also controls every
unit roundoff between zero and the distinguished execution's unit roundoff.
This closes the gap between a limit statement at zero and evaluation at one
fixed positive value of `u`. -/
def P06SecondOrderControl (remainder : ℝ → ℝ) (u0 : ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧
    p06SecondOrderAtZero remainder ∧
    ∀ u, |u| ≤ |u0| → |remainder u| ≤ constant * u ^ 2

/-- Errors generated before operation `k`, in the computation order used by
Model 1.5. -/
def p06PriorErrors {Ω : Type*} {steps : ℕ}
    (error : Fin steps → Ω → ℝ) (k : Fin steps) (omega : Ω) :
    Fin k.val → ℝ :=
  fun i ↦ error ⟨i.val, lt_trans i.isLt k.isLt⟩ omega

/-- Finite-computation form of Definition 1.3. The displayed integral identity
is the test-function characterization of
`E(delta_k | delta_{k-1},...,delta_1) = E(delta_k)`. -/
def p06MeanIndependent {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) {steps : ℕ}
    (error : Fin steps → Ω → ℝ) : Prop :=
  ∀ (k : Fin steps) (g : (Fin k.val → ℝ) → ℝ),
    MeasureTheory.Integrable
        (fun omega ↦ g (p06PriorErrors error k omega)) mu →
      MeasureTheory.Integrable
        (fun omega ↦
          g (p06PriorErrors error k omega) * error k omega) mu →
      (∫ omega,
          g (p06PriorErrors error k omega) * error k omega ∂mu) =
        (∫ omega, g (p06PriorErrors error k omega) ∂mu) *
          ∫ omega, error k omega ∂mu

/-- P06 Model 1.5 for a finite computation. Every generated scalar operation
obeys the standard relative-error equation (1.4); errors are ordered,
measurable, mean independent, and have mean zero. The probability measure is
not restricted to a finite sample space. -/
structure P06Model15 (Ω : Type*) [MeasurableSpace Ω] where
  probability : MeasureTheory.Measure Ω
  probability_univ : probability Set.univ = 1
  operationCount : ℕ
  exactValue : Fin operationCount → Ω → ℝ
  computedValue : Fin operationCount → Ω → ℝ
  error : Fin operationCount → Ω → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_lt_one : unitRoundoff < 1
  relative_error : ∀ k omega,
    computedValue k omega = exactValue k omega * (1 + error k omega)
  error_bound : ∀ k omega, |error k omega| ≤ unitRoundoff
  error_measurable : ∀ k, Measurable (error k)
  error_integrable : ∀ k,
    MeasureTheory.Integrable (error k) probability
  error_mean_zero : ∀ k, ∫ omega, error k omega ∂probability = 0
  error_mean_independent : p06MeanIndependent probability error

/-- The entries below the active diagonal position that the source algorithm
sets to exact zero after applying one perturbed Householder transformation. -/
noncomputable def p06HouseholderQRStep {m n : ℕ}
    (j : Fin n) (P : Fin m → Fin m → ℝ)
    (B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i k ↦ if k = j ∧ j.val < i.val then 0 else p06RectMatMul P B i k

/-- A padded Householder vector is constructed for an active column when it
has no support above the pivot and its exact reflector annihilates that
column below the pivot. Normalization is recorded separately by the run. -/
def p06HouseholderForActiveColumn {m n : ℕ}
    (j : Fin n) (x v : Fin m → ℝ) : Prop :=
  (∀ i, i.val < j.val → v i = 0) ∧
    ∀ i, j.val < i.val →
      p06MatVec (p06HouseholderMatrix v) x i = 0

/-- A Householder QR execution represented in the perturbed-transformation
form (4.1). The reflector is a deterministic construction from the current
active column, the intended subdiagonal entries are explicitly set to zero,
and every final entry is linked to the Model 1.5 scalar trace. -/
structure P06HouseholderQRRun
    (Ω : Type*) [MeasurableSpace Ω] (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (model : P06Model15 Ω) where
  rows_ge_columns : n ≤ m
  columns_pos : 0 < n
  reflectorBuilder : Fin n → (Fin m → ℝ) → Fin m → ℝ
  householderVector : Fin n → Ω → Fin m → ℝ
  localPerturbation : Fin n → Ω → Fin m → Fin m → ℝ
  state : Fin (n + 1) → Ω → Fin m → Fin n → ℝ
  RHat : Ω → Fin m → Fin n → ℝ
  exactQTransposeState : Fin (n + 1) → Ω → Fin m → Fin m → ℝ
  exactQ : Ω → Fin m → Fin m → ℝ
  outputIndex : Fin m → Fin n → Fin model.operationCount
  householder_from_active_column : ∀ j omega,
    householderVector j omega =
      reflectorBuilder j (fun i ↦ state j.castSucc omega i j)
  householder_active_column : ∀ j omega,
    p06HouseholderForActiveColumn j
      (fun i ↦ state j.castSucc omega i j) (householderVector j omega)
  householder_normalized : ∀ j omega,
    ∑ i : Fin m, householderVector j omega i ^ 2 = 2
  initial_state : ∀ omega, state 0 omega = A
  rounded_step : ∀ j omega,
    state j.succ omega =
      p06HouseholderQRStep j
        (fun i k ↦
          p06HouseholderMatrix (householderVector j omega) i k +
            localPerturbation j omega i k)
        (state j.castSucc omega)
  exactQTranspose_initial : ∀ omega,
    exactQTransposeState 0 omega = p06FiniteId
  exactQTranspose_step : ∀ j omega,
    exactQTransposeState j.succ omega =
      p06RectMatMul (p06HouseholderMatrix (householderVector j omega))
        (exactQTransposeState j.castSucc omega)
  exactQ_from_steps : ∀ omega i k,
    exactQ omega i k = exactQTransposeState (Fin.last n) omega k i
  exactQ_orthogonal : ∀ omega, p06Orthogonal (exactQ omega)
  output_state : ∀ omega, RHat omega = state (Fin.last n) omega
  output_from_trace : ∀ omega i j,
    RHat omega i j = model.computedValue (outputIndex i j) omega
  output_upper_trapezoidal : ∀ omega, p06UpperTrapezoidal (RHat omega)

/-- The probability-one strengthening of the local application bound (4.2)
assumed in Lemma 4.2 and Theorem 4.4. -/
structure P06Lemma42Assumption
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {model : P06Model15 Ω}
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Ω
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j, p06RectOpNorm2Le (run.localPerturbation j omega)
        ((c5 : ℝ) * p06GammaTilde m lambda model.unitRoundoff)
  probability_one : model.probability localEvent = 1

/-- The one-column conclusion of Lemma 4.2, specialized to a column of the QR
execution. Theorem 4.4 still has to intersect these events, assemble one
matrix perturbation, prove the simultaneous probability, and aggregate the
column bounds. -/
structure P06Lemma42ColumnCertificate
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {model : P06Model15 Ω}
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 c6 : ℕ) (lambda : ℝ)
    (hlocal : P06Lemma42Assumption run c5 lambda) (column : Fin n) where
  goodEvent : Set Ω
  goodEvent_measurable : MeasurableSet goodEvent
  goodEvent_subset_local : goodEvent ⊆ hlocal.localEvent
  failure_probability_bound :
    model.probability.real goodEventᶜ ≤
      2 * (m : ℝ) * Real.exp (-lambda ^ 2)
  deltaColumn : Ω → Fin m → ℝ
  remainder : ℝ → Ω → ℝ
  remainder_control : ∀ omega,
    P06SecondOrderControl (fun u ↦ remainder u omega) model.unitRoundoff
  exact_column_relation : ∀ omega i,
    A i column + deltaColumn omega i =
      ∑ k : Fin m, run.exactQ omega i k * run.RHat omega k column
  column_bound_on_good : ∀ omega, omega ∈ goodEvent →
    p06VecNorm2 (deltaColumn omega) ≤
      p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
          p06VecNorm2 (fun i ↦ A i column) +
        |remainder model.unitRoundoff omega|

/-- Euclidean norm on an arbitrary finite index type, needed for a dilation. -/
noncomputable def p06FiniteVecNorm2 {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- Matrix-vector multiplication on an arbitrary finite index type. -/
noncomputable def p06FiniteMatVec {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ ∑ j, A i j * x j

/-- Quadratic form on an arbitrary finite real matrix. -/
noncomputable def p06FiniteQuadraticForm {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * p06FiniteMatVec A x i

/-- Quadratic-form (Loewner) order used to express the largest-eigenvalue
threshold in P06 equation (3.4) without introducing eigenvalue machinery. -/
def p06FiniteLoewnerLe {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) : Prop :=
  ∀ x, p06FiniteQuadraticForm A x ≤ p06FiniteQuadraticForm B x

/-- P06 equation (3.3): the symmetric dilation `[[0,M],[Mᵀ,0]]`. -/
noncomputable def p06SelfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → ℝ :=
  fun a b ↦
    match a, b with
    | Sum.inl i, Sum.inr j => M i j
    | Sum.inr j, Sum.inl i => M i j
    | _, _ => 0

/-- Entrywise asymptotic order for a finite square-matrix family. This is the
finite-dimensional interpretation of the matrix-valued `O` notation in (4.8),
without choosing a norm or a hidden constant that the paper does not specify. -/
def p06MatrixFamilyIsBigOAtZero {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ) : Prop :=
  ∀ i j, (fun u ↦ A u i j) =O[nhds 0] scale

/-- A finite square-matrix remainder of order `u²` at zero. -/
def p06MatrixSecondOrderAtZero {m : ℕ}
    (remainder : ℝ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  p06MatrixFamilyIsBigOAtZero remainder fun u ↦ u ^ 2

/-- Product `P_(k-1) ⋯ P_1 P_0`, with the empty product equal to the
identity matrix. -/
noncomputable def p06HouseholderProduct {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | k + 1 => P k * p06HouseholderProduct P k

/-- Product of the locally perturbed transformations through step `k`. -/
noncomputable def p06PerturbedHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 1
  | u, omega, k + 1 =>
      (P k + DeltaP u k omega) *
        p06PerturbedHouseholderProduct P DeltaP u omega k

/-- Sum of all product terms containing exactly one local `DeltaP_j`, in the
unfactored ordering of the first line of (4.8). -/
noncomputable def p06FirstOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega * p06HouseholderProduct P k

/-- Exact sum of all terms containing at least two local perturbations. Its
recurrence is obtained by multiplying the zero-, one-, and higher-order parts
by the next factor `P_k + DeltaP_k`. -/
noncomputable def p06HigherOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06HigherOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06HigherOrderHouseholderProduct P DeltaP u omega k

/-- Exact Householder matrices generated by a sequence of normalized vectors. -/
noncomputable def p06HouseholderSequenceMatrix {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  p06HouseholderMatrix (v j)

/-- A unit-roundoff-indexed execution family for the vector computation in
Lemmas 4.1--4.2. The distinguished execution at `model.unitRoundoff` is tied
to the Model 1.5 scalar trace; the family supplies the asymptotic meaning of
the `O(u²)` notation in (4.8). -/
structure P06HouseholderApplicationFamily
    (Omega : Type*) [MeasurableSpace Omega] (m r : ℕ)
    (model : P06Model15 Omega) where
  dimension_pos : 0 < m
  steps_pos : 0 < r
  b : Fin m → ℝ
  householderVector : ℕ → Fin m → ℝ
  localPerturbation :
    ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ
  computed : ℝ → Omega → Fin m → ℝ
  outputIndex : Fin m → Fin model.operationCount
  householder_normalized : ∀ j, j < r →
    ∑ i : Fin m, householderVector j i ^ 2 = 2
  householder_involutory : ∀ j, j < r →
    p06HouseholderSequenceMatrix householderVector j *
        p06HouseholderSequenceMatrix householderVector j = 1
  computed_product : ∀ u omega,
    computed u omega =
      p06MatVec
        (p06PerturbedHouseholderProduct
          (p06HouseholderSequenceMatrix householderVector)
          localPerturbation u omega r)
        b
  output_from_trace : ∀ omega i,
    computed model.unitRoundoff omega i =
      model.computedValue (outputIndex i) omega

/-- The probability-one form of the local application bound (4.2) used by
Lemma 4.2, together with its family-level `DeltaP_j = O(u)` meaning. -/
structure P06Lemma42VectorAssumption
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Omega
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j : Fin r,
        p06RectOpNorm2Le
          (run.localPerturbation model.unitRoundoff j.val omega)
          ((c5 : ℝ) * p06GammaTilde m lambda model.unitRoundoff)
  local_first_order : ∀ omega, omega ∈ localEvent →
    ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ run.localPerturbation u j omega) (fun u ↦ u)
  probability_one : model.probability localEvent = 1

/-- The exact transformed vector `b_(r+1) = P_r ⋯ P_1 b`. -/
noncomputable def p06ApplicationExactState
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) : Fin m → ℝ :=
  p06MatVec
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)
    run.b

/-- The zero-based form of (4.9) for an arbitrary prefix length. -/
noncomputable def p06TransformedHouseholderInsertion
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (p06HouseholderProduct P (j + 1)) *
    DeltaP u j omega * p06HouseholderProduct P j

/-- Sum of the transformed insertions with zero-based indices `0 <= j < k`. -/
noncomputable def p06TransformedHouseholderInsertionSum
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ j ∈ Finset.range k,
    p06TransformedHouseholderInsertion P DeltaP u omega j

/-- The paper's `Q = (P_r ⋯ P_1)^T`. -/
noncomputable def p06ApplicationQ
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)

/-- The unfactored sum in the first line of equation (4.8). -/
noncomputable def p06ApplicationFirstOrderMatrix
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06FirstOrderHouseholderProduct
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

/-- Equation (4.9), with zero-based `j`: the left product includes `P_j`,
while the right product ends at `P_(j-1)` and is empty when `j = 0`. -/
noncomputable def p06ApplicationF
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) (j : Fin r) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertion
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega j.val

/-- The sum `sum_(j=1)^r F_j` from the second line of (4.8). -/
noncomputable def p06ApplicationFSum
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertionSum
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

end HighamBench
```
