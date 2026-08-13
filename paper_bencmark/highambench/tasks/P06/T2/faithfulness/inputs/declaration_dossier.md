# Declaration dossier for P06-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p06_t2_self_adjoint_dilation_norm_bridge
    {m n : ℕ} (M : Fin m → Fin n → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    p06RectOpNorm2Le M L ↔
      p06FiniteLoewnerLe (p06SelfAdjointDilation M)
        (fun a b : Fin m ⊕ Fin n ↦ L * p06FiniteId a b)
```

## Elaborated target type

```lean
∀ {m n : Nat} (M : Fin m → Fin n → Real) (L : Real),
  Real.instLE.le 0 L →
    Iff (HighamBench.p06RectOpNorm2Le M L)
      (HighamBench.p06FiniteLoewnerLe (HighamBench.p06SelfAdjointDilation M) fun a b =>
        instHMul.hMul L (HighamBench.p06FiniteId a b))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (M : Fin m → Fin n → Real) (L : Real)
  (hL : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) L),
  Iff (@HighamBench.p06RectOpNorm2Le m n M L)
    (@HighamBench.p06FiniteLoewnerLe.{0} (Sum.{0, 0} (Fin m) (Fin n))
      (@instFintypeSum.{0, 0} (Fin m) (Fin n) (Fin.fintype m) (Fin.fintype n))
      (@HighamBench.p06SelfAdjointDilation m n M) fun (a b : Sum.{0, 0} (Fin m) (Fin n)) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) L
        (@HighamBench.p06FiniteId.{0} (Sum.{0, 0} (Fin m) (Fin n))
          (fun (a b : Sum.{0, 0} (Fin m) (Fin n)) =>
            @instDecidableEqSum.{0, 0} (Fin m) (Fin n) (instDecidableEqFin m) (instDecidableEqFin n) a b)
          a b))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P06Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P06Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p06FiniteId`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a9037c406664bfc13b1a434dbaf41ca104afd808a9ca85949e0dd52361ad6016`

Type:

```lean
{ι : Type u_1} → [DecidableEq ι] → ι → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → [DecidableEq.{u_1 + 1} ι] → ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [DecidableEq ι] i j => ite (Eq i j) 1 0
```

### D002: `HighamBench.p06FiniteLoewnerLe`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `29fd5e4651ff034b2867e2a0fe108ffa9a89079e677bf93faf1d5cc013262247`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → [Fintype.{u_1} ι] → (A B : ι → ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A B =>
  ∀ (x : ι → Real), Real.instLE.le (HighamBench.p06FiniteQuadraticForm A x) (HighamBench.p06FiniteQuadraticForm B x)
```

### D003: `HighamBench.p06RectOpNorm2Le`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2f0f3a599fcba43fced25539e0ee05f966cef66bd1dec61d355e81e51e2bc1f9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (L : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A L =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (HighamBench.p06VecNorm2 (HighamBench.p06MatVec A x)) (instHMul.hMul L (HighamBench.p06VecNorm2 x))
```

### D004: `HighamBench.p06SelfAdjointDilation`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `53cc5f88a60adb56cc8442c818fa36d8fc6c9a59e3f9b6dd70ba3ca237853a83`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n) → Real
```

Fully explicit type:

```lean
{m n : Nat} → (M : Fin m → Fin n → Real) → Sum.{0, 0} (Fin m) (Fin n) → Sum.{0, 0} (Fin m) (Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} M a b =>
  HighamBench.p06SelfAdjointDilation.match_1 (fun a b => Real) a b (fun i j => M i j) (fun j i => M i j) fun x x_1 => 0
```

### D005: `HighamBench.p06FiniteQuadraticForm`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b2a3caa2b131aec4750b821fb5fdc5ebe3b4978680b79a022718f9a3ff57923b`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → Real) → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → [Fintype.{u_1} ι] → (A : ι → ι → Real) → (x : ι → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A x => Finset.univ.sum fun i => instHMul.hMul (x i) (HighamBench.p06FiniteMatVec A x i)
```

### D006: `HighamBench.p06MatVec`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `893dee110847631319ce412fdc634324446f2cfd73af2c3a356c467875edecc9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (x : Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D007: `HighamBench.p06SelfAdjointDilation.match_1`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2e93fce8941b11aab9fae216b0f8967e24e11858f44e61127d4d4d4b625dec34`

Type:

```lean
{m n : Nat} →
  (motive : Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n) → Sort u_1) →
    (a b : Sum (Fin m) (Fin n)) →
      ((i : Fin m) → (j : Fin n) → motive (Sum.inl i) (Sum.inr j)) →
        ((j : Fin n) → (i : Fin m) → motive (Sum.inr j) (Sum.inl i)) →
          ((x x_1 : Sum (Fin m) (Fin n)) → motive x x_1) → motive a b
```

Fully explicit type:

```lean
{m n : Nat} →
  (motive : Sum.{0, 0} (Fin m) (Fin n) → Sum.{0, 0} (Fin m) (Fin n) → Sort u_1) →
    (a b : Sum.{0, 0} (Fin m) (Fin n)) →
      (h_1 :
          (i : Fin m) → (j : Fin n) → motive (@Sum.inl.{0, 0} (Fin m) (Fin n) i) (@Sum.inr.{0, 0} (Fin m) (Fin n) j)) →
        (h_2 :
            (j : Fin n) →
              (i : Fin m) → motive (@Sum.inr.{0, 0} (Fin m) (Fin n) j) (@Sum.inl.{0, 0} (Fin m) (Fin n) i)) →
          (h_3 : (x x_1 : Sum.{0, 0} (Fin m) (Fin n)) → motive x x_1) → motive a b
```

Definition body (one-level semantic boundary):

```lean
fun {m n} motive a b h_1 h_2 h_3 =>
  Sum.casesOn a
    (fun val =>
      HighamBench.p06SelfAdjointDilation._sparseCasesOn_1 b (fun val_1 => h_1 val val_1) fun h => h_3 (Sum.inl val) b)
    fun val =>
    HighamBench.p06SelfAdjointDilation._sparseCasesOn_2 b (fun val_1 => h_2 val val_1) fun h => h_3 (Sum.inr val) b
```

### D008: `HighamBench.p06VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D009: `HighamBench.p06FiniteMatVec`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b24fc73f1af2f6391e5db4a099c98a3db898d965bdf2719166452e6ff5e904a8`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → Real) → ι → Real
```

Fully explicit type:

```lean
{ι : Type u_1} → [Fintype.{u_1} ι] → (A : ι → ι → Real) → (x : ι → Real) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D010: `HighamBench.p06SelfAdjointDilation._sparseCasesOn_1`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3c429f9ecaacc60087da2dc77ae1606f32a23d9f1f6b9ee7253a96bb2452101d`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : β) → motive (Sum.inr val)) → (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : (t : Sum.{u, v} α β) → Sort u_1} →
      (t : Sum.{u, v} α β) →
        (inr : (val : β) → motive (@Sum.inr.{u, v} α β val)) →
          ((h : Nat.hasNotBit (nat_lit 2) (@Sum.ctorIdx.{u, v} α β t)) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inr =>
  Sum.rec (motive := fun t => (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t) (fun val «else» => «else» ⋯)
    (fun val «else» => inr val) t
```

### D011: `HighamBench.p06SelfAdjointDilation._sparseCasesOn_2`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cadeae4b49c6aacf73024f8587ace0c7734c9e74602f2cb19cf7879cd1dca94c`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : α) → motive (Sum.inl val)) → (Nat.hasNotBit 1 t.ctorIdx → motive t) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : (t : Sum.{u, v} α β) → Sort u_1} →
      (t : Sum.{u, v} α β) →
        (inl : (val : α) → motive (@Sum.inl.{u, v} α β val)) →
          ((h : Nat.hasNotBit (nat_lit 1) (@Sum.ctorIdx.{u, v} α β t)) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inl =>
  Sum.rec (motive := fun t => (Nat.hasNotBit 1 t.ctorIdx → motive t) → motive t) (fun val «else» => inl val)
    (fun val «else» => «else» ⋯) t
```

### D012: `Fin`

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

### D013: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D014: `HMul.hMul`

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

### D015: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D016: `LE.le`

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

### D017: `Nat`

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

### D018: `OfNat.ofNat`

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

### D019: `Real`

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

### D020: `Real.instLE`

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

### D021: `Real.instMul`

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

### D022: `Real.instZero`

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

### D023: `Sum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b918d4b75e8964578622cc8220c8e47d62bd100bdf794f538778ce95c76f70c6`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D024: `Zero.toOfNat0`

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

### D025: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D026: `instDecidableEqSum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e82c0dc84549c649cd05cd11dc0a7647cdf8009b36bcf62a4387ebc229f9d316`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [DecidableEq α] → [DecidableEq β] → DecidableEq (Sum α β)
```

Fully explicit type:

```lean
{α : Type u_1} →
  {β : Type u_2} →
    [DecidableEq.{u_1 + 1} α] → [DecidableEq.{u_2 + 1} β] → DecidableEq.{max (u_2 + 1) (u_1 + 1)} (Sum.{u_1, u_2} α β)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] [DecidableEq β] => instDecidableEqSum.decEq
```

### D027: `instFintypeSum`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Sum`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `26993d4e890c6ac0fc8a0a76b602ea044068841a7430282875d3fa3c6e1638b5`

Type:

```lean
(α : Type u) → (β : Type v) → [Fintype α] → [Fintype β] → Fintype (Sum α β)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → [Fintype.{u} α] → [Fintype.{v} β] → Fintype.{max v u} (Sum.{u, v} α β)
```

Definition body (one-level semantic boundary):

```lean
fun α β [Fintype α] [Fintype β] => { elems := Finset.univ.disjSum Finset.univ, complete := ⋯ }
```

### D028: `instHMul`

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

### D029: `DecidableEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ceb5edcca38a0d8e0cbe42efd319eed4e877a75211690cacfd89ee5799fb1004`

Type:

```lean
Sort u → Sort (max 1 u)
```

Fully explicit type:

```lean
(α : Sort u) → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun α => (a b : α) → Decidable (Eq a b)
```

### D030: `Eq`

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

### D031: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D032: `One.toOfNat1`

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

### D033: `Real.instOne`

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

### D034: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D035: `Finset.sum`

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

### D036: `Finset.univ`

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

### D037: `HPow.hPow`

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

### D038: `Monoid.toNatPow`

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

### D039: `Nat.hasNotBit`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7699bcfbcaba03b7e3c810ec7a92e896502b1469cf1fc5b0a64fe91880a756fd`

Type:

```lean
Nat → Nat → Prop
```

Fully explicit type:

```lean
(m n : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun m n => Ne (Nat.land 1 (m.shiftRight n)) 1
```

### D040: `Real.instAddCommMonoid`

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

### D041: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D042: `Real.sqrt`

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

### D043: `Sum.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7674fe9612b87e143d023c1d08d4603d6cf1f13a165277c77c0c3c17ab768682`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : α) → motive (Sum.inl val)) → ((val : β) → motive (Sum.inr val)) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : (t : Sum.{u, v} α β) → Sort u_1} →
      (t : Sum.{u, v} α β) →
        (inl : (val : α) → motive (@Sum.inl.{u, v} α β val)) →
          (inr : (val : β) → motive (@Sum.inr.{u, v} α β val)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inl inr => Sum.rec (fun val => inl val) (fun val => inr val) t
```

### D044: `Sum.ctorIdx`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f2e8ea052f4671bb35c4cb334f4c653780658af219b1b860c094b6edf670d102`

Type:

```lean
{α : Type u} → {β : Type v} → Sum α β → Nat
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → Sum.{u, v} α β → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} x => Sum.casesOn x (fun val => 0) fun val => 1
```

### D045: `Sum.inl`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1a4aaa4b5e1935c80236f326430592c895be07047c023475286fc160cbbfdb60`

Type:

```lean
{α : Type u} → {β : Type v} → α → Sum α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (val : α) → Sum.{u, v} α β
```

### D046: `Sum.inr`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `5fe7cba3f12df2d7f7efb2b320c8dd9ff78fdbfb0267e92f2e571c99d2f1e6f1`

Type:

```lean
{α : Type u} → {β : Type v} → β → Sum α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (val : β) → Sum.{u, v} α β
```

### D047: `instHPow`

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

### D048: `instOfNatNat`

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

### D049: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D050: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D051: `Eq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `62d4020b7012db70e44624c7d64dd267524e7e75e4b869680e0c95d2231c85d1`

Type:

```lean
∀ {α : Sort u_1} (a : α), Eq a a
```

Fully explicit type:

```lean
∀ {α : Sort u_1} (a : α), @Eq.{u_1} α a a
```

### D052: `Nat.land`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ba03bca5cd1935764fe2e7cb6539b6c860f3eb526cb9c7b1f6e16d6eabb9ff7d`

Type:

```lean
Nat → Nat → Nat
```

Fully explicit type:

```lean
Nat → Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.bitwise Bool.and
```

### D053: `Nat.ne_of_beq_eq_false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `5d02d2e9f1cc8cdfa62b0caf31b9843167d35f0b8445d653452912a5f56fd1ee`

Type:

```lean
∀ {n m : Nat}, Eq (n.beq m) Bool.false → Not (Eq n m)
```

Fully explicit type:

```lean
∀ {n m : Nat}, @Eq.{1} Bool (Nat.beq n m) Bool.false → Not (@Eq.{1} Nat n m)
```

### D054: `Nat.shiftRight`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `83adfdc344d13b726e9b2aa74662fceecc7cda9ef92d8b83bff3d2058a7ee7a6`

Type:

```lean
Nat → Nat → Nat
```

Fully explicit type:

```lean
Nat → Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  Nat.brecOn (motive := fun x => Nat → Nat) x_1
    (fun x f x_2 =>
      Nat.shiftLeft.match_1 (fun x x_3 => Nat.below (motive := fun x => Nat → Nat) x_3 → Nat) x_2 x (fun n x => n)
        (fun n m x => instHDiv.hDiv (x.1 n) 2) f)
    x
```

### D055: `Sum.rec`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `3ccfe56c135565c27c454b52bb1960295625b2148cd6d2a03f85045c566e3488`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      ((val : α) → motive (Sum.inl val)) → ((val : β) → motive (Sum.inr val)) → (t : Sum α β) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : (t : Sum.{u, v} α β) → Sort u_1} →
      (inl : (val : α) → motive (@Sum.inl.{u, v} α β val)) →
        (inr : (val : β) → motive (@Sum.inr.{u, v} α β val)) → (t : Sum.{u, v} α β) → motive t
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
SHA-256: `80ab87e3785b274488c63c1e88e3895907493e271a0e0963907f8d8538bd6ae5`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P06. -/
noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular Frobenius norm in P06's finite matrix notation. -/
noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The homogeneous rectangular operator-2 upper-bound predicate. -/
def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

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

/-- Identity matrix on an arbitrary finite decidable index type. -/
noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

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

/-- The exact state obtained after the first `r` unperturbed transformations.
The recurrence represents `P_(r-1) ⋯ P_0 b`. -/
noncomputable def p06ExactState {m : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 => p06MatVec (P r) (p06ExactState P b r)

/-- The coefficient of the terms containing exactly one local perturbation.
This is the recursive form of the insertion sum in P06 equations (4.8)--(4.9). -/
noncomputable def p06FirstOrderState {m : ℕ}
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06FirstOrderState P E b r) i +
        p06MatVec (E r) (p06ExactState P b r) i

/-- The sum of all terms containing at least two local perturbations, after
factoring out `t²` from transformations `P_r + t E_r`. -/
noncomputable def p06HigherOrderState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06HigherOrderState t P E b r) i +
        p06MatVec (E r) (p06FirstOrderState P E b r) i +
        t * p06MatVec (E r) (p06HigherOrderState t P E b r) i

/-- State obtained from the fully perturbed sequence `P_r + t E_r`. -/
noncomputable def p06PerturbedState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 =>
      p06MatVec (fun i j ↦ P r i j + t * E r i j)
        (p06PerturbedState t P E b r)

end HighamBench
```
