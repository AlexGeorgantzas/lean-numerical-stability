# Declaration dossier for P07-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p07_t2_backward_error_product_budget
    {m n : ℕ} (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ)
    (e₀ eY r y eR : ℝ)
    (heY : 0 ≤ eY) (hy : 0 ≤ y)
    (hBase : p07RectOpNorm2Le
      (fun i j ↦ p07RectMatMul Y R i j - A i j) e₀)
    (hDeltaY : p07RectOpNorm2Le ΔY eY)
    (hR : p07RectOpNorm2Le R r)
    (hY : p07RectOpNorm2Le Y y)
    (hDeltaR : p07RectOpNorm2Le ΔR eR) :
    p07RectOpNorm2Le (p07BackwardError Y ΔY R ΔR A)
      (e₀ + (eY * r + (y * eR + eY * eR)))
```

## Elaborated target type

```lean
∀ {m n : Nat} (Y ΔY : Fin m → Fin n → Real) (R ΔR : Fin n → Fin n → Real) (A : Fin m → Fin n → Real)
  (e₀ eY r y eR : Real),
  Real.instLE.le 0 eY →
    Real.instLE.le 0 y →
      HighamBench.p07RectOpNorm2Le (fun i j => instHSub.hSub (HighamBench.p07RectMatMul Y R i j) (A i j)) e₀ →
        HighamBench.p07RectOpNorm2Le ΔY eY →
          HighamBench.p07RectOpNorm2Le R r →
            HighamBench.p07RectOpNorm2Le Y y →
              HighamBench.p07RectOpNorm2Le ΔR eR →
                HighamBench.p07RectOpNorm2Le (HighamBench.p07BackwardError Y ΔY R ΔR A)
                  (instHAdd.hAdd e₀
                    (instHAdd.hAdd (instHMul.hMul eY r) (instHAdd.hAdd (instHMul.hMul y eR) (instHMul.hMul eY eR))))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (Y ΔY : Fin m → Fin n → Real) (R ΔR : Fin n → Fin n → Real) (A : Fin m → Fin n → Real)
  (e₀ eY r y eR : Real)
  (heY : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eY)
  (hy : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) y)
  (hBase :
    @HighamBench.p07RectOpNorm2Le m n
      (fun (i : Fin m) (j : Fin n) =>
        @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@HighamBench.p07RectMatMul m n n Y R i j)
          (A i j))
      e₀)
  (hDeltaY : @HighamBench.p07RectOpNorm2Le m n ΔY eY) (hR : @HighamBench.p07RectOpNorm2Le n n R r)
  (hY : @HighamBench.p07RectOpNorm2Le m n Y y) (hDeltaR : @HighamBench.p07RectOpNorm2Le n n ΔR eR),
  @HighamBench.p07RectOpNorm2Le m n (@HighamBench.p07BackwardError m n Y ΔY R ΔR A)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) e₀
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eY r)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y eR)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eY eR))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P07Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P07Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p07BackwardError`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `35ff0f1732e66d99522b9fad625edccc29dc4cc776ff61884eb53a8495684051`

Type:

```lean
{m n : Nat} →
  (Fin m → Fin n → Real) →
    (Fin m → Fin n → Real) →
      (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} →
  (Y ΔY : Fin m → Fin n → Real) → (R ΔR : Fin n → Fin n → Real) → (A : Fin m → Fin n → Real) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} Y ΔY R ΔR A i j =>
  instHAdd.hAdd (instHSub.hSub (HighamBench.p07RectMatMul Y R i j) (A i j))
    (instHAdd.hAdd (HighamBench.p07RectMatMul ΔY R i j)
      (instHAdd.hAdd (HighamBench.p07RectMatMul Y ΔR i j) (HighamBench.p07RectMatMul ΔY ΔR i j)))
```

### D002: `HighamBench.p07RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f4aa477905f0e4f5f887cacfd9cfe27184181051fd51bd5c72a323007e9f230f`

Type:

```lean
{m n p : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin p → Real) → Fin m → Fin p → Real
```

Fully explicit type:

```lean
{m n p : Nat} → (A : Fin m → Fin n → Real) → (B : Fin n → Fin p → Real) → Fin m → Fin p → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D003: `HighamBench.p07RectOpNorm2Le`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3bc11a5a31a6cc30e603ebb4db699976fe20c2ba6cf962c97a349a0d3defc334`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (c : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A c =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (HighamBench.p07VecNorm2 (HighamBench.p07MatVec A x)) (instHMul.hMul c (HighamBench.p07VecNorm2 x))
```

### D004: `HighamBench.p07MatVec`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c20ee94e8dfa7a21c0972744b89ff2650d7462ecb441662c2e1930d980ab8dc5`

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

### D005: `HighamBench.p07VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9ab663fe9a74061006c9976250ea5e93003df8c9f220f04dff6f950bb66a0ff4`

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

### D006: `Fin`

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

### D007: `HAdd.hAdd`

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

### D008: `HMul.hMul`

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

### D009: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D010: `LE.le`

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

### D011: `Nat`

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

### D012: `OfNat.ofNat`

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

### D013: `Real`

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

### D014: `Real.instAdd`

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

### D015: `Real.instLE`

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

### D016: `Real.instMul`

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

### D017: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D018: `Real.instZero`

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

### D019: `Zero.toOfNat0`

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

### D020: `instHAdd`

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

### D021: `instHMul`

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

### D022: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D023: `Fin.fintype`

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

### D024: `Finset.sum`

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

### D025: `Finset.univ`

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

### D026: `Real.instAddCommMonoid`

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

### D027: `HPow.hPow`

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

### D028: `Monoid.toNatPow`

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

### D029: `Real.instMonoid`

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

### D030: `Real.sqrt`

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

### D031: `instHPow`

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

### D032: `instOfNatNat`

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

### `HighamBench.P07Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P07Definitions.lean`
SHA-256: `456801a246d914d7d5bd4fdb8c43f735ab409ae3d697f68cc9220f80637de59c`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P07. -/
noncomputable def p07VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p07MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Product of two compatible finite rectangular matrices. -/
noncomputable def p07RectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Homogeneous rectangular operator-2 upper-bound certificate. -/
def p07RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec A x) ≤ c * p07VecNorm2 x

/-- Homogeneous lower singular-value certificate. -/
def p07RectLowerBound {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (c : ℝ) : Prop :=
  ∀ x, c * p07VecNorm2 x ≤ p07VecNorm2 (p07MatVec A x)

/-- A rectangular matrix acts isometrically on Euclidean vectors. -/
def p07Isometry {m n : ℕ} (Q : Fin m → Fin n → ℝ) : Prop :=
  ∀ x, p07VecNorm2 (p07MatVec Q x) = p07VecNorm2 x

/-- Paired lower/upper singular-value certificate used to express the
condition-number identity in P07 Lemma 2.1 without choosing singular values. -/
def p07ConditionCertificate {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (lower upper : ℝ) : Prop :=
  p07RectLowerBound A lower ∧ p07RectOpNorm2Le A upper

/-- Exact error matrix expanded in the proof of P07 Theorem 3.5. -/
noncomputable def p07BackwardError {m n : ℕ}
    (Y ΔY : Fin m → Fin n → ℝ)
    (R ΔR : Fin n → Fin n → ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦
    (p07RectMatMul Y R i j - A i j) +
      (p07RectMatMul ΔY R i j +
        (p07RectMatMul Y ΔR i j + p07RectMatMul ΔY ΔR i j))

end HighamBench
```
