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
- Semantic SHA-256: `c20ee94e8dfa7a21c0972744b89ff2650d7462ecb441662c2e1930d980ab8dc5`
- Reuse SHA-256: `2c57ade87344bcd23c15d60d29e08d8e736d0b39921a84f5f6eae43a2cebef3c`

Hash-verified prior interpretation:

For an m-by-n real array A and n-vector x, this returns the m-vector whose i-th entry is the finite sum of A i j times x j.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `HighamBench.p07VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `9ab663fe9a74061006c9976250ea5e93003df8c9f220f04dff6f950bb66a0ff4`
- Reuse SHA-256: `7b95691578028c3cbc7bdfea5d3bf7a47abc942b755f9b237c7c74cbb6bf2862`

Hash-verified prior interpretation:

This is the Euclidean vector 2-norm, the square root of the sum of the squares of all coordinates.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `f53009fa223bbdaf32a11aabafd6ae3905217db5e5485a58ba85a5a9bbeabf26`

Hash-verified prior interpretation:

Fin n is the finite coordinate type with n elements indexed from zero through n minus one.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `4735d44aa1c8d5538ec3e2f96011a3779a892715d104b019269f656a4cb8b285`

Hash-verified prior interpretation:

This dispatches the selected heterogeneous addition operation, which here is ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `1762e1a6d37464af56133510a8e2f8d2d3a2f73f280ffc8c3b9782bc83c4f5db`

Hash-verified prior interpretation:

This dispatches the selected heterogeneous multiplication operation, which here is ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `1d6c5538d176983f9f66a5e8b158177e8e77312bfb5c479547f1aa6803644b14`

Hash-verified prior interpretation:

This dispatches the selected non-strict order relation, which here is real less-than-or-equal.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `9f4ae78e268f549f9fa054e8a40dc22788e317dd074a667cdbf8b9f9a04c9e0f`

Hash-verified prior interpretation:

This interprets a natural-number literal in the requested type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `0494ec48a9b90eb653272c5d824dd315471ba96930fec5ed804c46889b610589`

Hash-verified prior interpretation:

Real is Lean's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `55ec683888ef424087b3c22991e754a8e5b90baebaa3f3bc29fb9149cf1f6338`

Hash-verified prior interpretation:

This is ordinary addition on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `2ed855b976956890f6711c98a5bc63a243beeefa08dc5896af2afad348a74bd8`

Hash-verified prior interpretation:

This is the standard non-strict order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `b5ca9ce66e8e0587bfc928482989109c5e9fb5d61c08cd29b8cd647786c9f0bb`

Hash-verified prior interpretation:

This is ordinary multiplication on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `fc3a9dc5bf82509a928c929795409ec170fd84f45c7d62e1469b4cba24ec9f78`

Hash-verified prior interpretation:

This lifts a homogeneous Add instance to heterogeneous-addition notation with the same input and output type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `82fca9b6c172b8aeabc0990e33296f4c8cefd3de30cc36f77b5ad630a722f8aa`

Hash-verified prior interpretation:

This lifts a homogeneous Mul instance to heterogeneous-multiplication notation with the same input and output type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `39d9783de210591165f8499841e03d99a0a0b62255eb37f35a73bb01a49c2398`

Hash-verified prior interpretation:

This provides the finite enumeration of every element of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `a63cd30eebffc4e76d0571b9ebf5db7feee1cfd30b57b048e28ebe78c96ac2cf`

Hash-verified prior interpretation:

This forms the finite additive sum of a function over a finite set.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `8d3033a348432d628aa39091e52f7667d26e9f28843d61f06169d3818f9bc98c`

Hash-verified prior interpretation:

This is the finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `2436f37fe5f5b335500c23bb11b11d3cd2846daac0a0cf97783d3ecaa14c4a74`

Hash-verified prior interpretation:

This supplies real addition, zero, associativity, commutativity, and identity laws to finite sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `952e5795ef7760dad834bbcc3b861fae368185e0dd6070f16dd7164291a4fc5b`

Hash-verified prior interpretation:

This dispatches exponentiation, here raising a real coordinate to a natural-number power.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `a177366079d99333be27eafbc37babf4ee79482cd37f3837ae3662025699994f`

Hash-verified prior interpretation:

This supplies natural-number powers from repeated multiplication in a monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `5ecabffed05500c8ce16d7e7757c9f1a4b160004e0f0616f03a7ddefa43f8efa`

Hash-verified prior interpretation:

This supplies real multiplication, one, and natural powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `0817c22961009afbc31736125fe57848bc41bcfcd5f650dab32ca6cb7a9331fd`

Hash-verified prior interpretation:

This is the nonnegative real square-root function.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `8957e4a97b00059c55dc6f45409d20d173c0b722eca8c932ec27934e2b6c0331`

Hash-verified prior interpretation:

This lifts a Pow instance to heterogeneous-power notation while retaining the same base and result type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `9fa32deaa97ab2beed5a53804c107f2ed5a722fbf240731dd537975f9920a6b9`

Hash-verified prior interpretation:

This interprets each natural-number literal as that same natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
