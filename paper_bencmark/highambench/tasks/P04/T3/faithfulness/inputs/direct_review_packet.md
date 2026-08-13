# Declaration dossier for P04-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p04_t3_block_lu_solve_backward_error
    {N : ℕ} (uLow uFma u : ℝ) (q n bdim : ℕ)
    (A L U ΔF ΔL ΔU M : Fin N → Fin N → ℝ)
    (x y rhs : Fin N → ℝ)
    (hfact : p04MatMul L U = A + ΔF)
    (hforward : p04MatVec (L + ΔL) y = rhs)
    (hbackward : p04MatVec (U + ΔU) x = y)
    (hΔF : ∀ i j,
      |ΔF i j| ≤ p04FactorizationCoeff uLow uFma u q n bdim * M i j)
    (hLΔU : ∀ i j,
      |p04MatMul L ΔU i j| ≤ gamma u n * M i j)
    (hΔLU : ∀ i j,
      |p04MatMul ΔL U i j| ≤ gamma u n * M i j)
    (hΔLΔU : ∀ i j,
      |p04MatMul ΔL ΔU i j| ≤ (gamma u n) ^ 2 * M i j) :
    ∃ ΔA : Fin N → Fin N → ℝ,
      p04MatVec (A + ΔA) x = rhs ∧
      ∀ i j,
        |ΔA i j| ≤
          (p04FactorizationCoeff uLow uFma u q n bdim +
              2 * gamma u n + (gamma u n) ^ 2) * M i j
```

## Elaborated target type

```lean
∀ {N : Nat} (uLow uFma u : Real) (q n bdim : Nat) (A L U ΔF ΔL ΔU M : Fin N → Fin N → Real) (x y rhs : Fin N → Real),
  Eq (HighamBench.p04MatMul L U) (instHAdd.hAdd A ΔF) →
    Eq (HighamBench.p04MatVec (instHAdd.hAdd L ΔL) y) rhs →
      Eq (HighamBench.p04MatVec (instHAdd.hAdd U ΔU) x) y →
        (∀ (i j : Fin N),
            Real.instLE.le (abs (ΔF i j))
              (instHMul.hMul (HighamBench.p04FactorizationCoeff uLow uFma u q n bdim) (M i j))) →
          (∀ (i j : Fin N),
              Real.instLE.le (abs (HighamBench.p04MatMul L ΔU i j)) (instHMul.hMul (HighamBench.gamma u n) (M i j))) →
            (∀ (i j : Fin N),
                Real.instLE.le (abs (HighamBench.p04MatMul ΔL U i j)) (instHMul.hMul (HighamBench.gamma u n) (M i j))) →
              (∀ (i j : Fin N),
                  Real.instLE.le (abs (HighamBench.p04MatMul ΔL ΔU i j))
                    (instHMul.hMul (instHPow.hPow (HighamBench.gamma u n) 2) (M i j))) →
                Exists fun ΔA =>
                  And (Eq (HighamBench.p04MatVec (instHAdd.hAdd A ΔA) x) rhs)
                    (∀ (i j : Fin N),
                      Real.instLE.le (abs (ΔA i j))
                        (instHMul.hMul
                          (instHAdd.hAdd
                            (instHAdd.hAdd (HighamBench.p04FactorizationCoeff uLow uFma u q n bdim)
                              (instHMul.hMul 2 (HighamBench.gamma u n)))
                            (instHPow.hPow (HighamBench.gamma u n) 2))
                          (M i j)))
```

## Fully explicit elaborated target type

```lean
∀ {N : Nat} (uLow uFma u : Real) (q n bdim : Nat) (A L U ΔF ΔL ΔU M : Fin N → Fin N → Real) (x y rhs : Fin N → Real)
  (hfact :
    @Eq.{1} (Fin N → Fin N → Real) (@HighamBench.p04MatMul N L U)
      (@HAdd.hAdd.{0, 0, 0} (Fin N → Fin N → Real) (Fin N → Fin N → Real) (Fin N → Fin N → Real)
        (@instHAdd.{0} (Fin N → Fin N → Real)
          (@Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Fin N → Real) fun (i : Fin N) =>
            @Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Real) fun (i : Fin N) => Real.instAdd))
        A ΔF))
  (hforward :
    @Eq.{1} (Fin N → Real)
      (@HighamBench.p04MatVec N
        (@HAdd.hAdd.{0, 0, 0} (Fin N → Fin N → Real) (Fin N → Fin N → Real) (Fin N → Fin N → Real)
          (@instHAdd.{0} (Fin N → Fin N → Real)
            (@Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Fin N → Real) fun (i : Fin N) =>
              @Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Real) fun (i : Fin N) => Real.instAdd))
          L ΔL)
        y)
      rhs)
  (hbackward :
    @Eq.{1} (Fin N → Real)
      (@HighamBench.p04MatVec N
        (@HAdd.hAdd.{0, 0, 0} (Fin N → Fin N → Real) (Fin N → Fin N → Real) (Fin N → Fin N → Real)
          (@instHAdd.{0} (Fin N → Fin N → Real)
            (@Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Fin N → Real) fun (i : Fin N) =>
              @Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Real) fun (i : Fin N) => Real.instAdd))
          U ΔU)
        x)
      y)
  (hΔF :
    ∀ (i j : Fin N),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔF i j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (HighamBench.p04FactorizationCoeff uLow uFma u q n bdim) (M i j)))
  (hLΔU :
    ∀ (i j : Fin N),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p04MatMul N L ΔU i j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (HighamBench.gamma u n) (M i j)))
  (hΔLU :
    ∀ (i j : Fin N),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p04MatMul N ΔL U i j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (HighamBench.gamma u n) (M i j)))
  (hΔLΔU :
    ∀ (i j : Fin N),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p04MatMul N ΔL ΔU i j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (HighamBench.gamma u n) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (M i j))),
  @Exists.{1} (Fin N → Fin N → Real) fun (ΔA : Fin N → Fin N → Real) =>
    And
      (@Eq.{1} (Fin N → Real)
        (@HighamBench.p04MatVec N
          (@HAdd.hAdd.{0, 0, 0} (Fin N → Fin N → Real) (Fin N → Fin N → Real) (Fin N → Fin N → Real)
            (@instHAdd.{0} (Fin N → Fin N → Real)
              (@Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Fin N → Real) fun (i : Fin N) =>
                @Pi.instAdd.{0, 0} (Fin N) (fun (a : Fin N) => Real) fun (i : Fin N) => Real.instAdd))
            A ΔA)
          x)
        rhs)
      (∀ (i j : Fin N),
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (HighamBench.p04FactorizationCoeff uLow uFma u q n bdim)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (HighamBench.gamma u n)))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) (HighamBench.gamma u n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (M i j)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P04Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P04Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

Type:

```lean
Real → Nat → Real
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D002: `HighamBench.p04FactorizationCoeff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `58150a8b6a28d9f37e85b4fa160f7cd8e719b20162f1f5649a8627672eae4572`

Type:

```lean
Real → Real → Real → Nat → Nat → Nat → Real
```

Fully explicit type:

```lean
(uLow uFma u : Real) → (q n b : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun uLow uFma u q n b =>
  instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 uLow) (instHPow.hPow uLow 2))
    (instHMul.hMul
      (Real.instMax.max
        (instHAdd.hAdd
          (instHAdd.hAdd (HighamBench.gamma uFma (instHSub.hSub q 1))
            (HighamBench.gamma u (instHAdd.hAdd (instHSub.hSub n b) 1)))
          (instHMul.hMul (HighamBench.gamma uFma (instHSub.hSub q 1))
            (HighamBench.gamma u (instHAdd.hAdd (instHSub.hSub n b) 1))))
        (HighamBench.gamma u b))
      (instHPow.hPow (instHAdd.hAdd 1 uLow) 2))
```

### D003: `HighamBench.p04MatMul`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6c71297d2486e8ef22f02ec47100b9bbcc0e87cf0e3cdfec01f82b8944677f5a`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D004: `HighamBench.p04MatVec`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fcc6c49f75d28a5e1cd319f8faa78701086a74db8b07f8b6e8628c584f9f351c`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D005: `HighamBench.p04FactorizationCoeff._proof_1`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `7b8f48496f9b74b3b702884c5b69a9939b93b9c70db21de69d00271603bfb6d4`

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

### D007: `Eq`

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

### D008: `Exists`

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
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `2c99a1926bdac64e3a35f3fa155d689dc336fe4eb783a294540e765003beae74`

Hash-verified prior interpretation:

HAdd.hAdd selects the heterogeneous-addition operation supplied by its typeclass instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `8915b03a91c892e98db02c0973c28bad864cb016b465642b346d14f34e446a76`

Hash-verified prior interpretation:

HMul.hMul selects the heterogeneous-multiplication operation supplied by its typeclass instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D013: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `c476dc1b2ea074ec4bd39cbce7c0ff24c628f572b131686eb6963c3e7131fb19`

Hash-verified prior interpretation:

LE.le selects the non-strict order relation supplied for the type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D015: `Nat`

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

### D016: `Nat.instAtLeastTwoHAddOfNat`

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

### D017: `Nat.instNeZeroSucc`

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

### D018: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `37f0ecf64bd742bcc93f38034359021b711500e02dfff8ff3c1f2db70c293777`

Hash-verified prior interpretation:

OfNat.ofNat interprets a natural-number literal in the requested type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D020: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `3483e25ab144d9f6b5fc2cc409de11ee2b17d27a19ada9ad855dd312dd9e9444`

Hash-verified prior interpretation:

Real is mathlib's type of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `2600632309109b9eef72c7a64a51bb9f19137f042a46f93146279b789a7082de`

Hash-verified prior interpretation:

Real.instAdd supplies ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `1f5c2cb2573ac7ae1df7dd2fb4169025e230cf39eed10a3bb6015178c0a216f9`

Hash-verified prior interpretation:

Real.instAddGroup supplies the additive-group structure on Real, including negation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `96f4d2c6a6ed1a6072650c127a11af0743154b941d6d0bf8072e93589cecd9d1`

Hash-verified prior interpretation:

Real.instLE supplies the usual non-strict order on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D025: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `cc1d87e896e40ca98beaba733d8981b2be417bf56b3cd139099a7fe33f462ebe`

Hash-verified prior interpretation:

Real.instMul supplies ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`
- Reuse SHA-256: `11515d289291036cdc99fffdf3a5fc5b207622a159829c92fabab8dbc5d90b0b`

Hash-verified prior interpretation:

Real.instNatCast supplies the canonical embedding of Nat into Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `094296f36b8f60f6e248ebe56a2c9cd0a87d2a95d53003f3fb7fc76713aa00a8`

Hash-verified prior interpretation:

Real.lattice supplies max and min under the usual real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `32a708fd3378d4db96640e2e6509634aa96151e94172fcf7f08b2b9a3e3d8a93`

Hash-verified prior interpretation:

abs a is max(a,-a), hence standard absolute value on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `8f153af5aa1baf5f6424ff39c5d08323cd358ffeece5f9ced3043ad2cffa73b6`

Hash-verified prior interpretation:

instHAdd lifts a homogeneous Add operation to HAdd.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `46765db2b9c4e049bf61e51bed5aa60e6f7c8d1bae634a71be3cc3d75d34fb61`

Hash-verified prior interpretation:

instHMul lifts a homogeneous Mul operation to HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D032: `instOfNatAtLeastTwo`

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

### D033: `instOfNatNat`

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

### D034: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `df63d67be0a47651e461c7c0857bc6f06de6eb2312aa865ec12586eb832a6aa4`

Hash-verified prior interpretation:

DivInvMonoid.toDiv extracts the division operation from a division/inverse monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Fin.fintype`

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

### D036: `Finset.sum`

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

### D037: `Finset.univ`

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

### D038: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `7cc520200fbbc81cb5af9bd69f23a7fa8d3c03985e9622d43e610579ec2d1769`

Hash-verified prior interpretation:

HDiv.hDiv selects the heterogeneous-division operation supplied by its instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `b332fe28eda7461a55409befd08f414509b9cfcdfd7730a06048da7b83c87c62`

Hash-verified prior interpretation:

HSub.hSub selects the heterogeneous-subtraction operation supplied by its instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `Max.max`

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

### D041: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`
- Reuse SHA-256: `fb2cb8ca958b6b9b06056213ea79965d590b2ebafdc4f8f0a3e9756bb034f7d8`

Hash-verified prior interpretation:

Nat.cast maps a natural number to the corresponding value in a type with NatCast.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D042: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`
- Reuse SHA-256: `decd674803aac02ebd385212bdf204f6212acc91345ee72dc5ad8d7b3dfe3bb0`

Hash-verified prior interpretation:

One.toOfNat1 turns a One instance into the OfNat instance for the literal 1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D043: `Real.instAddCommMonoid`

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

### D044: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `ab4d730c0e1a3194e52e83a676c0de91daf486521f7cb16d7cf21b77a11bde44`

Hash-verified prior interpretation:

Real.instDivInvMonoid supplies real multiplication, inverse, and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D045: `Real.instMax`

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

### D046: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`
- Reuse SHA-256: `278b68069fb2dca8c3606f359ce8d431c0f9e00fb8e417d19697eed49e4fc22e`

Hash-verified prior interpretation:

Real.instOne supplies the multiplicative identity 1 in Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D047: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `b749cd229005c3a1648902abc2bc67a4c2a7c085861f5f029cae4ef461a4036c`

Hash-verified prior interpretation:

Real.instSub supplies ordinary real subtraction a-b=a+(-b).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D048: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`
- Reuse SHA-256: `62b44b9ddca5bb499eb94e1c4dcea8170c8d2b20443add211beee7e2ca3209f3`

Hash-verified prior interpretation:

instAddNat supplies ordinary natural-number addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D049: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `bf79a894f33a6eb637c4e4c038bf278981a5dc8a3e147af4deafafc35a9b734c`

Hash-verified prior interpretation:

instHDiv lifts homogeneous division to HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D050: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `f39a60e5a7fdc34f852de226b72fe543dea9c623443daecb3a67b84708f713fb`

Hash-verified prior interpretation:

instHSub lifts homogeneous subtraction to HSub.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D051: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

Type:

```lean
Sub Nat
```

Fully explicit type:

```lean
Sub.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
```

### D052: `Nat.AtLeastTwo`

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
