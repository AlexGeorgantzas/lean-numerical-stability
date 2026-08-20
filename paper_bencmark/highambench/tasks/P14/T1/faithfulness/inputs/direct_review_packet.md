# Declaration dossier for P14-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p14_t1_positive_recursive_sum_relative_error
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P14BasicSumExecution x (u t))
    (hu : Filter.Tendsto u l (nhds 0)) :
    let exactSum := p14ExpSum x
    0 < exactSum ∧
    (∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i)) ∧
    (∀ᶠ t in l,
      |p14ExactComputedExpSum (run t) -
          p14RecursiveComputedExpSum (run t)| ≤
        gamma (u t) (n - 1) *
          ∑ i, |p14ComputedExp (run t) i|) ∧
    (∀ᶠ t in l,
      |p14BasicSumDelta (run t)| ≤
        p14BasicSumFiniteEnvelope n (u t) exactSum) ∧
    (∀ᶠ t in l,
      p14BasicSumFiniteEnvelope n (u t) exactSum =
        (n + 1 : ℝ) * u t * exactSum +
          p14BasicSumQuadraticRemainder n exactSum (u t)) ∧
    (fun t => p14BasicSumQuadraticRemainder n exactSum (u t)) =O[l]
      (fun t => (u t) ^ 2) ∧
    ∀ t,
      p14RecursiveComputedExpSum (run t) =
        exactSum + p14BasicSumDelta (run t)
```

## Elaborated target type

```lean
∀ {n : Nat},
  instLTNat.lt 0 n →
    ∀ {ι : Type u_1} {l : Filter ι} [l.NeBot] (x : Fin n → Real) (u : ι → Real)
      (run : (t : ι) → HighamBench.P14BasicSumExecution x (u t)),
      Filter.Tendsto u l (nhds 0) →
        have exactSum := HighamBench.p14ExpSum x;
        And (Real.instLT.lt 0 exactSum)
          (And
            (∀ (t : ι) (i : Fin n),
              Real.instLE.le (abs (instHSub.hSub (HighamBench.p14ComputedExp (run t) i) (Real.exp (x i))))
                (instHMul.hMul (u t) (Real.exp (x i))))
            (And
              (Filter.Eventually
                (fun t =>
                  Real.instLE.le
                    (abs
                      (instHSub.hSub (HighamBench.p14ExactComputedExpSum (run t))
                        (HighamBench.p14RecursiveComputedExpSum (run t))))
                    (instHMul.hMul (HighamBench.gamma (u t) (instHSub.hSub n 1))
                      (Finset.univ.sum fun i => abs (HighamBench.p14ComputedExp (run t) i))))
                l)
              (And
                (Filter.Eventually
                  (fun t =>
                    Real.instLE.le (abs (HighamBench.p14BasicSumDelta (run t)))
                      (HighamBench.p14BasicSumFiniteEnvelope n (u t) exactSum))
                  l)
                (And
                  (Filter.Eventually
                    (fun t =>
                      Eq (HighamBench.p14BasicSumFiniteEnvelope n (u t) exactSum)
                        (instHAdd.hAdd (instHMul.hMul (instHMul.hMul (instHAdd.hAdd n.cast 1) (u t)) exactSum)
                          (HighamBench.p14BasicSumQuadraticRemainder n exactSum (u t))))
                    l)
                  (And
                    (Asymptotics.IsBigO l (fun t => HighamBench.p14BasicSumQuadraticRemainder n exactSum (u t)) fun t =>
                      instHPow.hPow (u t) 2)
                    (∀ (t : ι),
                      Eq (HighamBench.p14RecursiveComputedExpSum (run t))
                        (instHAdd.hAdd exactSum (HighamBench.p14BasicSumDelta (run t)))))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l] (x : Fin n → Real) (u : ι → Real)
  (run : (t : ι) → @HighamBench.P14BasicSumExecution n x (u t))
  (hu :
    @Filter.Tendsto.{u_1, 0} ι Real u l
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))),
  have exactSum : Real := @HighamBench.p14ExpSum n x;
  And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) exactSum)
    (And
      (∀ (t : ι) (i : Fin n),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HighamBench.p14ComputedExp n x (u t) (run t) i) (Real.exp (x i))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (u t) (Real.exp (x i))))
      (And
        (@Filter.Eventually.{u_1} ι
          (fun (t : ι) =>
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HighamBench.p14ExactComputedExpSum n x (u t) (run t))
                  (@HighamBench.p14RecursiveComputedExpSum n x (u t) (run t))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.gamma (u t)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n))
                  fun (i : Fin n) =>
                  @abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p14ComputedExp n x (u t) (run t) i))))
          l)
        (And
          (@Filter.Eventually.{u_1} ι
            (fun (t : ι) =>
              @LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p14BasicSumDelta n x (u t) (run t)))
                (HighamBench.p14BasicSumFiniteEnvelope n (u t) exactSum))
            l)
          (And
            (@Filter.Eventually.{u_1} ι
              (fun (t : ι) =>
                @Eq.{1} Real (HighamBench.p14BasicSumFiniteEnvelope n (u t) exactSum)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast n)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                        (u t))
                      exactSum)
                    (HighamBench.p14BasicSumQuadraticRemainder n exactSum (u t))))
              l)
            (And
              (@Asymptotics.IsBigO.{u_1, 0, 0} ι Real Real Real.norm Real.norm l
                (fun (t : ι) => HighamBench.p14BasicSumQuadraticRemainder n exactSum (u t)) fun (t : ι) =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) (u t)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (∀ (t : ι),
                @Eq.{1} Real (@HighamBench.p14RecursiveComputedExpSum n x (u t) (run t))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) exactSum
                    (@HighamBench.p14BasicSumDelta n x (u t) (run t)))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P14Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P14Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P14BasicSumExecution`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a2f9e06f3a9c55a133571a2a3687d610900196ccee5808d13d38c3ec443bad12`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real → Type
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → (u : Real) → Type
```

### D002: `HighamBench.gamma`

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

### D003: `HighamBench.p14BasicSumDelta`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a7211acf54b70f5641ce97b8637c7a8dcdaae3ec1ed975b22ed5032ca5540c51`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → Real
```

Fully explicit type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → (run : @HighamBench.P14BasicSumExecution n x u) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {x} {u} run => instHSub.hSub (HighamBench.p14RecursiveComputedExpSum run) (HighamBench.p14ExpSum x)
```

### D004: `HighamBench.p14BasicSumFiniteEnvelope`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7fdb1cddeb40aebd3999f4061924173a939d0c844568df21f2e4775e2d3d879b`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (u exactSum : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n u exactSum => instHMul.hMul (instHAdd.hAdd u (instHMul.hMul (HighamBench.gamma u n) (instHAdd.hAdd 1 u))) exactSum
```

### D005: `HighamBench.p14BasicSumQuadraticRemainder`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `af68d9f0691df4a3560a4f7556d085db28ba0d4ced4095c46fc61f86390241d0`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (exactSum u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n exactSum u =>
  instHDiv.hDiv
    (instHMul.hMul (instHMul.hMul (instHMul.hMul n.cast (instHAdd.hAdd n.cast 1)) exactSum) (instHPow.hPow u 2))
    (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D006: `HighamBench.p14ComputedExp`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b5627e046b4d7780bbb7b25e3432520a166096fc133aeb8921dacfff73a2a6c6`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → (run : @HighamBench.P14BasicSumExecution n x u) → (i : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {x} {u} run i => instHMul.hMul (Real.exp (x i)) (instHAdd.hAdd 1 (run.expError i))
```

### D007: `HighamBench.p14ExactComputedExpSum`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b9429d8dbc06888b2c40fc7181036882f0350ced97a644a3b0ccf383d7b92bf7`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → Real
```

Fully explicit type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → (run : @HighamBench.P14BasicSumExecution n x u) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {x} {u} run => Finset.univ.sum fun i => HighamBench.p14ComputedExp run i
```

### D008: `HighamBench.p14ExpSum`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8f913d09c91e68ed49377c477b128a614150d79814d916fc11d9e5fe77b46368`

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
fun {n} x => Finset.univ.sum fun i => Real.exp (x i)
```

### D009: `HighamBench.p14RecursiveComputedExpSum`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9f68a7d40c9253e940c5244764fa7ee1cac6dcadd8492a314a9e95439ae43f06`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → Real
```

Fully explicit type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → (run : @HighamBench.P14BasicSumExecution n x u) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {x} {u} run => HighamBench.recursiveSum run.fp.fl_add n (HighamBench.p14ComputedExp run)
```

### D010: `HighamBench.P14BasicSumExecution.expError`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3a7500f0117a5fc1c6f4a9d58a5d5b1e2a03c0e9a9e54f780025ab59e6d8a4f6`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → (self : @HighamBench.P14BasicSumExecution n x u) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n x u self => self.3
```

### D011: `HighamBench.P14BasicSumExecution.fp`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b4b591d07913f182c08f573af66c769bcdb7bd09c781014ef7a5970185d39745`

Type:

```lean
{n : Nat} → {x : Fin n → Real} → {u : Real} → HighamBench.P14BasicSumExecution x u → HighamBench.StandardAddModel
```

Fully explicit type:

```lean
{n : Nat} →
  {x : Fin n → Real} → {u : Real} → (self : @HighamBench.P14BasicSumExecution n x u) → HighamBench.StandardAddModel
```

Definition body (one-level semantic boundary):

```lean
fun n x u self => self.1
```

### D012: `HighamBench.P14BasicSumExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `7e0ad978f53db3b008e141783424119716d20115579f809d7b23bfb4cf4931d5`

Type:

```lean
{n : Nat} →
  {x : Fin n → Real} →
    {u : Real} →
      (fp : HighamBench.StandardAddModel) →
        Eq fp.u u →
          (expError : Fin n → Real) →
            (∀ (i : Fin n), Real.instLE.le (abs (expError i)) u) → HighamBench.P14BasicSumExecution x u
```

Fully explicit type:

```lean
{n : Nat} →
  {x : Fin n → Real} →
    {u : Real} →
      (fp : HighamBench.StandardAddModel) →
        (unit_eq : @Eq.{1} Real (HighamBench.StandardAddModel.u fp) u) →
          (expError : Fin n → Real) →
            (expError_le :
                ∀ (i : Fin n),
                  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (expError i)) u) →
              @HighamBench.P14BasicSumExecution n x u
```

### D013: `HighamBench.StandardAddModel.fl_add`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `74b643970f719ee8bb48fde2f9970bb4c4568fb59d10e316bf1b16e3d35ea302`

Type:

```lean
HighamBench.StandardAddModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.StandardAddModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D014: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3a24e7a5c707c014d59b9d90d536db1f1c79ef135d2ba34adb6af8a4258efe41`

Type:

```lean
(Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
(flAdd : Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun flAdd x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Real) x
    (fun x f x_2 =>
      HighamBench.recursiveSum.match_1 (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Real) x → Real) x
        x_2 (fun x x_3 => 0)
        (fun n v x => if h : Eq n 0 then v ⟨0, ⋯⟩ else flAdd (x.1 fun i => v i.castSucc) (v (Fin.last n))) f)
    x_1
```

### D015: `HighamBench.StandardAddModel`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `3af55263a5df34d0cebe2443070580aacd6049ec653e6aa810dee85f7d8da3b8`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D016: `HighamBench.StandardAddModel.u`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c64c9c9e28b3861652ba7445f856da30d4b2e48822f5710fa9e1e9bcf81ad0a8`

Type:

```lean
HighamBench.StandardAddModel → Real
```

Fully explicit type:

```lean
(self : HighamBench.StandardAddModel) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D017: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7f01e5fdb761df0e050b0929b93312fc9084bc345726c816952ed0fd4844be27`

Type:

```lean
∀ (n : Nat), Eq n 0 → instLTNat.lt 0 (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ (n : Nat) (h : @Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D018: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `56d4f4744c0103a83d3305dc49473baf5a72c1037bbec52ff87f6f4a5419f79e`

Type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      ((x : Fin 0 → Real) → motive 0 x) →
        ((n : Nat) → (v : Fin (instHAdd.hAdd n 1) → Real) → motive n.succ v) → motive x x_1
```

Fully explicit type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      (h_1 :
          (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Real) →
            motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
        (h_2 :
            (n : Nat) →
              (v :
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Real) →
                motive (Nat.succ n) v) →
          motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D019: `HighamBench.StandardAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `7d89a60d997fdb3f5928a4b754043bc2ff3d75d6af267762a5f86bdca796bc01`

Type:

```lean
(u : Real) →
  Real.instLE.le 0 u →
    (fl_add : Real → Real → Real) →
      (∀ (x : Real), Eq (fl_add 0 x) x) →
        (∀ (x y : Real),
            Exists fun δ =>
              And (Real.instLE.le (abs δ) u)
                (Eq (fl_add x y) (instHMul.hMul (instHAdd.hAdd x y) (instHAdd.hAdd 1 δ)))) →
          HighamBench.StandardAddModel
```

Fully explicit type:

```lean
(u : Real) →
  (u_nonneg :
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u) →
    (fl_add : Real → Real → Real) →
      (fl_add_zero :
          ∀ (x : Real),
            @Eq.{1} Real (fl_add (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x) x) →
        (model_add :
            ∀ (x y : Real),
              @Exists.{1} Real fun (δ : Real) =>
                And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup δ) u)
                  (@Eq.{1} Real (fl_add x y)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ)))) →
          HighamBench.StandardAddModel
```

### D020: `And`

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

### D021: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D022: `Eq`

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

### D023: `Filter`

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

### D024: `Filter.Eventually`

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

### D025: `Filter.NeBot`

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

### D026: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D027: `Fin`

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

### D028: `Fin.fintype`

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

### D029: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D030: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D031: `HAdd.hAdd`

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

### D032: `HMul.hMul`

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

### D033: `HPow.hPow`

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

### D034: `HSub.hSub`

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

### D035: `LE.le`

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

### D036: `LT.lt`

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

### D037: `Monoid.toNatPow`

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

### D038: `Nat`

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

### D039: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D040: `OfNat.ofNat`

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

### D041: `One.toOfNat1`

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

### D042: `PseudoMetricSpace.toUniformSpace`

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

### D043: `Real`

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

### D044: `Real.exp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Exponential`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D045: `Real.instAdd`

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

### D046: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D047: `Real.instAddGroup`

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

### D048: `Real.instLE`

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

### D049: `Real.instLT`

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

### D050: `Real.instMonoid`

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

### D051: `Real.instMul`

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

### D052: `Real.instNatCast`

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

### D053: `Real.instOne`

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

### D054: `Real.instSub`

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

### D055: `Real.instZero`

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

### D056: `Real.lattice`

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

### D057: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D058: `Real.pseudoMetricSpace`

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

### D059: `UniformSpace.toTopologicalSpace`

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

### D060: `Zero.toOfNat0`

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

### D061: `abs`

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

### D062: `instHAdd`

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

### D063: `instHMul`

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

### D064: `instHPow`

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

### D065: `instHSub`

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

### D066: `instLTNat`

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

### D067: `instOfNatNat`

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

### D068: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D069: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D070: `DivInvMonoid.toDiv`

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

### D071: `HDiv.hDiv`

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

### D072: `Real.instDivInvMonoid`

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

### D073: `instHDiv`

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

### D074: `Fin.castSucc`

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

### D075: `Fin.last`

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

### D076: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D077: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D078: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → (F_1 : (t : Nat) → (f : @Nat.below.{u} motive t) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D079: `Nat.succ`

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

### D080: `Not`

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

### D081: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a2551097d29bac847f3c59e8213b5882afd4a95e9247c2382e8bce33011974b5`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (c → α) → (Not c → α) → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t : c → α) → (e : Not c → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h e t
```

### D082: `instAddNat`

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

### D083: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D084: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} →
  (t : Nat) → (zero : motive Nat.zero) → (succ : (n : Nat) → motive (Nat.succ n)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D085: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```

Fully explicit type:

```lean
Nat
```

### D086: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```
