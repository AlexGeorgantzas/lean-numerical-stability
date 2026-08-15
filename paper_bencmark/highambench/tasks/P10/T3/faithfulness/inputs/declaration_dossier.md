# Declaration dossier for P10-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t3_sylr_logarithmic_stability {depth : ℕ}
    (run : P10SylRRun depth) :
    P10SylRLogarithmicallyStable run
```

## Elaborated target type

```lean
∀ {depth : Nat} (run : HighamBench.P10SylRRun depth), HighamBench.P10SylRLogarithmicallyStable run
```

## Fully explicit elaborated target type

```lean
∀ {depth : Nat} (run : HighamBench.P10SylRRun depth), @HighamBench.P10SylRLogarithmicallyStable depth run
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P10Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P10Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Analysis.SpecialFunctions.Log.Base`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P10SylRLogarithmicallyStable`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ffa694374b0e3e10cf40fbb79ca8630ed2cd3abaa91a368d83fecbea83789b7a`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Prop
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run =>
  And
    (∀ (k : Nat),
      instLTNat.lt k depth →
        Real.instLE.le (run.errorEnvelope (instHAdd.hAdd k 1))
          (instHAdd.hAdd (instHMul.hMul (HighamBench.p10SylRRecurrenceGrowth run) (run.errorEnvelope k))
            (HighamBench.p10SylRRecurrenceForcing run)))
    (And
      (Real.instLE.le (HighamBench.p10SylRForwardError (HighamBench.p10SylRTopProblem run))
        (HighamBench.p10SylREquation20Bound run))
      (And
        (Eq (HighamBench.p10SylREquation20Bound run)
          (instHMul.hMul
            (instHMul.hMul
              (instHMul.hMul
                (instHMul.hMul 2 (instHPow.hPow (instHPow.hPow 2 depth).cast (instHAdd.hAdd 1 (Real.logb 2 3))))
                (HighamBench.p10SylRHalfMu run))
              (HighamBench.p10SylRConventionalForwardScale run))
            (instHPow.hPow (HighamBench.p10SylRConditionRatio run) (instHPow.hPow 2 depth).log2)))
        (Eq (instHAdd.hAdd 1 (instHPow.hPow 2 depth).log2) (instHAdd.hAdd depth 1))))
```

### D002: `HighamBench.P10SylRRun`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `16fd396ab1d5c8448134bb4459f8bd23e2d66d31d17c00e9c3b3a165b2632b36`

Type:

```lean
Nat → Type 1
```

Fully explicit type:

```lean
(depth : Nat) → Type 1
```

### D003: `HighamBench.P10SylRRun.errorEnvelope`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bc8e2d7d2a13899f7ea739c2e88f8b887f2b5f838db8420b7dc76f385cc7b9b7`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Nat → Real
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.15
```

### D004: `HighamBench.P10SylRRun.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `007bcd290fe373e19871e892e2f37a212e70c56c22d14a37b9b5750536135d93`

Type:

```lean
{depth : Nat} →
  (epsilon : Real) →
    Real.instLT.lt 0 epsilon →
      Real.instLE.le epsilon 1 →
        (mu : Nat → Real) →
          (∀ (n : Nat), Real.instLE.le 0 (mu n)) →
            Monotone mu →
              (∀ (n : Nat), instLTNat.lt 0 n → Real.instLE.le 1 (mu n)) →
                (muDegree : Nat) →
                  (muGrowthConstant : Real) →
                    Real.instLE.le 0 muGrowthConstant →
                      (∀ (n : Nat),
                          instLTNat.lt 0 n →
                            Real.instLE.le (mu n) (instHMul.hMul muGrowthConstant (instHPow.hPow n.cast muDegree))) →
                        (Node : Nat → Type) →
                          (top : Node depth) →
                            (problem : (k : Nat) → instLENat.le k depth → Node k → HighamBench.P10SylRProblem k) →
                              (errorEnvelope : Nat → Real) →
                                (∀ (k : Nat) (hk : instLENat.le k depth) (node : Node k),
                                    Real.instLE.le (HighamBench.p10SylRForwardError (problem k hk node))
                                      (errorEnvelope k)) →
                                  (∀ (k : Nat) (hk : instLENat.le k depth),
                                      Exists fun node =>
                                        Eq (HighamBench.p10SylRForwardError (problem k hk node)) (errorEnvelope k)) →
                                    (child21 child11 child22 child12 :
                                        (k : Nat) → instLTNat.lt k depth → Node (instHAdd.hAdd k 1) → Node k) →
                                      (∀ (k : Nat) (hk : instLTNat.lt k depth) (node : Node (instHAdd.hAdd k 1)),
                                          HighamBench.P10SylRLevelCertificate epsilon
                                            (mu (instHPow.hPow 2 (instHSub.hSub depth 1))) (errorEnvelope k)
                                            (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).A)
                                            (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).B)
                                            (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).C)
                                            (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).exactSolution)
                                            (problem depth ⋯ top).separation.value (problem (instHAdd.hAdd k 1) ⋯ node)
                                            (problem k ⋯ (child21 k hk node)) (problem k ⋯ (child11 k hk node))
                                            (problem k ⋯ (child22 k hk node)) (problem k ⋯ (child12 k hk node))) →
                                        (∀ (k : Nat) (hk : instLENat.le k depth) (node : Node k),
                                            Real.instLE.le (HighamBench.p10DyadicFrobNorm (problem k hk node).A)
                                              (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).A)) →
                                          (∀ (k : Nat) (hk : instLENat.le k depth) (node : Node k),
                                              Real.instLE.le (HighamBench.p10DyadicFrobNorm (problem k hk node).B)
                                                (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).B)) →
                                            (∀ (k : Nat) (hk : instLENat.le k depth) (node : Node k),
                                                Real.instLE.le
                                                  (HighamBench.p10DyadicFrobNorm (problem k hk node).exactSolution)
                                                  (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).exactSolution)) →
                                              (∀ (k : Nat) (hk : instLENat.le k depth) (node : Node k),
                                                  Real.instLE.le (problem depth ⋯ top).separation.value
                                                    (problem k hk node).separation.value) →
                                                Real.instLE.le (errorEnvelope 0)
                                                    (instHMul.hMul
                                                      (instHMul.hMul
                                                        (instHMul.hMul (mu (instHPow.hPow 2 (instHSub.hSub depth 1)))
                                                          epsilon)
                                                        (HighamBench.p10DyadicFrobNorm
                                                          (problem depth ⋯ top).exactSolution))
                                                      (instHDiv.hDiv
                                                        (instHAdd.hAdd
                                                          (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).A)
                                                          (HighamBench.p10DyadicFrobNorm (problem depth ⋯ top).B))
                                                        (problem depth ⋯ top).separation.value)) →
                                                  HighamBench.P10SylRRun depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (epsilon : Real) →
    (epsilon_pos :
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          epsilon) →
      (epsilon_le_one :
          @LE.le.{0} Real Real.instLE epsilon
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
        (mu : Nat → Real) →
          (mu_nonneg :
              ∀ (n : Nat),
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (mu n)) →
            (mu_mono : @Monotone.{0, 0} Nat Real Nat.instPreorder Real.instPreorder mu) →
              (mu_ge_one :
                  ∀ (n : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                      @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (mu n)) →
                (muDegree : Nat) →
                  (muGrowthConstant : Real) →
                    (muGrowthConstant_nonneg :
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          muGrowthConstant) →
                      (mu_polynomial_bound :
                          ∀ (n : Nat),
                            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                              @LE.le.{0} Real Real.instLE (mu n)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muGrowthConstant
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                    (@Nat.cast.{0} Real Real.instNatCast n) muDegree))) →
                        (Node : Nat → Type) →
                          (top : Node depth) →
                            (problem :
                                (k : Nat) → @LE.le.{0} Nat instLENat k depth → Node k → HighamBench.P10SylRProblem k) →
                              (errorEnvelope : Nat → Real) →
                                (errorEnvelope_upper :
                                    ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth) (node : Node k),
                                      @LE.le.{0} Real Real.instLE
                                        (@HighamBench.p10SylRForwardError k (problem k hk node)) (errorEnvelope k)) →
                                  (errorEnvelope_attained :
                                      ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth),
                                        @Exists.{1} (Node k) fun (node : Node k) =>
                                          @Eq.{1} Real (@HighamBench.p10SylRForwardError k (problem k hk node))
                                            (errorEnvelope k)) →
                                    (child21 child11 child22 child12 :
                                        (k : Nat) →
                                          @LT.lt.{0} Nat instLTNat k depth →
                                            Node
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                              Node k) →
                                      (level :
                                          ∀ (k : Nat) (hk : @LT.lt.{0} Nat instLTNat k depth)
                                            (node :
                                              Node
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
                                            @HighamBench.P10SylRLevelCertificate k epsilon
                                              (mu
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) depth
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (errorEnvelope k)
                                              (@HighamBench.p10DyadicFrobNorm depth
                                                (@HighamBench.P10SylRProblem.A depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                              (@HighamBench.p10DyadicFrobNorm depth
                                                (@HighamBench.P10SylRProblem.B depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                              (@HighamBench.p10DyadicFrobNorm depth
                                                (@HighamBench.P10SylRProblem.C depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                              (@HighamBench.p10DyadicFrobNorm depth
                                                (@HighamBench.P10SylRProblem.exactSolution depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                              (@HighamBench.P10SylvesterSeparation.value depth
                                                (@HighamBench.P10SylRProblem.A depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top))
                                                (@HighamBench.P10SylRProblem.B depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top))
                                                (@HighamBench.P10SylRProblem.separation depth
                                                  (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                              (problem
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@Iff.mpr (@LE.le.{0} Nat instLENat (Nat.succ k) depth)
                                                  (@LT.lt.{0} Nat instLTNat k depth) (@Nat.succ_le_iff k depth) hk)
                                                node)
                                              (problem k (@Nat.le_of_lt k depth hk) (child21 k hk node))
                                              (problem k (@Nat.le_of_lt k depth hk) (child11 k hk node))
                                              (problem k (@Nat.le_of_lt k depth hk) (child22 k hk node))
                                              (problem k (@Nat.le_of_lt k depth hk) (child12 k hk node))) →
                                        (node_A_norm_bound :
                                            ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth) (node : Node k),
                                              @LE.le.{0} Real Real.instLE
                                                (@HighamBench.p10DyadicFrobNorm k
                                                  (@HighamBench.P10SylRProblem.A k (problem k hk node)))
                                                (@HighamBench.p10DyadicFrobNorm depth
                                                  (@HighamBench.P10SylRProblem.A depth
                                                    (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))) →
                                          (node_B_norm_bound :
                                              ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth) (node : Node k),
                                                @LE.le.{0} Real Real.instLE
                                                  (@HighamBench.p10DyadicFrobNorm k
                                                    (@HighamBench.P10SylRProblem.B k (problem k hk node)))
                                                  (@HighamBench.p10DyadicFrobNorm depth
                                                    (@HighamBench.P10SylRProblem.B depth
                                                      (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))) →
                                            (node_R_norm_bound :
                                                ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth) (node : Node k),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@HighamBench.p10DyadicFrobNorm k
                                                      (@HighamBench.P10SylRProblem.exactSolution k (problem k hk node)))
                                                    (@HighamBench.p10DyadicFrobNorm depth
                                                      (@HighamBench.P10SylRProblem.exactSolution depth
                                                        (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                          top)))) →
                                              (node_sep_bound :
                                                  ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k depth) (node : Node k),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@HighamBench.P10SylvesterSeparation.value depth
                                                        (@HighamBench.P10SylRProblem.A depth
                                                          (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top))
                                                        (@HighamBench.P10SylRProblem.B depth
                                                          (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top))
                                                        (@HighamBench.P10SylRProblem.separation depth
                                                          (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth) top)))
                                                      (@HighamBench.P10SylvesterSeparation.value k
                                                        (@HighamBench.P10SylRProblem.A k (problem k hk node))
                                                        (@HighamBench.P10SylRProblem.B k (problem k hk node))
                                                        (@HighamBench.P10SylRProblem.separation k
                                                          (problem k hk node)))) →
                                                (base_rounding_bound :
                                                    @LE.le.{0} Real Real.instLE
                                                      (errorEnvelope
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                            (@instHMul.{0} Real Real.instMul)
                                                            (mu
                                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                                (@instHPow.{0, 0} Nat Nat
                                                                  (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                  (@instHSub.{0} Nat instSubNat) depth
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))))
                                                            epsilon)
                                                          (@HighamBench.p10DyadicFrobNorm depth
                                                            (@HighamBench.P10SylRProblem.exactSolution depth
                                                              (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                top))))
                                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                          (@instHDiv.{0} Real
                                                            (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@HighamBench.p10DyadicFrobNorm depth
                                                              (@HighamBench.P10SylRProblem.A depth
                                                                (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                  top)))
                                                            (@HighamBench.p10DyadicFrobNorm depth
                                                              (@HighamBench.P10SylRProblem.B depth
                                                                (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                  top))))
                                                          (@HighamBench.P10SylvesterSeparation.value depth
                                                            (@HighamBench.P10SylRProblem.A depth
                                                              (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                top))
                                                            (@HighamBench.P10SylRProblem.B depth
                                                              (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                top))
                                                            (@HighamBench.P10SylRProblem.separation depth
                                                              (problem depth (@le_rfl.{0} Nat Nat.instPreorder depth)
                                                                top)))))) →
                                                  HighamBench.P10SylRRun depth
```

### D005: `HighamBench.p10SylRConditionRatio`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0b08dd2885374953881d68420fa2abda34c3b4c3d066b20fb5b0a58964750b0d`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run =>
  instHDiv.hDiv
    (instHAdd.hAdd (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).A)
      (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).B))
    (HighamBench.p10SylRTopProblem run).separation.value
```

### D006: `HighamBench.p10SylRConventionalForwardScale`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fdee9dbc649d118cc3f1249d6e1ca73dc125d2327e8b8189ff36412424cfb7e8`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run =>
  instHMul.hMul
    (instHMul.hMul run.epsilon (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).exactSolution))
    (HighamBench.p10SylRConditionRatio run)
```

### D007: `HighamBench.p10SylREquation20Bound`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0a0d1f98fde426877cc14b1c00e0448523a19223b1d1f38ba4be0c25d43bb27e`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run =>
  instHMul.hMul
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 2 (instHPow.hPow (instHPow.hPow 2 depth).cast (instHAdd.hAdd 1 (Real.logb 2 3))))
          (HighamBench.p10SylRHalfMu run))
        run.epsilon)
      (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).exactSolution))
    (instHPow.hPow (HighamBench.p10SylRConditionRatio run) (instHAdd.hAdd 1 (instHPow.hPow 2 depth).log2))
```

### D008: `HighamBench.p10SylRForwardError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1c86fef33e66fecda02210be18c96095902ddb9996f08b48883f6b585cc7f097`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (problem : HighamBench.P10SylRProblem depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} problem => HighamBench.p10DyadicFrobNorm (instHSub.hSub problem.computedSolution problem.exactSolution)
```

### D009: `HighamBench.p10SylRHalfMu`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4b29f365617719a83f168e5aa3f5a9910a88d0a190e9a5925cc3671bd1ddd1b2`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run => run.mu (instHPow.hPow 2 (instHSub.hSub depth 1))
```

### D010: `HighamBench.p10SylRRecurrenceForcing`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e9d84cee557e0fccb476377237b510a1fda19a3ca37b20acf82bc8b40295b218`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run =>
  instHMul.hMul (instHDiv.hDiv run.epsilon (HighamBench.p10SylRTopProblem run).separation.value)
    (instHAdd.hAdd (instHMul.hMul 3 (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).C))
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 2 (HighamBench.p10SylRHalfMu run))
          (instHAdd.hAdd (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).A)
            (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).B)))
        (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylRTopProblem run).exactSolution)))
```

### D011: `HighamBench.p10SylRRecurrenceGrowth`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7a325b01859a04c588044611c1360f70f877c1f0e94a11e13d2ab5b895d21f8d`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run => instHAdd.hAdd 4 (instHMul.hMul 2 (HighamBench.p10SylRConditionRatio run))
```

### D012: `HighamBench.p10SylRTopProblem`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `302c0b4a8765ec2f03b6fcf3f5b75f61abe77a20d1a39814ff130079e140b7f1`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → HighamBench.P10SylRProblem depth
```

Fully explicit type:

```lean
{depth : Nat} → (run : HighamBench.P10SylRRun depth) → HighamBench.P10SylRProblem depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} run => run.problem depth ⋯ run.top
```

### D013: `HighamBench.p10SylvesterForcing._proof_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `c2128dca62968615e359a6325c7f1616277ba7b25371bfb81b5d200ad4169f10`

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

### D014: `HighamBench.p10SylvesterGrowth._proof_2`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `b67429a01e375c9b3726bce26639b2ea8b2f6da939ade8cab4f6be469b7fd880`

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

### D015: `HighamBench.P10DyadicIndex`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5579808af03478c8ea64b0039d02d9651c6195ed1dd636f574bd650a81e6321b`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun x =>
  Nat.brecOn x fun x f =>
    HighamBench.P10DyadicIndex.match_1 (fun x => Nat.below x → Type) x (fun _ x => Fin 1) (fun depth x => Sum x.1 x.1) f
```

### D016: `HighamBench.P10DyadicMatrix`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1f52e33adf37c2286d307d213c9a5a517dee0d82cdbf1467738eeec4036d9cf6`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(depth : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun depth => Matrix (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
```

### D017: `HighamBench.P10SylRLevelCertificate`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `cf238c51a6c8e8cabd350907185bdf933756c076c886d7f6240b0734ce663a2c`

Type:

```lean
{depth : Nat} →
  Real →
    Real →
      Real →
        Real →
          Real →
            Real →
              Real →
                Real →
                  HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) →
                    HighamBench.P10SylRProblem depth →
                      HighamBench.P10SylRProblem depth →
                        HighamBench.P10SylRProblem depth → HighamBench.P10SylRProblem depth → Prop
```

Fully explicit type:

```lean
{depth : Nat} →
  (epsilon muHalf smallerError globalANorm globalBNorm globalCNorm globalRNorm globalSep : Real) →
    (parent :
        HighamBench.P10SylRProblem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (child21 child11 child22 child12 : HighamBench.P10SylRProblem depth) → Prop
```

### D018: `HighamBench.P10SylRProblem`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `642d3b93b7fec573ddf23ba02aabf877bcf89efaa2c210f7649a1ad5502a7f5c`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(depth : Nat) → Type
```

### D019: `HighamBench.P10SylRProblem.A`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8d98d1d28373487e4492f1b29b915635394a7f34eabe823a503b0f73c7b9cc9d`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.1
```

### D020: `HighamBench.P10SylRProblem.B`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `06fa02166d52390c43c90643c1d11dc9f07c9e622b53e00126dfc5f108cda72a`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.2
```

### D021: `HighamBench.P10SylRProblem.C`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f6c3ae4fe1acf2b799f5c700fda52a2fc18ae857967bed22544933fd9caae48f`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.3
```

### D022: `HighamBench.P10SylRProblem.computedSolution`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `02f3f679fe9f5f0627f1287f6b27d0571255a4fec946c63ff40d4e6f7deafc35`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.5
```

### D023: `HighamBench.P10SylRProblem.exactSolution`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `35431d7b6b5707f5f3bb34aecc6be6720cc3e786e1642ec08b82a029bec9ac6c`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.4
```

### D024: `HighamBench.P10SylRProblem.separation`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2f920f8e7715e93816f3682ab1db648bc6055b3a75f8c35ad920fd9e90456c37`

Type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRProblem depth) → HighamBench.P10SylvesterSeparation self.A self.B
```

Fully explicit type:

```lean
{depth : Nat} →
  (self : HighamBench.P10SylRProblem depth) →
    @HighamBench.P10SylvesterSeparation depth (@HighamBench.P10SylRProblem.A depth self)
      (@HighamBench.P10SylRProblem.B depth self)
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.7
```

### D025: `HighamBench.P10SylRRun.epsilon`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2de93953b3cb5664a55c54a290ce4b94d2ef5f4904f3c67bec0aa8318affb118`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.1
```

### D026: `HighamBench.P10SylRRun.mu`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9fc0f9e6413d42fbc86a98a7945b5180b4e07cd0e1f460d6d8177e2cdda5a766`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Nat → Real
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.4
```

### D027: `HighamBench.P10SylRRun.problem`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `628b59bad45f0801e6d05ac96c5188d4055de60e4e163dd2db3c3554242277ac`

Type:

```lean
{depth : Nat} →
  (self : HighamBench.P10SylRRun depth) → (k : Nat) → instLENat.le k depth → self.Node k → HighamBench.P10SylRProblem k
```

Fully explicit type:

```lean
{depth : Nat} →
  (self : HighamBench.P10SylRRun depth) →
    (k : Nat) →
      @LE.le.{0} Nat instLENat k depth → @HighamBench.P10SylRRun.Node depth self k → HighamBench.P10SylRProblem k
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.14
```

### D028: `HighamBench.P10SylRRun.top`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `368368df69486f1bf1221eddd3ded4e695a7beff456ae185b48af5abd72d3e26`

Type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → self.Node depth
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → @HighamBench.P10SylRRun.Node depth self depth
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.13
```

### D029: `HighamBench.P10SylvesterSeparation.value`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `775abbcadbbcbecaf55289e8186b34f96a0fd0c874a1831936333173b718007e`

Type:

```lean
{depth : Nat} → {A B : HighamBench.P10DyadicMatrix depth} → HighamBench.P10SylvesterSeparation A B → Real
```

Fully explicit type:

```lean
{depth : Nat} →
  {A B : HighamBench.P10DyadicMatrix depth} → (self : @HighamBench.P10SylvesterSeparation depth A B) → Real
```

Definition body (one-level semantic boundary):

```lean
fun depth A B self => self.1
```

### D030: `HighamBench.p10DyadicFrobNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a00a5081d1601d2e48548411686f2c24e2cbf3cc2da3e1549f9e78d14332c41c`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix depth → Real
```

Fully explicit type:

```lean
{depth : Nat} → (A : HighamBench.P10DyadicMatrix depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A => Matrix.frobeniusNormedRing.norm A
```

### D031: `HighamBench.p10SylvesterGrowth._proof_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `cf84cab1ce903e624601ece5316ee2528afd6cf1b755e7954d9ca7611a53f9e5`

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

### D032: `HighamBench.P10DyadicIndex.match_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `21fca3a47cded8cf37222de937232ca09cf5f64c810f59cdc4c9f03998e300f8`

Type:

```lean
(motive : Nat → Sort u_1) → (x : Nat) → (Unit → motive 0) → ((depth : Nat) → motive depth.succ) → motive x
```

Fully explicit type:

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (a : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (depth : Nat) → motive (Nat.succ depth)) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 Unit.unit) fun n => h_2 n
```

### D033: `HighamBench.P10SylRLevelCertificate.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `218993f18c9b96f4fd41a5eeb0d835783d7b66c2d967cf498912725b7a07764f`

Type:

```lean
∀ {depth : Nat} {epsilon muHalf smallerError globalANorm globalBNorm globalCNorm globalRNorm globalSep : Real}
  {parent : HighamBench.P10SylRProblem (instHAdd.hAdd depth 1)}
  {child21 child11 child22 child12 : HighamBench.P10SylRProblem depth},
  Eq (HighamBench.p10DyadicBlock21 parent.A) 0 →
    Eq (HighamBench.p10DyadicBlock21 parent.B) 0 →
      Eq child21.A (HighamBench.p10DyadicBlock22 parent.A) →
        Eq child21.B (HighamBench.p10DyadicBlock11 parent.B) →
          Eq child21.C (HighamBench.p10DyadicBlock21 parent.C) →
            Eq child21.exactSolution (HighamBench.p10DyadicBlock21 parent.exactSolution) →
              Eq child11.A (HighamBench.p10DyadicBlock11 parent.A) →
                Eq child11.B (HighamBench.p10DyadicBlock11 parent.B) →
                  Eq child22.A (HighamBench.p10DyadicBlock22 parent.A) →
                    Eq child22.B (HighamBench.p10DyadicBlock22 parent.B) →
                      Eq child12.A (HighamBench.p10DyadicBlock11 parent.A) →
                        Eq child12.B (HighamBench.p10DyadicBlock22 parent.B) →
                          Eq (HighamBench.p10DyadicBlock21 parent.computedSolution) child21.computedSolution →
                            Eq (HighamBench.p10DyadicBlock11 parent.computedSolution) child11.computedSolution →
                              Eq (HighamBench.p10DyadicBlock22 parent.computedSolution) child22.computedSolution →
                                Eq (HighamBench.p10DyadicBlock12 parent.computedSolution) child12.computedSolution →
                                  Eq
                                      (HighamBench.p10SylvesterAction (HighamBench.p10DyadicBlock22 parent.A)
                                        (HighamBench.p10DyadicBlock11 parent.B)
                                        (HighamBench.p10DyadicBlock21 parent.exactSolution))
                                      (Matrix.neg.neg (HighamBench.p10DyadicBlock21 parent.C)) →
                                    Eq
                                        (HighamBench.p10SylvesterAction (HighamBench.p10DyadicBlock11 parent.A)
                                          (HighamBench.p10DyadicBlock11 parent.B)
                                          (HighamBench.p10DyadicBlock11 parent.exactSolution))
                                        (Matrix.neg.neg (HighamBench.p10SylRExactRhs11 parent)) →
                                      Eq
                                          (HighamBench.p10SylvesterAction (HighamBench.p10DyadicBlock22 parent.A)
                                            (HighamBench.p10DyadicBlock22 parent.B)
                                            (HighamBench.p10DyadicBlock22 parent.exactSolution))
                                          (Matrix.neg.neg (HighamBench.p10SylRExactRhs22 parent)) →
                                        Eq
                                            (HighamBench.p10SylvesterAction (HighamBench.p10DyadicBlock11 parent.A)
                                              (HighamBench.p10DyadicBlock22 parent.B)
                                              (HighamBench.p10DyadicBlock12 parent.exactSolution))
                                            (Matrix.neg.neg (HighamBench.p10SylRExactRhs12 parent)) →
                                          Real.instLE.le
                                              (HighamBench.p10DyadicFrobNorm
                                                (instHSub.hSub child11.C (HighamBench.p10SylRExactRhs11 parent)))
                                              (instHAdd.hAdd
                                                (instHAdd.hAdd
                                                  (instHMul.hMul epsilon
                                                    (HighamBench.p10DyadicFrobNorm
                                                      (HighamBench.p10DyadicBlock11 parent.C)))
                                                  (instHMul.hMul
                                                    (HighamBench.p10DyadicFrobNorm
                                                      (HighamBench.p10DyadicBlock12 parent.A))
                                                    (HighamBench.p10SylRBlockError21 parent child21)))
                                                (instHMul.hMul
                                                  (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                    (HighamBench.p10DyadicFrobNorm
                                                      (HighamBench.p10DyadicBlock12 parent.A)))
                                                  (HighamBench.p10DyadicFrobNorm
                                                    (HighamBench.p10DyadicBlock21 parent.exactSolution)))) →
                                            Real.instLE.le
                                                (HighamBench.p10DyadicFrobNorm
                                                  (instHSub.hSub child22.C (HighamBench.p10SylRExactRhs22 parent)))
                                                (instHAdd.hAdd
                                                  (instHAdd.hAdd
                                                    (instHMul.hMul epsilon
                                                      (HighamBench.p10DyadicFrobNorm
                                                        (HighamBench.p10DyadicBlock22 parent.C)))
                                                    (instHMul.hMul
                                                      (HighamBench.p10DyadicFrobNorm
                                                        (HighamBench.p10DyadicBlock12 parent.B))
                                                      (HighamBench.p10SylRBlockError21 parent child21)))
                                                  (instHMul.hMul
                                                    (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                      (HighamBench.p10DyadicFrobNorm
                                                        (HighamBench.p10DyadicBlock12 parent.B)))
                                                    (HighamBench.p10DyadicFrobNorm
                                                      (HighamBench.p10DyadicBlock21 parent.exactSolution)))) →
                                              Real.instLE.le
                                                  (HighamBench.p10DyadicFrobNorm
                                                    (instHSub.hSub child12.C (HighamBench.p10SylRExactRhs12 parent)))
                                                  (instHAdd.hAdd
                                                    (instHAdd.hAdd
                                                      (instHAdd.hAdd
                                                        (instHAdd.hAdd
                                                          (instHMul.hMul epsilon
                                                            (HighamBench.p10DyadicFrobNorm
                                                              (HighamBench.p10DyadicBlock12 parent.C)))
                                                          (instHMul.hMul
                                                            (HighamBench.p10DyadicFrobNorm
                                                              (HighamBench.p10DyadicBlock12 parent.B))
                                                            (HighamBench.p10SylRBlockError11 parent child11)))
                                                        (instHMul.hMul
                                                          (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                            (HighamBench.p10DyadicFrobNorm
                                                              (HighamBench.p10DyadicBlock12 parent.B)))
                                                          (HighamBench.p10DyadicFrobNorm
                                                            (HighamBench.p10DyadicBlock11 parent.exactSolution))))
                                                      (instHMul.hMul
                                                        (HighamBench.p10DyadicFrobNorm
                                                          (HighamBench.p10DyadicBlock12 parent.A))
                                                        (HighamBench.p10SylRBlockError22 parent child22)))
                                                    (instHMul.hMul
                                                      (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                        (HighamBench.p10DyadicFrobNorm
                                                          (HighamBench.p10DyadicBlock12 parent.A)))
                                                      (HighamBench.p10DyadicFrobNorm
                                                        (HighamBench.p10DyadicBlock22 parent.exactSolution)))) →
                                                Real.instLE.le (HighamBench.p10SylRForwardError parent)
                                                    (instHAdd.hAdd
                                                      (instHAdd.hAdd
                                                        (instHAdd.hAdd (HighamBench.p10SylRBlockError21 parent child21)
                                                          (HighamBench.p10SylRBlockError11 parent child11))
                                                        (HighamBench.p10SylRBlockError22 parent child22))
                                                      (HighamBench.p10SylRBlockError12 parent child12)) →
                                                  Real.instLE.le (HighamBench.p10SylRBlockError21 parent child21)
                                                      smallerError →
                                                    Real.instLE.le (HighamBench.p10SylRBlockError11 parent child11)
                                                        (instHAdd.hAdd smallerError
                                                          (instHDiv.hDiv
                                                            (instHAdd.hAdd
                                                              (instHAdd.hAdd (instHMul.hMul epsilon globalCNorm)
                                                                (instHMul.hMul globalANorm smallerError))
                                                              (instHMul.hMul
                                                                (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                                  globalANorm)
                                                                globalRNorm))
                                                            globalSep)) →
                                                      Real.instLE.le (HighamBench.p10SylRBlockError22 parent child22)
                                                          (instHAdd.hAdd smallerError
                                                            (instHDiv.hDiv
                                                              (instHAdd.hAdd
                                                                (instHAdd.hAdd (instHMul.hMul epsilon globalCNorm)
                                                                  (instHMul.hMul globalBNorm smallerError))
                                                                (instHMul.hMul
                                                                  (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                                    globalBNorm)
                                                                  globalRNorm))
                                                              globalSep)) →
                                                        Real.instLE.le (HighamBench.p10SylRBlockError12 parent child12)
                                                            (instHAdd.hAdd smallerError
                                                              (instHDiv.hDiv
                                                                (instHAdd.hAdd
                                                                  (instHAdd.hAdd (instHMul.hMul epsilon globalCNorm)
                                                                    (instHMul.hMul
                                                                      (instHAdd.hAdd globalANorm globalBNorm)
                                                                      smallerError))
                                                                  (instHMul.hMul
                                                                    (instHMul.hMul (instHMul.hMul muHalf epsilon)
                                                                      (instHAdd.hAdd globalANorm globalBNorm))
                                                                    globalRNorm))
                                                                globalSep)) →
                                                          HighamBench.P10SylRLevelCertificate epsilon muHalf
                                                            smallerError globalANorm globalBNorm globalCNorm globalRNorm
                                                            globalSep parent child21 child11 child22 child12
```

Fully explicit type:

```lean
∀ {depth : Nat} {epsilon muHalf smallerError globalANorm globalBNorm globalCNorm globalRNorm globalSep : Real}
  {parent :
    HighamBench.P10SylRProblem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {child21 child11 child22 child12 : HighamBench.P10SylRProblem depth}
  (parent_A21_zero :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock21 depth
        (@HighamBench.P10SylRProblem.A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@OfNat.ofNat.{0} (HighamBench.P10DyadicMatrix depth) (nat_lit 0)
        (@Zero.toOfNat0.{0} (HighamBench.P10DyadicMatrix depth)
          (@Matrix.zero.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
            Real.instZero))))
  (parent_B21_zero :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock21 depth
        (@HighamBench.P10SylRProblem.B
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@OfNat.ofNat.{0} (HighamBench.P10DyadicMatrix depth) (nat_lit 0)
        (@Zero.toOfNat0.{0} (HighamBench.P10DyadicMatrix depth)
          (@Matrix.zero.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
            Real.instZero))))
  (child21_A :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.A depth child21)
      (@HighamBench.p10DyadicBlock22 depth
        (@HighamBench.P10SylRProblem.A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child21_B :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.B depth child21)
      (@HighamBench.p10DyadicBlock11 depth
        (@HighamBench.P10SylRProblem.B
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child21_C :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.C depth child21)
      (@HighamBench.p10DyadicBlock21 depth
        (@HighamBench.P10SylRProblem.C
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child21_exact :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.exactSolution depth child21)
      (@HighamBench.p10DyadicBlock21 depth
        (@HighamBench.P10SylRProblem.exactSolution
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child11_A :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.A depth child11)
      (@HighamBench.p10DyadicBlock11 depth
        (@HighamBench.P10SylRProblem.A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child11_B :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.B depth child11)
      (@HighamBench.p10DyadicBlock11 depth
        (@HighamBench.P10SylRProblem.B
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child22_A :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.A depth child22)
      (@HighamBench.p10DyadicBlock22 depth
        (@HighamBench.P10SylRProblem.A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child22_B :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.B depth child22)
      (@HighamBench.p10DyadicBlock22 depth
        (@HighamBench.P10SylRProblem.B
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child12_A :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.A depth child12)
      (@HighamBench.p10DyadicBlock11 depth
        (@HighamBench.P10SylRProblem.A
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (child12_B :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.P10SylRProblem.B depth child12)
      (@HighamBench.p10DyadicBlock22 depth
        (@HighamBench.P10SylRProblem.B
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent)))
  (computed_21 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock21 depth
        (@HighamBench.P10SylRProblem.computedSolution
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@HighamBench.P10SylRProblem.computedSolution depth child21))
  (computed_11 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock11 depth
        (@HighamBench.P10SylRProblem.computedSolution
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@HighamBench.P10SylRProblem.computedSolution depth child11))
  (computed_22 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock22 depth
        (@HighamBench.P10SylRProblem.computedSolution
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@HighamBench.P10SylRProblem.computedSolution depth child22))
  (computed_12 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10DyadicBlock12 depth
        (@HighamBench.P10SylRProblem.computedSolution
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          parent))
      (@HighamBench.P10SylRProblem.computedSolution depth child12))
  (exact_block_21 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10SylvesterAction depth
        (@HighamBench.p10DyadicBlock22 depth
          (@HighamBench.P10SylRProblem.A
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock11 depth
          (@HighamBench.P10SylRProblem.B
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock21 depth
          (@HighamBench.P10SylRProblem.exactSolution
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent)))
      (@Neg.neg.{0} (HighamBench.P10DyadicMatrix depth)
        (@Matrix.neg.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real Real.instNeg)
        (@HighamBench.p10DyadicBlock21 depth
          (@HighamBench.P10SylRProblem.C
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))))
  (exact_block_11 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10SylvesterAction depth
        (@HighamBench.p10DyadicBlock11 depth
          (@HighamBench.P10SylRProblem.A
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock11 depth
          (@HighamBench.P10SylRProblem.B
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock11 depth
          (@HighamBench.P10SylRProblem.exactSolution
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent)))
      (@Neg.neg.{0} (HighamBench.P10DyadicMatrix depth)
        (@Matrix.neg.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real Real.instNeg)
        (@HighamBench.p10SylRExactRhs11 depth parent)))
  (exact_block_22 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10SylvesterAction depth
        (@HighamBench.p10DyadicBlock22 depth
          (@HighamBench.P10SylRProblem.A
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock22 depth
          (@HighamBench.P10SylRProblem.B
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock22 depth
          (@HighamBench.P10SylRProblem.exactSolution
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent)))
      (@Neg.neg.{0} (HighamBench.P10DyadicMatrix depth)
        (@Matrix.neg.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real Real.instNeg)
        (@HighamBench.p10SylRExactRhs22 depth parent)))
  (exact_block_12 :
    @Eq.{1} (HighamBench.P10DyadicMatrix depth)
      (@HighamBench.p10SylvesterAction depth
        (@HighamBench.p10DyadicBlock11 depth
          (@HighamBench.P10SylRProblem.A
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock22 depth
          (@HighamBench.P10SylRProblem.B
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent))
        (@HighamBench.p10DyadicBlock12 depth
          (@HighamBench.P10SylRProblem.exactSolution
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            parent)))
      (@Neg.neg.{0} (HighamBench.P10DyadicMatrix depth)
        (@Matrix.neg.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real Real.instNeg)
        (@HighamBench.p10SylRExactRhs12 depth parent)))
  (rhs11_first_order_error :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p10DyadicFrobNorm depth
        (@HSub.hSub.{0, 0, 0} (HighamBench.P10DyadicMatrix depth) (HighamBench.P10DyadicMatrix depth)
          (HighamBench.P10DyadicMatrix depth)
          (@instHSub.{0} (HighamBench.P10DyadicMatrix depth)
            (@Matrix.sub.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
              Real.instSub))
          (@HighamBench.P10SylRProblem.C depth child11) (@HighamBench.p10SylRExactRhs11 depth parent)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock11 depth
                (@HighamBench.P10SylRProblem.C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent)))
            (@HighamBench.p10SylRBlockError21 depth parent child21)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent))))
          (@HighamBench.p10DyadicFrobNorm depth
            (@HighamBench.p10DyadicBlock21 depth
              (@HighamBench.P10SylRProblem.exactSolution
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                parent))))))
  (rhs22_first_order_error :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p10DyadicFrobNorm depth
        (@HSub.hSub.{0, 0, 0} (HighamBench.P10DyadicMatrix depth) (HighamBench.P10DyadicMatrix depth)
          (HighamBench.P10DyadicMatrix depth)
          (@instHSub.{0} (HighamBench.P10DyadicMatrix depth)
            (@Matrix.sub.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
              Real.instSub))
          (@HighamBench.P10SylRProblem.C depth child22) (@HighamBench.p10SylRExactRhs22 depth parent)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock22 depth
                (@HighamBench.P10SylRProblem.C
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.B
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent)))
            (@HighamBench.p10SylRBlockError21 depth parent child21)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.B
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent))))
          (@HighamBench.p10DyadicFrobNorm depth
            (@HighamBench.p10DyadicBlock21 depth
              (@HighamBench.P10SylRProblem.exactSolution
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                parent))))))
  (rhs12_first_order_error :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p10DyadicFrobNorm depth
        (@HSub.hSub.{0, 0, 0} (HighamBench.P10DyadicMatrix depth) (HighamBench.P10DyadicMatrix depth)
          (HighamBench.P10DyadicMatrix depth)
          (@instHSub.{0} (HighamBench.P10DyadicMatrix depth)
            (@Matrix.sub.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
              Real.instSub))
          (@HighamBench.P10SylRProblem.C depth child12) (@HighamBench.p10SylRExactRhs12 depth parent)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                (@HighamBench.p10DyadicFrobNorm depth
                  (@HighamBench.p10DyadicBlock12 depth
                    (@HighamBench.P10SylRProblem.C
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      parent))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.p10DyadicFrobNorm depth
                  (@HighamBench.p10DyadicBlock12 depth
                    (@HighamBench.P10SylRProblem.B
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      parent)))
                (@HighamBench.p10SylRBlockError11 depth parent child11)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon)
                (@HighamBench.p10DyadicFrobNorm depth
                  (@HighamBench.p10DyadicBlock12 depth
                    (@HighamBench.P10SylRProblem.B
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      parent))))
              (@HighamBench.p10DyadicFrobNorm depth
                (@HighamBench.p10DyadicBlock11 depth
                  (@HighamBench.P10SylRProblem.exactSolution
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    parent)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent)))
            (@HighamBench.p10SylRBlockError22 depth parent child22)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon)
            (@HighamBench.p10DyadicFrobNorm depth
              (@HighamBench.p10DyadicBlock12 depth
                (@HighamBench.P10SylRProblem.A
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  parent))))
          (@HighamBench.p10DyadicFrobNorm depth
            (@HighamBench.p10DyadicBlock22 depth
              (@HighamBench.P10SylRProblem.exactSolution
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                parent))))))
  (assembled_error_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p10SylRForwardError
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        parent)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HighamBench.p10SylRBlockError21 depth parent child21)
            (@HighamBench.p10SylRBlockError11 depth parent child11))
          (@HighamBench.p10SylRBlockError22 depth parent child22))
        (@HighamBench.p10SylRBlockError12 depth parent child12)))
  (child21_first_order_error :
    @LE.le.{0} Real Real.instLE (@HighamBench.p10SylRBlockError21 depth parent child21) smallerError)
  (child11_first_order_error :
    @LE.le.{0} Real Real.instLE (@HighamBench.p10SylRBlockError11 depth parent child11)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) smallerError
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon globalCNorm)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) globalANorm smallerError))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon) globalANorm)
              globalRNorm))
          globalSep)))
  (child22_first_order_error :
    @LE.le.{0} Real Real.instLE (@HighamBench.p10SylRBlockError22 depth parent child22)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) smallerError
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon globalCNorm)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) globalBNorm smallerError))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon) globalBNorm)
              globalRNorm))
          globalSep)))
  (child12_first_order_error :
    @LE.le.{0} Real Real.instLE (@HighamBench.p10SylRBlockError12 depth parent child12)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) smallerError
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon globalCNorm)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) globalANorm globalBNorm)
                smallerError))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muHalf epsilon)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) globalANorm globalBNorm))
              globalRNorm))
          globalSep))),
  @HighamBench.P10SylRLevelCertificate depth epsilon muHalf smallerError globalANorm globalBNorm globalCNorm globalRNorm
    globalSep parent child21 child11 child22 child12
```

### D034: `HighamBench.P10SylRProblem.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `faec15120d7f1926f7a35a3a80dda23858b75464eb6319148e7400746e16033e`

Type:

```lean
{depth : Nat} →
  (A B C exactSolution : HighamBench.P10DyadicMatrix depth) →
    HighamBench.P10DyadicMatrix depth →
      Eq (HighamBench.p10SylvesterAction A B exactSolution) (Matrix.neg.neg C) →
        HighamBench.P10SylvesterSeparation A B → HighamBench.P10SylRProblem depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (A B C exactSolution computedSolution : HighamBench.P10DyadicMatrix depth) →
    (exact_equation :
        @Eq.{1} (HighamBench.P10DyadicMatrix depth) (@HighamBench.p10SylvesterAction depth A B exactSolution)
          (@Neg.neg.{0} (HighamBench.P10DyadicMatrix depth)
            (@Matrix.neg.{0, 0, 0} (HighamBench.P10DyadicIndex depth) (HighamBench.P10DyadicIndex depth) Real
              Real.instNeg)
            C)) →
      (separation : @HighamBench.P10SylvesterSeparation depth A B) → HighamBench.P10SylRProblem depth
```

### D035: `HighamBench.P10SylRRun.Node`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `92beb3161926a3f7cf8a628a4ace2ba8d8911af7699ba20747c196d77ff81a19`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRRun depth → Nat → Type
```

Fully explicit type:

```lean
{depth : Nat} → (self : HighamBench.P10SylRRun depth) → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun depth self => self.12
```

### D036: `HighamBench.P10SylvesterSeparation`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `35b586ed1c058651e08003f3c611d782aa466b797c6fee609fcdec5e2b3b4c48`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix depth → HighamBench.P10DyadicMatrix depth → Type
```

Fully explicit type:

```lean
{depth : Nat} → (A B : HighamBench.P10DyadicMatrix depth) → Type
```

### D037: `HighamBench.p10DyadicIndexDecidableEq`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `6540a7db5a0344938948e514686739948c2744edfb4e1d9bd1de9d53293ca05a`

Type:

```lean
(depth : Nat) → DecidableEq (HighamBench.P10DyadicIndex depth)
```

Fully explicit type:

```lean
(depth : Nat) → DecidableEq.{1} (HighamBench.P10DyadicIndex depth)
```

Definition body (one-level semantic boundary):

```lean
fun depth => Nat.recAux (id inferInstance) (fun depth ih => id inferInstance) depth
```

### D038: `HighamBench.p10DyadicIndexFintype`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f99d4a3bfe23c0fcb745db86b44194a09f54f790689b1176b900a8c5fd204cda`

Type:

```lean
(depth : Nat) → Fintype (HighamBench.P10DyadicIndex depth)
```

Fully explicit type:

```lean
(depth : Nat) → Fintype.{0} (HighamBench.P10DyadicIndex depth)
```

Definition body (one-level semantic boundary):

```lean
fun depth => Nat.recAux (id inferInstance) (fun depth ih => id inferInstance) depth
```

### D039: `HighamBench.P10SylvesterSeparation.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `ebb1fb1737062e5698f146f941223bed77a0a898d832793fc545f0e5682a6539`

Type:

```lean
{depth : Nat} →
  {A B : HighamBench.P10DyadicMatrix depth} →
    (value : Real) →
      Real.instLT.lt 0 value →
        (∀ (X : HighamBench.P10DyadicMatrix depth),
            Real.instLE.le (instHMul.hMul value (HighamBench.p10DyadicFrobNorm X))
              (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylvesterAction A B X))) →
          (Exists fun X =>
              And (Eq (HighamBench.p10DyadicFrobNorm X) 1)
                (Eq (HighamBench.p10DyadicFrobNorm (HighamBench.p10SylvesterAction A B X)) value)) →
            HighamBench.P10SylvesterSeparation A B
```

Fully explicit type:

```lean
{depth : Nat} →
  {A B : HighamBench.P10DyadicMatrix depth} →
    (value : Real) →
      (value_pos :
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            value) →
        (lower_bound :
            ∀ (X : HighamBench.P10DyadicMatrix depth),
              @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) value
                  (@HighamBench.p10DyadicFrobNorm depth X))
                (@HighamBench.p10DyadicFrobNorm depth (@HighamBench.p10SylvesterAction depth A B X))) →
          (attained :
              @Exists.{1} (HighamBench.P10DyadicMatrix depth) fun (X : HighamBench.P10DyadicMatrix depth) =>
                And
                  (@Eq.{1} Real (@HighamBench.p10DyadicFrobNorm depth X)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (@Eq.{1} Real (@HighamBench.p10DyadicFrobNorm depth (@HighamBench.p10SylvesterAction depth A B X))
                    value)) →
            @HighamBench.P10SylvesterSeparation depth A B
```

### D040: `HighamBench.p10DyadicBlock11`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `23fc2273720fa3e6ff769aa105dfbe1e4fdcc0a74d3c256f417e752011adb91e`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (A :
      HighamBench.P10DyadicMatrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A => Matrix.toBlocks₁₁ A
```

### D041: `HighamBench.p10DyadicBlock12`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `84ec58c283eb7dd624c5b7a540ecd5aa4cf85aa033b8aed1b5a140b829aed541`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (A :
      HighamBench.P10DyadicMatrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A => Matrix.toBlocks₁₂ A
```

### D042: `HighamBench.p10DyadicBlock21`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b7242445929a78c2949acb678d55442e38a34bae5d90617a5cb306812dc81a67`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (A :
      HighamBench.P10DyadicMatrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A => Matrix.toBlocks₂₁ A
```

### D043: `HighamBench.p10DyadicBlock22`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d0397a4b2ae96bcb539cc75d98e6554cc85da003c8079480ef3ee200a06b39ac`

Type:

```lean
{depth : Nat} → HighamBench.P10DyadicMatrix (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (A :
      HighamBench.P10DyadicMatrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A => Matrix.toBlocks₂₂ A
```

### D044: `HighamBench.p10SylRBlockError11`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f34f96075277e0c90a60da7802d6fb3b11cd07160120cc3cf7078b1562e9254c`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10SylRProblem depth → Real
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (child : HighamBench.P10SylRProblem depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent child =>
  HighamBench.p10DyadicFrobNorm
    (instHSub.hSub child.computedSolution (HighamBench.p10DyadicBlock11 parent.exactSolution))
```

### D045: `HighamBench.p10SylRBlockError12`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `fb6f699c9166cb7d38c188b1f940353239385b99e66d323482191e9585f16f7d`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10SylRProblem depth → Real
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (child : HighamBench.P10SylRProblem depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent child =>
  HighamBench.p10DyadicFrobNorm
    (instHSub.hSub child.computedSolution (HighamBench.p10DyadicBlock12 parent.exactSolution))
```

### D046: `HighamBench.p10SylRBlockError21`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `03782148889f68a0dc31c260aeb21201f71a6c9af5378560ddfdcd5ce298f454`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10SylRProblem depth → Real
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (child : HighamBench.P10SylRProblem depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent child =>
  HighamBench.p10DyadicFrobNorm
    (instHSub.hSub child.computedSolution (HighamBench.p10DyadicBlock21 parent.exactSolution))
```

### D047: `HighamBench.p10SylRBlockError22`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f091c768f86ad70832916c2bad266b56d6c0db4c03f2deacddb7d043efe5cc30`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10SylRProblem depth → Real
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    (child : HighamBench.P10SylRProblem depth) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent child =>
  HighamBench.p10DyadicFrobNorm
    (instHSub.hSub child.computedSolution (HighamBench.p10DyadicBlock22 parent.exactSolution))
```

### D048: `HighamBench.p10SylRExactRhs11`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `efc1b19e54f6dca00243f7464b8afb014850e2358e03c902ee411e42481565e1`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent =>
  instHAdd.hAdd (HighamBench.p10DyadicBlock11 parent.C)
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p10DyadicBlock12 parent.A)
      (HighamBench.p10DyadicBlock21 parent.exactSolution))
```

### D049: `HighamBench.p10SylRExactRhs12`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e64849ff70d914a924066e99ea7c84f56d49bfa2d7d57a26e674fb953015a14d`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent =>
  instHAdd.hAdd
    (instHSub.hSub (HighamBench.p10DyadicBlock12 parent.C)
      (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p10DyadicBlock11 parent.exactSolution)
        (HighamBench.p10DyadicBlock12 parent.B)))
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p10DyadicBlock12 parent.A)
      (HighamBench.p10DyadicBlock22 parent.exactSolution))
```

### D050: `HighamBench.p10SylRExactRhs22`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a7b99fe71d4c0f9984b029252f51c191bc5769e9fc94c976dccb944fc4c891d3`

Type:

```lean
{depth : Nat} → HighamBench.P10SylRProblem (instHAdd.hAdd depth 1) → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} →
  (parent :
      HighamBench.P10SylRProblem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) depth
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} parent =>
  instHSub.hSub (HighamBench.p10DyadicBlock22 parent.C)
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p10DyadicBlock21 parent.exactSolution)
      (HighamBench.p10DyadicBlock12 parent.B))
```

### D051: `HighamBench.p10SylvesterAction`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `8c348dc16de2b022e2d74f4e85bbf0d5d88ff0b2925a8e5dc44d84423ac7fe46`

Type:

```lean
{depth : Nat} →
  HighamBench.P10DyadicMatrix depth →
    HighamBench.P10DyadicMatrix depth → HighamBench.P10DyadicMatrix depth → HighamBench.P10DyadicMatrix depth
```

Fully explicit type:

```lean
{depth : Nat} → (A B X : HighamBench.P10DyadicMatrix depth) → HighamBench.P10DyadicMatrix depth
```

Definition body (one-level semantic boundary):

```lean
fun {depth} A B X =>
  instHSub.hSub (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A X)
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul X B)
```

### D052: `Nat`

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

### D053: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D054: `Eq`

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

### D055: `HAdd.hAdd`

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

### D056: `HMul.hMul`

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

### D057: `HPow.hPow`

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

### D058: `LE.le`

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

### D059: `LT.lt`

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

### D060: `Monoid.toNatPow`

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

### D061: `Nat.cast`

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

### D062: `Nat.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `de0cbde8dd75c1a0c6d5d08b9cfa1cd5908aeb874409a1c880c9c9616deb1709`

Type:

```lean
Monoid Nat
```

Fully explicit type:

```lean
Monoid.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D063: `Nat.log2`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Log2`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `fc74c7a58f40702a0685ed3d7334d3aa752161a2cbccae9d1db5d328dc5f25c5`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n =>
  Nat.rec (motive := fun x => Nat → Nat) (fun x => 0) (fun x ih n => Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n)) n n
```

### D064: `OfNat.ofNat`

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

### D065: `One.toOfNat1`

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

### D066: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D067: `Real.instAdd`

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

### D068: `Real.instLE`

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

### D069: `Real.instMonoid`

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

### D070: `Real.instMul`

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

### D071: `Real.instNatCast`

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

### D072: `Real.instOne`

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

### D073: `Real.instPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d7348547260a6fa37dab6a95efbf0e3e5560a074d2443d0cb606f21bce228fe0`

Type:

```lean
Pow Real Real
```

Fully explicit type:

```lean
Pow.{0, 0} Real Real
```

Definition body (one-level semantic boundary):

```lean
{ pow := Real.rpow }
```

### D074: `Real.logb`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Log.Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4b9329114a77424f72f09d29513a791b03cc9f40f0e4f28ede0cde8746638366`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(b x : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b x => instHDiv.hDiv (Real.log x) (Real.log b)
```

### D075: `instAddNat`

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

### D076: `instHAdd`

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

### D077: `instHMul`

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

### D078: `instHPow`

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

### D079: `instLTNat`

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

### D080: `instOfNatAtLeastTwo`

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

### D081: `instOfNatNat`

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

### D082: `DivInvMonoid.toDiv`

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

### D083: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D084: `HDiv.hDiv`

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

### D085: `HSub.hSub`

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

### D086: `Iff.mpr`

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

### D087: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f9a0c1f5b41c8d9a8658798c73b295495f6dfbf0bd7d081817aec4f598bbfc46`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub α] → Sub (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub.{v} α] → Sub.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Sub α] => Pi.instSub
```

### D088: `Monotone`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Monotone.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `504d2068b5b4f5d618a181313cc376a05deb04ee0ca24df32deaea8ae6037e1d`

Type:

```lean
{α : Type u} → {β : Type v} → [Preorder α] → [Preorder β] → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → [Preorder.{u} α] → [Preorder.{v} β] → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Preorder α] [inst_1 : Preorder β] f => ∀ ⦃a b : α⦄, inst.le a b → inst_1.le (f a) (f b)
```

### D089: `Nat.AtLeastTwo`

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

### D090: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Fully explicit type:

```lean
Preorder.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D091: `Nat.le_of_lt`

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

### D092: `Nat.succ`

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

### D093: `Nat.succ_le_iff`

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

### D094: `Real.instDivInvMonoid`

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

### D095: `Real.instLT`

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

### D096: `Real.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D097: `Real.instSub`

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

### D098: `Real.instZero`

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

### D099: `Zero.toOfNat0`

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

### D100: `instHDiv`

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

### D101: `instHSub`

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

### D102: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D103: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D104: `le_rfl`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `6c7575f2a6e8e313921f1056be4884262ead03ee5de7fe2832f63c92d9c8c7e1`

Type:

```lean
∀ {α : Type u_1} [inst : Preorder α] {a : α}, inst.le a a
```

Fully explicit type:

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] {a : α}, @LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a a
```

### D105: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D106: `Matrix`

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

### D107: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`

Type:

```lean
{m : Type u_3} → {α : Type u_5} → [Fintype m] → [RCLike α] → [DecidableEq m] → NormedRing (Matrix m m α)
```

Fully explicit type:

```lean
{m : Type u_3} →
  {α : Type u_5} →
    [Fintype.{u_3} m] →
      [RCLike.{u_5} α] → [DecidableEq.{u_3 + 1} m] → NormedRing.{max u_5 u_3} (Matrix.{u_3, u_3, u_5} m m α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {α} [Fintype m] [RCLike α] [DecidableEq m] =>
  let __src := Matrix.frobeniusSeminormedAddCommGroup;
  let __src_1 := Matrix.instRing;
  { toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := ⋯, toMul := __src_1.toMul, left_distrib := ⋯,
    right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, toOne := __src_1.toOne, one_mul := ⋯,
    mul_one := ⋯, toNatCast := __src_1.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯, npow := __src_1.npow,
    npow_zero := ⋯, npow_succ := ⋯, toNeg := __src.toNeg, toSub := __src.toSub, sub_eq_add_neg := ⋯,
    zsmul := __src.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    toIntCast := __src_1.toIntCast, intCast_ofNat := ⋯, intCast_negSucc := ⋯,
    toPseudoMetricSpace := __src.toPseudoMetricSpace, eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D108: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D109: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D110: `Norm.norm`

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

### D111: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`

Type:

```lean
{α : Type u_5} → [self : NormedRing α] → Norm α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : NormedRing.{u_5} α] → Norm.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NormedRing α] => self.1
```

### D112: `Real.instRCLike`

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

### D113: `Sum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `b918d4b75e8964578622cc8220c8e47d62bd100bdf794f538778ce95c76f70c6`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D114: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D115: `DecidableEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D116: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D117: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D118: `Matrix.neg`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1d4a0647aeb637effb2c6c25b5dbf60fa226065a3bcaf43028e168bc24a216b2`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Neg α] → Neg (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Neg.{v} α] → Neg.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Neg α] => Pi.instNeg
```

### D119: `Matrix.zero`

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

### D120: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D121: `Nat.recAux`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `77f23cb7cf264c6bc2fff40d98328186c84469d67c63c1c65d0c9963f0addd47`

Type:

```lean
{motive : Nat → Sort u} → motive 0 → ((n : Nat) → motive n → motive (instHAdd.hAdd n 1)) → (t : Nat) → motive t
```

Fully explicit type:

```lean
{motive : Nat → Sort u} →
  (zero : motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    (succ :
        (n : Nat) →
          motive n →
            motive
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (t : Nat) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} zero succ t => Nat.rec zero succ t
```

### D122: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Neg.{u} α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D123: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Fully explicit type:

```lean
Neg.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D124: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Fully explicit type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D125: `id`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `dbf7c9f75c53aa3b4f811b7fd8038f2d2ab775571e37341e9514361b972c4868`

Type:

```lean
{α : Sort u} → α → α
```

Fully explicit type:

```lean
{α : Sort u} → (a : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} a => a
```

### D126: `inferInstance`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a035e8579f88a0c5ce0a542c50396cd8f34aa652df8abeec2eb80c43a343b97b`

Type:

```lean
{α : Sort u} → [i : α] → α
```

Fully explicit type:

```lean
{α : Sort u} → [i : α] → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [i : α] => i
```

### D127: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D128: `instDecidableEqSum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D129: `instFintypeSum`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Sum`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D130: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D131: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `8eecda35a630fe4097c6149154c07645e87eaf089a78dde5ca01f180806c2a40`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} → [Fintype m] → [Mul α] → [AddCommMonoid α] → HMul (Matrix l m α) (Matrix m n α) (Matrix l n α)
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} →
        [Fintype.{u_2} m] →
          [Mul.{v} α] →
            [AddCommMonoid.{v} α] →
              HMul.{max (max v u_2) u_1, max (max v u_3) u_2, max (max v u_3) u_1} (Matrix.{u_1, u_2, v} l m α)
                (Matrix.{u_2, u_3, v} m n α) (Matrix.{u_1, u_3, v} l n α)
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {α} [Fintype m] [Mul α] [AddCommMonoid α] =>
  { hMul := fun M N i k => dotProduct (fun j => M i j) fun j => N j k }
```

### D132: `Matrix.toBlocks₁₁`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Block`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `eb27e635f4afb18683da62903a5f25326d821e95be4e9b29076e98a0037f07e8`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} → {n : Type u_3} → {o : Type u_4} → {α : Type u_12} → Matrix (Sum n o) (Sum l m) α → Matrix n l α
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {o : Type u_4} →
        {α : Type u_12} →
          (M : Matrix.{max u_4 u_3, max u_2 u_1, u_12} (Sum.{u_3, u_4} n o) (Sum.{u_1, u_2} l m) α) →
            Matrix.{u_3, u_1, u_12} n l α
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {o} {α} M => EquivLike.toFunLike.coe Matrix.of fun i j => M (Sum.inl i) (Sum.inl j)
```

### D133: `Matrix.toBlocks₁₂`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Block`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `c545aa5e71443e80d6537ea3a37763af463f90cbe56ccc8950e13b61c71fdda5`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} → {n : Type u_3} → {o : Type u_4} → {α : Type u_12} → Matrix (Sum n o) (Sum l m) α → Matrix n m α
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {o : Type u_4} →
        {α : Type u_12} →
          (M : Matrix.{max u_4 u_3, max u_2 u_1, u_12} (Sum.{u_3, u_4} n o) (Sum.{u_1, u_2} l m) α) →
            Matrix.{u_3, u_2, u_12} n m α
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {o} {α} M => EquivLike.toFunLike.coe Matrix.of fun i j => M (Sum.inl i) (Sum.inr j)
```

### D134: `Matrix.toBlocks₂₁`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Block`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `17fde03ccce1c854ae5786b1a625fcf08057b3b922a856e6cff6ec7cc9448bc2`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} → {n : Type u_3} → {o : Type u_4} → {α : Type u_12} → Matrix (Sum n o) (Sum l m) α → Matrix o l α
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {o : Type u_4} →
        {α : Type u_12} →
          (M : Matrix.{max u_4 u_3, max u_2 u_1, u_12} (Sum.{u_3, u_4} n o) (Sum.{u_1, u_2} l m) α) →
            Matrix.{u_4, u_1, u_12} o l α
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {o} {α} M => EquivLike.toFunLike.coe Matrix.of fun i j => M (Sum.inr i) (Sum.inl j)
```

### D135: `Matrix.toBlocks₂₂`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Block`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `a35ebf4a29f53ea6c707dab819dd89d60c5ed93c8c60f81bb55ba0cf86bd1953`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} → {n : Type u_3} → {o : Type u_4} → {α : Type u_12} → Matrix (Sum n o) (Sum l m) α → Matrix o m α
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {o : Type u_4} →
        {α : Type u_12} →
          (M : Matrix.{max u_4 u_3, max u_2 u_1, u_12} (Sum.{u_3, u_4} n o) (Sum.{u_1, u_2} l m) α) →
            Matrix.{u_4, u_2, u_12} o m α
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {o} {α} M => EquivLike.toFunLike.coe Matrix.of fun i j => M (Sum.inr i) (Sum.inr j)
```

### D136: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### `HighamBench.P10Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P10Definitions.lean`
SHA-256: `f49e4d8aea5940088440cc81e8a85365243730ec35689bf1f3bb9434c1e80cc6`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- A square real matrix in the native finite `Matrix` representation. -/
abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite square matrix multiplication. -/
noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

/-- The Frobenius norm, written explicitly to keep the public statement lightweight. -/
noncomputable def p10FrobNorm {n : ℕ} (A : P10Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- An otherwise unspecified matrix norm with the consistency properties used
in the paper's normwise product analysis. -/
structure P10ConsistentMatrixNorm (n : ℕ) where
  value : P10Matrix n → ℝ
  value_nonneg : ∀ A, 0 ≤ value A
  value_eq_zero_iff : ∀ A, value A = 0 ↔ A = 0
  value_smul : ∀ (c : ℝ) A, value (c • A) = |c| * value A
  value_add_le : ∀ A B, value (A + B) ≤ value A + value B
  value_matMul_le : ∀ A B,
    value (p10MatMul n A B) ≤ value A * value B

/-- One stable matrix-product computation with inherited operand errors.  The
cross term and the local higher-order remainder are retained in the execution
model but excluded from its first-order error. -/
structure P10FirstOrderProductRun (n : ℕ) where
  dimension_pos : 0 < n
  matrixNorm : P10ConsistentMatrixNorm n
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mu : ℕ → ℝ
  mu_nonneg : ∀ k, 0 ≤ mu k
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ k,
    mu k ≤ muGrowthConstant * (k : ℝ) ^ muDegree
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10Matrix n
  rightPerturbation : P10Matrix n
  computedProduct : P10Matrix n
  localFirstOrderError : P10Matrix n
  higherOrderRemainder : P10Matrix n
  leftInheritedError : ℝ
  rightInheritedError : ℝ
  leftInheritedError_nonneg : 0 ≤ leftInheritedError
  rightInheritedError_nonneg : 0 ≤ rightInheritedError
  higherOrderCoeff : ℝ
  higherOrderCoeff_nonneg : 0 ≤ higherOrderCoeff
  computed_product :
    computedProduct =
      p10MatMul n
          (exactLeft + leftPerturbation)
          (exactRight + rightPerturbation) +
        localFirstOrderError + higherOrderRemainder
  local_error_bound :
    matrixNorm.value localFirstOrderError ≤
      mu n * epsilon * matrixNorm.value exactLeft * matrixNorm.value exactRight
  left_inherited_error_bound :
    matrixNorm.value leftPerturbation ≤ leftInheritedError
  right_inherited_error_bound :
    matrixNorm.value rightPerturbation ≤ rightInheritedError
  higher_order_bound :
    matrixNorm.value higherOrderRemainder ≤ higherOrderCoeff * epsilon ^ 2

/-- The realized product error with the inherited cross term and the local
higher-order remainder removed, exactly as required by first-order analysis. -/
noncomputable def p10FirstOrderProductError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  run.computedProduct - p10MatMul n run.exactLeft run.exactRight -
      p10MatMul n run.leftPerturbation run.rightPerturbation -
    run.higherOrderRemainder

/-- The three first-order contributions printed in equation (8). -/
noncomputable def p10FirstOrderProductErrorBudget {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
      run.matrixNorm.value run.exactRight +
    (run.matrixNorm.value run.exactLeft * run.rightInheritedError +
      run.leftInheritedError * run.matrixNorm.value run.exactRight)

/-- The inherited-right error matrix produced to first order by multiplying
the right operand perturbation on the left by the exact left operand. -/
noncomputable def p10InheritedRightError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.exactLeft run.rightPerturbation

/-- Equation (8)'s local stable-multiplication contribution. -/
noncomputable def p10LocalProductErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
    run.matrixNorm.value run.exactRight

/-- Equation (8)'s inherited-right contribution `||A||*err(B,n)`. -/
noncomputable def p10InheritedRightErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.matrixNorm.value run.exactLeft * run.rightInheritedError

/-- Equation (8)'s inherited-left contribution `err(A,n)*||B||`. -/
noncomputable def p10InheritedLeftErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.leftInheritedError * run.matrixNorm.value run.exactRight

/-- The selected inherited-right term, including both its propagated matrix
bound and its exact additive position in equation (8)'s first-order budget. -/
def P10InheritedRightEquation8Term {n : ℕ}
    (run : P10FirstOrderProductRun n) : Prop :=
  run.matrixNorm.value (p10InheritedRightError run) ≤
      p10InheritedRightErrorContribution run ∧
    p10FirstOrderProductErrorBudget run =
      p10LocalProductErrorContribution run +
        (p10InheritedRightErrorContribution run +
          p10InheritedLeftErrorContribution run)

/-- The one-level amplification factor in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterGrowth {n : ℕ}
    (A B : P10Matrix n) (sep : ℝ) : ℝ :=
  4 + 2 * (p10FrobNorm A + p10FrobNorm B) / sep

/-- The one-level forcing term in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterForcing {n : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ) : ℝ :=
  epsilon / sep *
    (3 * p10FrobNorm C +
      2 * mu * (p10FrobNorm A + p10FrobNorm B) * p10FrobNorm R)

/-! ## Recursive Sylvester solver model -/

/-- Recursive index set for a matrix of dimension exactly `2^depth`. -/
def P10DyadicIndex : ℕ → Type
  | 0 => Fin 1
  | depth + 1 => P10DyadicIndex depth ⊕ P10DyadicIndex depth

noncomputable instance p10DyadicIndexFintype (depth : ℕ) :
    Fintype (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : Fintype (P10DyadicIndex depth) := ih
      infer_instance

noncomputable instance p10DyadicIndexDecidableEq (depth : ℕ) :
    DecidableEq (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : DecidableEq (P10DyadicIndex depth) := ih
      infer_instance

/-- A square real matrix of power-of-two dimension. -/
abbrev P10DyadicMatrix (depth : ℕ) :=
  Matrix (P10DyadicIndex depth) (P10DyadicIndex depth) ℝ

/-- The Frobenius norm used in the paper's definition of `sep(A,B)`. -/
noncomputable def p10DyadicFrobNorm {depth : ℕ}
    (A : P10DyadicMatrix depth) : ℝ :=
  letI : NormedRing (P10DyadicMatrix depth) :=
    Matrix.frobeniusNormedRing
  ‖A‖

noncomputable def p10DyadicBlock11 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₁ A

noncomputable def p10DyadicBlock12 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₂ A

noncomputable def p10DyadicBlock21 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₁ A

noncomputable def p10DyadicBlock22 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₂ A

/-- The Sylvester operator `X ↦ A*X-X*B`. -/
noncomputable def p10SylvesterAction {depth : ℕ}
    (A B X : P10DyadicMatrix depth) : P10DyadicMatrix depth :=
  A * X - X * B

/-- Certificate for the Frobenius variational definition of `sep(A,B)`. -/
structure P10SylvesterSeparation {depth : ℕ}
    (A B : P10DyadicMatrix depth) where
  value : ℝ
  value_pos : 0 < value
  lower_bound : ∀ X,
    value * p10DyadicFrobNorm X ≤
      p10DyadicFrobNorm (p10SylvesterAction A B X)
  attained : ∃ X,
    p10DyadicFrobNorm X = 1 ∧
      p10DyadicFrobNorm (p10SylvesterAction A B X) = value

/-- One exact Sylvester problem and its first-order computed SylR result.
Real-valued states model the standard finite regime: exceptional values and
the higher-order terms suppressed by the paper are outside this certificate. -/
structure P10SylRProblem (depth : ℕ) where
  A : P10DyadicMatrix depth
  B : P10DyadicMatrix depth
  C : P10DyadicMatrix depth
  exactSolution : P10DyadicMatrix depth
  computedSolution : P10DyadicMatrix depth
  exact_equation :
    p10SylvesterAction A B exactSolution = -C
  separation : P10SylvesterSeparation A B

/-- Absolute Frobenius forward error in the paper's first-order model. -/
noncomputable def p10SylRForwardError {depth : ℕ}
    (problem : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm (problem.computedSolution - problem.exactSolution)

noncomputable def p10SylRExactRhs11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock11 parent.C +
    p10DyadicBlock12 parent.A * p10DyadicBlock21 parent.exactSolution

noncomputable def p10SylRExactRhs22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock22 parent.C -
    p10DyadicBlock21 parent.exactSolution * p10DyadicBlock12 parent.B

noncomputable def p10SylRExactRhs12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock12 parent.C -
      p10DyadicBlock11 parent.exactSolution * p10DyadicBlock12 parent.B +
    p10DyadicBlock12 parent.A * p10DyadicBlock22 parent.exactSolution

/-- Total error in a computed child block, measured against the corresponding
block of the exact parent solution.  This includes rounded-RHS error. -/
noncomputable def p10SylRBlockError21 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock21 parent.exactSolution)

noncomputable def p10SylRBlockError11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock11 parent.exactSolution)

noncomputable def p10SylRBlockError22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock22 parent.exactSolution)

noncomputable def p10SylRBlockError12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock12 parent.exactSolution)

/-- One non-base SylR node and the four page-86 first-order block estimates.
The fields expose the solve order `R21`, `R11`, `R22`, `R12`, exact right-hand
sides (15)--(18), product model (8), and separation inequality (19). -/
structure P10SylRLevelCertificate {depth : ℕ}
    (epsilon muHalf smallerError globalANorm globalBNorm globalCNorm
      globalRNorm globalSep : ℝ)
    (parent : P10SylRProblem (depth + 1))
    (child21 child11 child22 child12 : P10SylRProblem depth) where
  parent_A21_zero : p10DyadicBlock21 parent.A = 0
  parent_B21_zero : p10DyadicBlock21 parent.B = 0
  child21_A : child21.A = p10DyadicBlock22 parent.A
  child21_B : child21.B = p10DyadicBlock11 parent.B
  child21_C : child21.C = p10DyadicBlock21 parent.C
  child21_exact :
    child21.exactSolution = p10DyadicBlock21 parent.exactSolution
  child11_A : child11.A = p10DyadicBlock11 parent.A
  child11_B : child11.B = p10DyadicBlock11 parent.B
  child22_A : child22.A = p10DyadicBlock22 parent.A
  child22_B : child22.B = p10DyadicBlock22 parent.B
  child12_A : child12.A = p10DyadicBlock11 parent.A
  child12_B : child12.B = p10DyadicBlock22 parent.B
  computed_21 :
    p10DyadicBlock21 parent.computedSolution = child21.computedSolution
  computed_11 :
    p10DyadicBlock11 parent.computedSolution = child11.computedSolution
  computed_22 :
    p10DyadicBlock22 parent.computedSolution = child22.computedSolution
  computed_12 :
    p10DyadicBlock12 parent.computedSolution = child12.computedSolution
  exact_block_21 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock21 parent.exactSolution) =
      -p10DyadicBlock21 parent.C
  exact_block_11 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock11 parent.exactSolution) =
      -p10SylRExactRhs11 parent
  exact_block_22 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock22 parent.exactSolution) =
      -p10SylRExactRhs22 parent
  exact_block_12 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock12 parent.exactSolution) =
      -p10SylRExactRhs12 parent
  rhs11_first_order_error :
    p10DyadicFrobNorm (child11.C - p10SylRExactRhs11 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock11 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs22_first_order_error :
    p10DyadicFrobNorm (child22.C - p10SylRExactRhs22 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock22 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs12_first_order_error :
    p10DyadicFrobNorm (child12.C - p10SylRExactRhs12 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock12 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError11 parent child11 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock11 parent.exactSolution) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError22 parent child22 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock22 parent.exactSolution)
  assembled_error_bound :
    p10SylRForwardError parent ≤
      p10SylRBlockError21 parent child21 +
        p10SylRBlockError11 parent child11 +
        p10SylRBlockError22 parent child22 +
        p10SylRBlockError12 parent child12
  child21_first_order_error :
    p10SylRBlockError21 parent child21 ≤ smallerError
  child11_first_order_error :
    p10SylRBlockError11 parent child11 ≤
      smallerError +
        (epsilon * globalCNorm + globalANorm * smallerError +
            muHalf * epsilon * globalANorm * globalRNorm) / globalSep
  child22_first_order_error :
    p10SylRBlockError22 parent child22 ≤
      smallerError +
        (epsilon * globalCNorm + globalBNorm * smallerError +
            muHalf * epsilon * globalBNorm * globalRNorm) / globalSep
  child12_first_order_error :
    p10SylRBlockError12 parent child12 ≤
      smallerError +
        (epsilon * globalCNorm +
            (globalANorm + globalBNorm) * smallerError +
            muHalf * epsilon * (globalANorm + globalBNorm) * globalRNorm) /
          globalSep

/-- Complete proof-carrying SylR recursion family for dimensions `2^k` up to
the requested depth. `errorEnvelope k` is the attained worst first-order error
among the dimension-`2^k` calls, including rounded right-hand sides. -/
structure P10SylRRun (depth : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  mu_mono : Monotone mu
  mu_ge_one : ∀ n, 0 < n → 1 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  Node : ℕ → Type
  top : Node depth
  problem : ∀ k, k ≤ depth → Node k → P10SylRProblem k
  errorEnvelope : ℕ → ℝ
  errorEnvelope_upper : ∀ k (hk : k ≤ depth) (node : Node k),
    p10SylRForwardError (problem k hk node) ≤ errorEnvelope k
  errorEnvelope_attained : ∀ k (hk : k ≤ depth),
    ∃ node : Node k,
      p10SylRForwardError (problem k hk node) = errorEnvelope k
  child21 : ∀ k, k < depth → Node (k + 1) → Node k
  child11 : ∀ k, k < depth → Node (k + 1) → Node k
  child22 : ∀ k, k < depth → Node (k + 1) → Node k
  child12 : ∀ k, k < depth → Node (k + 1) → Node k
  level : ∀ k (hk : k < depth) (node : Node (k + 1)),
    P10SylRLevelCertificate
      epsilon (mu (2 ^ (depth - 1))) (errorEnvelope k)
      (p10DyadicFrobNorm (problem depth le_rfl top).A)
      (p10DyadicFrobNorm (problem depth le_rfl top).B)
      (p10DyadicFrobNorm (problem depth le_rfl top).C)
      (p10DyadicFrobNorm (problem depth le_rfl top).exactSolution)
      (problem depth le_rfl top).separation.value
      (problem (k + 1) (Nat.succ_le_iff.mpr hk) node)
      (problem k (Nat.le_of_lt hk) (child21 k hk node))
      (problem k (Nat.le_of_lt hk) (child11 k hk node))
      (problem k (Nat.le_of_lt hk) (child22 k hk node))
      (problem k (Nat.le_of_lt hk) (child12 k hk node))
  node_A_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).A ≤
      p10DyadicFrobNorm (problem depth le_rfl top).A
  node_B_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).B ≤
      p10DyadicFrobNorm (problem depth le_rfl top).B
  node_R_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).exactSolution ≤
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution
  node_sep_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    (problem depth le_rfl top).separation.value ≤
      (problem k hk node).separation.value
  base_rounding_bound : errorEnvelope 0 ≤
    mu (2 ^ (depth - 1)) * epsilon *
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution *
      ((p10DyadicFrobNorm (problem depth le_rfl top).A +
          p10DyadicFrobNorm (problem depth le_rfl top).B) /
        (problem depth le_rfl top).separation.value)

noncomputable def p10SylRTopProblem {depth : ℕ}
    (run : P10SylRRun depth) : P10SylRProblem depth :=
  run.problem depth le_rfl run.top

noncomputable def p10SylRConditionRatio {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  (p10DyadicFrobNorm (p10SylRTopProblem run).A +
      p10DyadicFrobNorm (p10SylRTopProblem run).B) /
    (p10SylRTopProblem run).separation.value

noncomputable def p10SylRHalfMu {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.mu (2 ^ (depth - 1))

/-- Conventional first-order forward-error scale used in the comparison
following equation (20). -/
noncomputable def p10SylRConventionalForwardScale {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon * p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    p10SylRConditionRatio run

/-- Exact multiplier in the recurrence preceding equation (20). -/
noncomputable def p10SylRRecurrenceGrowth {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  4 + 2 * p10SylRConditionRatio run

/-- Exact first-order forcing term in the recurrence preceding (20). -/
noncomputable def p10SylRRecurrenceForcing {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon / (p10SylRTopProblem run).separation.value *
    (3 * p10DyadicFrobNorm (p10SylRTopProblem run).C +
      2 * p10SylRHalfMu run *
        (p10DyadicFrobNorm (p10SylRTopProblem run).A +
          p10DyadicFrobNorm (p10SylRTopProblem run).B) *
        p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution)

/-- Equation (20) with the explicit universal constant `2`; this is a finite
strengthening of the paper's unspecified big-O constant. -/
noncomputable def p10SylREquation20Bound {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
    p10SylRHalfMu run * run.epsilon *
    p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    (p10SylRConditionRatio run) ^ (1 + Nat.log2 (2 ^ depth))

/-- Finite form of the recurrence, equation (20), its conventional-error
comparison, and the logarithmic condition-number exponent. -/
def P10SylRLogarithmicallyStable {depth : ℕ}
    (run : P10SylRRun depth) : Prop :=
  (∀ k, k < depth →
      run.errorEnvelope (k + 1) ≤
        p10SylRRecurrenceGrowth run * run.errorEnvelope k +
          p10SylRRecurrenceForcing run) ∧
    p10SylRForwardError (p10SylRTopProblem run) ≤
      p10SylREquation20Bound run ∧
    p10SylREquation20Bound run =
      2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
        p10SylRHalfMu run * p10SylRConventionalForwardScale run *
        (p10SylRConditionRatio run) ^ Nat.log2 (2 ^ depth) ∧
    1 + Nat.log2 (2 ^ depth) = depth + 1

end HighamBench
```
