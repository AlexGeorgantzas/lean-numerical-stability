# Declaration dossier for P17-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p17_t2_recursive_sum_bias_condition_bound
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (hsum : p17ExactSum run.a ≠ 0) :
    |p17ExpectedRecursiveSum run - p17ExactSum run.a| /
        |p17ExactSum run.a| ≤
      p17SummationCondition run.a *
        p17Gamma m (p17UnitRoundoff (run.p + run.r))
```

## Elaborated target type

```lean
∀ {m : Nat} {Ω : Type u_1} [inst : Fintype Ω] (run : HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω),
  Ne (HighamBench.p17ExactSum run.a) 0 →
    Real.instLE.le
      (instHDiv.hDiv (abs (instHSub.hSub (HighamBench.p17ExpectedRecursiveSum run) (HighamBench.p17ExactSum run.a)))
        (abs (HighamBench.p17ExactSum run.a)))
      (instHMul.hMul (HighamBench.p17SummationCondition run.a)
        (HighamBench.p17Gamma m (HighamBench.p17UnitRoundoff (instHAdd.hAdd run.p run.r))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} {Ω : Type u_1} [inst : Fintype.{u_1} Ω]
  (run : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst)
  (hsum :
    @Ne.{1} Real
      (@HighamBench.p17ExactSum
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.P17LimitedPrecisionRecursiveSumRun.a.{u_1} m Ω inst run))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HighamBench.p17ExpectedRecursiveSum.{u_1} m Ω inst run)
          (@HighamBench.p17ExactSum
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HighamBench.P17LimitedPrecisionRecursiveSumRun.a.{u_1} m Ω inst run))))
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HighamBench.p17ExactSum
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HighamBench.P17LimitedPrecisionRecursiveSumRun.a.{u_1} m Ω inst run))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HighamBench.p17SummationCondition
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.P17LimitedPrecisionRecursiveSumRun.a.{u_1} m Ω inst run))
      (HighamBench.p17Gamma m
        (HighamBench.p17UnitRoundoff
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HighamBench.P17LimitedPrecisionRecursiveSumRun.p.{u_1} m Ω inst run)
            (@HighamBench.P17LimitedPrecisionRecursiveSumRun.r.{u_1} m Ω inst run)))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P17Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P17Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P17LimitedPrecisionRecursiveSumRun`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ace3179ccf30cf04c14ebcee55d2b8f502cdfa9f8ce0fe0e41db599a443a794b`

Type:

```lean
Nat → (Ω : Type u_1) → [Fintype Ω] → Type u_1
```

Fully explicit type:

```lean
(m : Nat) → (Ω : Type u_1) → [Fintype.{u_1} Ω] → Type u_1
```

### D002: `HighamBench.P17LimitedPrecisionRecursiveSumRun.a`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e50cfccf69dab2200459c7b74d24519fdd75a6840c847029aeb9d20f5a6bca0e`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → Fin (instHAdd.hAdd m 1) → Real
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] →
      (self : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.6
```

### D003: `HighamBench.P17LimitedPrecisionRecursiveSumRun.p`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4b1bd1650658fb1e16d1132aaeffd9eceb794491263e09494ae574b85b83e4e2`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → Nat
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] → (self : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.2
```

### D004: `HighamBench.P17LimitedPrecisionRecursiveSumRun.r`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1a1252dd1f75472f55596d2ab59186740870c583d8da51c043f12fb95ffe1038`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → Nat
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] → (self : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.3
```

### D005: `HighamBench.p17ExactSum`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `848417c7f33279dafd13c76e57c16d106352e6d30f31556f926cf1df05292c9f`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a => Finset.univ.sum fun i => a i
```

### D006: `HighamBench.p17ExpectedRecursiveSum`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `45bbb166d4419f1260709601b2a2a2e83ba179088ef6e807d7da6b2a8416cf7e`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → Real
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] → (run : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {Ω} [Fintype Ω] run =>
  HighamBench.p17Expectation run.probability fun ω => HighamBench.p17RecursiveSum run.a fun k => run.delta k ω
```

### D007: `HighamBench.p17Gamma`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b618e3f80d471499c2e719ece1298451cd8b322884851dc6e31f84efc4bffba9`

Type:

```lean
Nat → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n u => instHSub.hSub (instHPow.hPow (instHAdd.hAdd 1 u) n) 1
```

### D008: `HighamBench.p17SummationCondition`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fc08de23529c01f8faa80a18a0d4ed5a7e469e253e5a60e2f2665e0187753fd9`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a => instHDiv.hDiv (Finset.univ.sum fun i => abs (a i)) (abs (HighamBench.p17ExactSum a))
```

### D009: `HighamBench.p17UnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2e1b884518fe748bc9c633d226f6ce911dc8b29df0c965e62309ecbe8fe0c3fc`

Type:

```lean
Nat → Real
```

Fully explicit type:

```lean
(p : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun p => instHPow.hPow (1 / 2) (instHSub.hSub p 1)
```

### D010: `HighamBench.P17LimitedPrecisionRecursiveSumRun.delta`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5e28f16149b568261491969bc0508e984b4bc02e17efe5111be77b1fc848e02f`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → Fin m → Ω → Real
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] →
      (self : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) → Fin m → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.7
```

### D011: `HighamBench.P17LimitedPrecisionRecursiveSumRun.mk`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `93782331e6c436ef83cda017924420324703c857d1c60bc662f3f415eac6d837`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] →
      (probability : HighamBench.P17FiniteProbability Ω) →
        (p r : Nat) →
          instLTNat.lt 0 p →
            instLTNat.lt 0 r →
              (a : Fin (instHAdd.hAdd m 1) → Real) →
                (delta beta : Fin m → Ω → Real) →
                  (truncate : Real → Real) →
                    (∀ (k : Fin m) (ω : Ω), Real.instLE.le (abs (delta k ω)) (HighamBench.p17UnitRoundoff p)) →
                      (∀ (k : Fin m) (ω : Ω), Real.instLE.le 0 (instHAdd.hAdd 1 (delta k ω))) →
                        (∀ (k : Fin m) (ω : Ω),
                            Real.instLE.le (abs (beta k ω)) (HighamBench.p17UnitRoundoff (instHAdd.hAdd p r))) →
                          (∀ (k : Fin m) (ω : Ω),
                              Eq (truncate (HighamBench.p17RecursivePreRound a (fun j => delta j ω) k))
                                (instHMul.hMul (HighamBench.p17RecursivePreRound a (fun j => delta j ω) k)
                                  (instHAdd.hAdd 1 (beta k ω)))) →
                            (∀ (k : Fin m) (ω : Ω),
                                Eq (HighamBench.p17RecursivePreRound a (fun j => delta j ω) k) 0 → Eq (delta k ω) 0) →
                              (∀ (k : Fin m) (ω : Ω),
                                  Eq (HighamBench.p17RecursivePreRound a (fun j => delta j ω) k) 0 → Eq (beta k ω) 0) →
                                (∀ (k : Fin m), HighamBench.p17HistoryMeasurable delta k (beta k)) →
                                  (∀ (k : Fin m) (X : Ω → Real),
                                      HighamBench.p17HistoryMeasurable delta k X →
                                        Eq
                                          (HighamBench.p17Expectation probability fun ω =>
                                            instHMul.hMul (X ω) (delta k ω))
                                          (HighamBench.p17Expectation probability fun ω =>
                                            instHMul.hMul (X ω) (beta k ω))) →
                                    HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] →
      (probability : @HighamBench.P17FiniteProbability.{u_1} Ω inst) →
        (p r : Nat) →
          (p_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
            (r_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) →
              (a :
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Real) →
                (delta beta : Fin m → Ω → Real) →
                  (truncate : Real → Real) →
                    (delta_bound :
                        ∀ (k : Fin m) (ω : Ω),
                          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (delta k ω))
                            (HighamBench.p17UnitRoundoff p)) →
                      (rounding_factor_nonneg :
                          ∀ (k : Fin m) (ω : Ω),
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (delta k ω))) →
                        (beta_bound :
                            ∀ (k : Fin m) (ω : Ω),
                              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (beta k ω))
                                (HighamBench.p17UnitRoundoff
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p r))) →
                          (truncation_equation :
                              ∀ (k : Fin m) (ω : Ω),
                                @Eq.{1} Real
                                  (truncate (@HighamBench.p17RecursivePreRound m a (fun (j : Fin m) => delta j ω) k))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HighamBench.p17RecursivePreRound m a (fun (j : Fin m) => delta j ω) k)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                      (beta k ω)))) →
                            (delta_zero :
                                ∀ (k : Fin m) (ω : Ω),
                                  @Eq.{1} Real (@HighamBench.p17RecursivePreRound m a (fun (j : Fin m) => delta j ω) k)
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                    @Eq.{1} Real (delta k ω)
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                              (beta_zero :
                                  ∀ (k : Fin m) (ω : Ω),
                                    @Eq.{1} Real
                                        (@HighamBench.p17RecursivePreRound m a (fun (j : Fin m) => delta j ω) k)
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                                      @Eq.{1} Real (beta k ω)
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                (beta_history :
                                    ∀ (k : Fin m), @HighamBench.p17HistoryMeasurable.{u_1} m Ω delta k (beta k)) →
                                  (conditional_mean :
                                      ∀ (k : Fin m) (X : Ω → Real),
                                        @HighamBench.p17HistoryMeasurable.{u_1} m Ω delta k X →
                                          @Eq.{1} Real
                                            (@HighamBench.p17Expectation.{u_1} Ω inst probability fun (ω : Ω) =>
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (X ω) (delta k ω))
                                            (@HighamBench.p17Expectation.{u_1} Ω inst probability fun (ω : Ω) =>
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (X ω) (beta k ω))) →
                                    @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst
```

### D012: `HighamBench.P17LimitedPrecisionRecursiveSumRun.probability`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b0371bd5bae152cc489cceecaa14f2f1e20aa725fa021fdd17c221532b1c48b8`

Type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype Ω] → HighamBench.P17LimitedPrecisionRecursiveSumRun m Ω → HighamBench.P17FiniteProbability Ω
```

Fully explicit type:

```lean
{m : Nat} →
  {Ω : Type u_1} →
    [inst : Fintype.{u_1} Ω] →
      (self : @HighamBench.P17LimitedPrecisionRecursiveSumRun.{u_1} m Ω inst) →
        @HighamBench.P17FiniteProbability.{u_1} Ω inst
```

Definition body (one-level semantic boundary):

```lean
fun m Ω [Fintype Ω] self => self.1
```

### D013: `HighamBench.p17Expectation`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `11fae07829d61b57addb3f2e2be7e9036d8a1f8a8ef1b16838117ee6186916da`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17FiniteProbability Ω → (Ω → Real) → Real
```

Fully explicit type:

```lean
{Ω : Type u_1} → [inst : Fintype.{u_1} Ω] → (P : @HighamBench.P17FiniteProbability.{u_1} Ω inst) → (X : Ω → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [Fintype Ω] P X => Finset.univ.sum fun ω => instHMul.hMul (P.prob ω) (X ω)
```

### D014: `HighamBench.p17RecursiveSum`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `db5a2e19747e9a6d254bee6309e21c422212116f4b169ea1a3f6280382091206`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Real
```

Fully explicit type:

```lean
{m : Nat} →
  (a :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    (delta : Fin m → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta =>
  Fin.foldl m (fun acc k => instHMul.hMul (instHAdd.hAdd acc (a k.succ)) (instHAdd.hAdd 1 (delta k))) (a 0)
```

### D015: `HighamBench.p17UnitRoundoff._proof_1`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `6add6f3a805986e842859d18df685b1be0e6256f312fa0e9c6957e13f62d7365`

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

### D016: `HighamBench.P17FiniteProbability`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `cdc6900d6b44706c8faf4d7e391274862067cb6d95b1131a47b2560a766d95d3`

Type:

```lean
(Ω : Type u_1) → [Fintype Ω] → Type u_1
```

Fully explicit type:

```lean
(Ω : Type u_1) → [Fintype.{u_1} Ω] → Type u_1
```

### D017: `HighamBench.P17FiniteProbability.prob`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3636c9f4d2f36ba03c4caf5f0ddd2ad616a29ee70ad7e10bc918a28de663df17`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17FiniteProbability Ω → Ω → Real
```

Fully explicit type:

```lean
{Ω : Type u_1} → [inst : Fintype.{u_1} Ω] → (self : @HighamBench.P17FiniteProbability.{u_1} Ω inst) → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun Ω [Fintype Ω] self => self.1
```

### D018: `HighamBench.p17HistoryMeasurable`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `abb40cf56e6f17c27b1223311cf80c7107d7c0f71e4293e9c61fc91ae0ce516f`

Type:

```lean
{m : Nat} → {Ω : Type u_1} → (Fin m → Ω → Real) → Fin m → (Ω → Real) → Prop
```

Fully explicit type:

```lean
{m : Nat} → {Ω : Type u_1} → (delta : Fin m → Ω → Real) → (k : Fin m) → (X : Ω → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} {Ω} delta k X =>
  ∀ (ω₁ ω₂ : Ω), (∀ (j : Fin m), instLTNat.lt j.val k.val → Eq (delta j ω₁) (delta j ω₂)) → Eq (X ω₁) (X ω₂)
```

### D019: `HighamBench.p17RecursivePreRound`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `dae4d26f8b0f7e7b45d38512bbd65f64aabda62baf6e10c4c8970649403c3921`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} →
  (a :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    (delta : Fin m → Real) → (k : Fin m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta k => instHAdd.hAdd (HighamBench.p17RecursiveSumBefore a delta k) (a k.succ)
```

### D020: `HighamBench.p17RecursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `18694e9c1d9246eac6354d260a132cdf303f1118117c94cb9e1e005712488d03`

Type:

```lean
∀ {m : Nat}, NeZero (instHAdd.hAdd m 1)
```

Fully explicit type:

```lean
∀ {m : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D021: `HighamBench.P17FiniteProbability.mk`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `fd0a240d1fc266d3cd085bc0f6cc5d37e8496bf562c971bd11b5f95e9e7b4d90`

Type:

```lean
{Ω : Type u_1} →
  [inst : Fintype Ω] →
    (prob : Ω → Real) →
      (∀ (ω : Ω), Real.instLE.le 0 (prob ω)) →
        Eq (Finset.univ.sum fun ω => prob ω) 1 → HighamBench.P17FiniteProbability Ω
```

Fully explicit type:

```lean
{Ω : Type u_1} →
  [inst : Fintype.{u_1} Ω] →
    (prob : Ω → Real) →
      (prob_nonneg :
          ∀ (ω : Ω),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (prob ω)) →
        (prob_sum :
            @Eq.{1} Real
              (@Finset.sum.{u_1, 0} Ω Real Real.instAddCommMonoid (@Finset.univ.{u_1} Ω inst) fun (ω : Ω) => prob ω)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          @HighamBench.P17FiniteProbability.{u_1} Ω inst
```

### D022: `HighamBench.p17RecursiveSumBefore`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b0cffd1b1978ca87c8b1ea80b35b4d982b7eba4c987f85d7d535854b2eec865a`

Type:

```lean
{m : Nat} → (Fin (instHAdd.hAdd m 1) → Real) → (Fin m → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} →
  (a :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    (delta : Fin m → Real) → (k : Fin m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} a delta k =>
  Fin.foldl k.val
    (fun acc j =>
      have q := ⟨j.val, ⋯⟩;
      instHMul.hMul (instHAdd.hAdd acc (a q.succ)) (instHAdd.hAdd 1 (delta q)))
    (a 0)
```

### D023: `HighamBench.p17RecursiveSumBefore._proof_1`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `aed4abfdb1053e620927af170c3392a2edc788934a058c8727ae9f49dfacd8df`

Type:

```lean
∀ {m : Nat} (k : Fin m) (j : Fin k.val), instLTNat.lt j.val m
```

Fully explicit type:

```lean
∀ {m : Nat} (k : Fin m) (j : Fin (@Fin.val m k)), @LT.lt.{0} Nat instLTNat (@Fin.val (@Fin.val m k) j) m
```

### D024: `DivInvMonoid.toDiv`

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

### D025: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D026: `HAdd.hAdd`

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

### D027: `HDiv.hDiv`

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

### D028: `HMul.hMul`

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

### D029: `HSub.hSub`

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

### D030: `LE.le`

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

### D031: `Nat`

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

### D032: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D033: `OfNat.ofNat`

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

### D034: `Real`

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

### D035: `Real.instAddGroup`

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

### D036: `Real.instDivInvMonoid`

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

### D037: `Real.instLE`

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

### D038: `Real.instMul`

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

### D039: `Real.instSub`

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

### D040: `Real.instZero`

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

### D041: `Real.lattice`

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

### D042: `Zero.toOfNat0`

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

### D043: `abs`

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

### D044: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D045: `instHAdd`

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

### D046: `instHDiv`

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

### D047: `instHMul`

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

### D048: `instHSub`

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

### D049: `instOfNatNat`

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

### D050: `Fin`

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

### D051: `Fin.fintype`

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

### D052: `Finset.sum`

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

### D053: `Finset.univ`

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

### D054: `HPow.hPow`

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

### D055: `Monoid.toNatPow`

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

### D056: `One.toOfNat1`

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

### D057: `Real.instAdd`

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

### D058: `Real.instAddCommMonoid`

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

### D059: `Real.instMonoid`

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

### D060: `Real.instNatCast`

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

### D061: `Real.instOne`

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

### D062: `instHPow`

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

### D063: `instOfNatAtLeastTwo`

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

### D064: `instSubNat`

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

### D065: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D066: `Fin.foldl`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Fold`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5ab599c7f2f67b41cf899570d42ffbfae3263cdad61b9afc24765cd587fdf181`

Type:

```lean
{α : Sort u_1} → (n : Nat) → (α → Fin n → α) → α → α
```

Fully explicit type:

```lean
{α : Sort u_1} → (n : Nat) → (f : α → Fin n → α) → (init : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} n f init => Fin.foldl.loop✝ n f init 0
```

### D067: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8f9c302902ae8c66b3f71728ffe02994a026b562f27b9df8d4f84793e455e26b`

Type:

```lean
{n : Nat} → [NeZero n] → {i : Nat} → OfNat (Fin n) i
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n] → {i : Nat} → OfNat.{0} (Fin n) i
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] {i} => { ofNat := Fin.ofNat n i }
```

### D068: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

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
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D069: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D070: `Nat.AtLeastTwo`

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

### D071: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D072: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D073: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

Fully explicit type:

```lean
{R : Type u_1} → [Zero.{u_1} R] → (n : R) → Prop
```

### D074: `Zero.ofOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d610ee8a0a2a61b7850d6032e696e6ae93221da787dff4096e98d4122502f26d`

Type:

```lean
{α : Type u_1} → [OfNat α 0] → Zero α
```

Fully explicit type:

```lean
{α : Type u_1} → [OfNat.{u_1} α (nat_lit 0)] → Zero.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [OfNat α 0] => { zero := 0 }
```

### D075: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```
