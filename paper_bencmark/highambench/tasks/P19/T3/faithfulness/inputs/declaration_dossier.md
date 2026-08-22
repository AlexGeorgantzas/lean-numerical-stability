# Declaration dossier for P19-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t3_right_flexible_attainable_forward_error
    {n : ℕ} (semantics : P19FirstOrderSemantics)
    (choice : P19StaticSquareKappaChoice) :
    (∀ (right : P19StaticRightFamily n semantics)
        (mgs : P19MGSSelectionLaw right.family)
        (appendix : P19StaticRightAppendixCTheory choice right)
        (applicability : ∀ k : P19Theorem31Dimension n,
          p19IterationWellConditioned (right.family.iteration k) →
          (k.1 = n ∨ p19MGSNearDependence (right.family.iteration k)) →
          P19StaticRightConditions choice (right.iteration k)),
      ∃ k : P19Theorem31Dimension n,
        p19IterationWellConditioned (right.family.iteration k) ∧
          p19FirstOrderLe semantics
            (p19ForwardError right.family.system.xExact
              (right.family.iteration k).xHat)
            ((right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR)) ∧
      (∀ (flexible : P19StaticFlexibleFamily n semantics)
          (mgs : P19MGSSelectionLaw flexible.family)
          (appendix : P19StaticFlexibleAppendixDTheory choice flexible)
          (applicability : ∀ k : P19Theorem31Dimension n,
            p19IterationWellConditioned (flexible.family.iteration k) →
            (k.1 = n ∨
              p19MGSNearDependence (flexible.family.iteration k)) →
            P19StaticFlexibleConditions choice (flexible.iteration k)),
        ∃ k : P19Theorem31Dimension n,
          p19IterationWellConditioned (flexible.family.iteration k) ∧
            p19FirstOrderLe semantics
              (p19ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat)
              ((flexible.family.iteration k).dimensionFactor *
                p19StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR)) ∧
        ∀ (family : P19Theorem31Family n semantics)
          (preconditioner : P19StaticFixedRightPreconditioner family)
          (ug um ua etaR rhoAR : ℝ),
          p19StaticRightAttainableEnvelope choice preconditioner
              ug um ua etaR rhoAR =
            p19StaticFlexibleAttainableEnvelope choice preconditioner
                ug ua rhoAR +
              um * etaR *
                p19StaticRightPreconditionerKappa choice preconditioner
```

## Elaborated target type

```lean
∀ {n : Nat} (semantics : HighamBench.P19FirstOrderSemantics) (choice : HighamBench.P19StaticSquareKappaChoice),
  And
    (∀ (right : HighamBench.P19StaticRightFamily n semantics),
      HighamBench.P19MGSSelectionLaw right.family →
        ∀ (appendix : HighamBench.P19StaticRightAppendixCTheory choice right),
          (∀ (k : HighamBench.P19Theorem31Dimension n),
              HighamBench.p19IterationWellConditioned (right.family.iteration k) →
                Or (Eq k.val n) (HighamBench.p19MGSNearDependence (right.family.iteration k)) →
                  HighamBench.P19StaticRightConditions choice (right.iteration k)) →
            Exists fun k =>
              And (HighamBench.p19IterationWellConditioned (right.family.iteration k))
                (HighamBench.p19FirstOrderLe semantics
                  (HighamBench.p19ForwardError right.family.system.xExact (right.family.iteration k).xHat)
                  (instHMul.hMul (right.family.iteration k).dimensionFactor
                    (HighamBench.p19StaticRightAttainableEnvelope choice right.preconditioner
                      (right.iteration k).core.ug (right.iteration k).core.um (right.iteration k).core.ua
                      (right.iteration k).core.etaR (right.iteration k).core.rhoAR))))
    (And
      (∀ (flexible : HighamBench.P19StaticFlexibleFamily n semantics),
        HighamBench.P19MGSSelectionLaw flexible.family →
          ∀ (appendix : HighamBench.P19StaticFlexibleAppendixDTheory choice flexible),
            (∀ (k : HighamBench.P19Theorem31Dimension n),
                HighamBench.p19IterationWellConditioned (flexible.family.iteration k) →
                  Or (Eq k.val n) (HighamBench.p19MGSNearDependence (flexible.family.iteration k)) →
                    HighamBench.P19StaticFlexibleConditions choice (flexible.iteration k)) →
              Exists fun k =>
                And (HighamBench.p19IterationWellConditioned (flexible.family.iteration k))
                  (HighamBench.p19FirstOrderLe semantics
                    (HighamBench.p19ForwardError flexible.family.system.xExact (flexible.family.iteration k).xHat)
                    (instHMul.hMul (flexible.family.iteration k).dimensionFactor
                      (HighamBench.p19StaticFlexibleAttainableEnvelope choice flexible.preconditioner
                        (flexible.iteration k).core.ug (flexible.iteration k).core.ua
                        (flexible.iteration k).core.rhoAR))))
      (∀ (family : HighamBench.P19Theorem31Family n semantics)
        (preconditioner : HighamBench.P19StaticFixedRightPreconditioner family) (ug um ua etaR rhoAR : Real),
        Eq (HighamBench.p19StaticRightAttainableEnvelope choice preconditioner ug um ua etaR rhoAR)
          (instHAdd.hAdd (HighamBench.p19StaticFlexibleAttainableEnvelope choice preconditioner ug ua rhoAR)
            (instHMul.hMul (instHMul.hMul um etaR)
              (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (semantics : HighamBench.P19FirstOrderSemantics) (choice : HighamBench.P19StaticSquareKappaChoice),
  And
    (∀ (right : HighamBench.P19StaticRightFamily n semantics)
      (mgs : @HighamBench.P19MGSSelectionLaw n semantics (@HighamBench.P19StaticRightFamily.family n semantics right))
      (appendix : @HighamBench.P19StaticRightAppendixCTheory choice n semantics right)
      (applicability :
        ∀ (k : HighamBench.P19Theorem31Dimension n),
          @HighamBench.p19IterationWellConditioned n
              (@HighamBench.P19Theorem31Family.system n semantics
                (@HighamBench.P19StaticRightFamily.family n semantics right))
              semantics
              (@HighamBench.P19Theorem31Family.basisFamily n semantics
                (@HighamBench.P19StaticRightFamily.family n semantics right))
              k
              (@HighamBench.P19Theorem31Family.iteration n semantics
                (@HighamBench.P19StaticRightFamily.family n semantics right) k) →
            Or
                (@Eq.{1} Nat
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)
                  n)
                (@HighamBench.p19MGSNearDependence n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right))
                  semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right))
                  k
                  (@HighamBench.P19Theorem31Family.iteration n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right) k)) →
              @HighamBench.P19StaticRightConditions choice n semantics
                (@HighamBench.P19StaticRightFamily.family n semantics right)
                (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                (@HighamBench.P19StaticRightFamily.iteration n semantics right k)),
      @Exists.{1} (HighamBench.P19Theorem31Dimension n) fun (k : HighamBench.P19Theorem31Dimension n) =>
        And
          (@HighamBench.p19IterationWellConditioned n
            (@HighamBench.P19Theorem31Family.system n semantics
              (@HighamBench.P19StaticRightFamily.family n semantics right))
            semantics
            (@HighamBench.P19Theorem31Family.basisFamily n semantics
              (@HighamBench.P19StaticRightFamily.family n semantics right))
            k
            (@HighamBench.P19Theorem31Family.iteration n semantics
              (@HighamBench.P19StaticRightFamily.family n semantics right) k))
          (HighamBench.p19FirstOrderLe semantics
            (@HighamBench.p19ForwardError n
              (@HighamBench.P19Theorem31System.xExact n
                (@HighamBench.P19Theorem31Family.system n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)))
              (@HighamBench.P19Algorithm2Iteration.xHat n
                (@HighamBench.P19Theorem31Family.system n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right))
                semantics
                (@HighamBench.P19Theorem31Family.basisFamily n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right))
                k
                (@HighamBench.P19Theorem31Family.iteration n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right) k)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                (@HighamBench.P19Theorem31Family.system n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right))
                semantics
                (@HighamBench.P19Theorem31Family.basisFamily n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right))
                k
                (@HighamBench.P19Theorem31Family.iteration n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right) k))
              (@HighamBench.p19StaticRightAttainableEnvelope choice n semantics
                (@HighamBench.P19StaticRightFamily.family n semantics right)
                (@HighamBench.P19StaticRightFamily.preconditioner n semantics right)
                (@HighamBench.P19StaticFixedRightCore.ug n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                  (@HighamBench.P19StaticRightIteration.core n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right)
                    (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                    (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                (@HighamBench.P19StaticFixedRightCore.um n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                  (@HighamBench.P19StaticRightIteration.core n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right)
                    (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                    (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                (@HighamBench.P19StaticFixedRightCore.ua n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                  (@HighamBench.P19StaticRightIteration.core n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right)
                    (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                    (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                (@HighamBench.P19StaticFixedRightCore.etaR n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                  (@HighamBench.P19StaticRightIteration.core n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right)
                    (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                    (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics
                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                  (@HighamBench.P19StaticRightIteration.core n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right)
                    (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                    (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))))))
    (And
      (∀ (flexible : HighamBench.P19StaticFlexibleFamily n semantics)
        (mgs :
          @HighamBench.P19MGSSelectionLaw n semantics
            (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
        (appendix : @HighamBench.P19StaticFlexibleAppendixDTheory choice n semantics flexible)
        (applicability :
          ∀ (k : HighamBench.P19Theorem31Dimension n),
            @HighamBench.p19IterationWellConditioned n
                (@HighamBench.P19Theorem31Family.system n semantics
                  (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                semantics
                (@HighamBench.P19Theorem31Family.basisFamily n semantics
                  (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                k
                (@HighamBench.P19Theorem31Family.iteration n semantics
                  (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k) →
              Or
                  (@Eq.{1} Nat
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                          (@LE.le.{0} Nat instLENat k n))
                      k)
                    n)
                  (@HighamBench.p19MGSNearDependence n
                    (@HighamBench.P19Theorem31Family.system n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                    semantics
                    (@HighamBench.P19Theorem31Family.basisFamily n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                    k
                    (@HighamBench.P19Theorem31Family.iteration n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k)) →
                @HighamBench.P19StaticFlexibleConditions choice n semantics
                  (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                  (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                  (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)),
        @Exists.{1} (HighamBench.P19Theorem31Dimension n) fun (k : HighamBench.P19Theorem31Dimension n) =>
          And
            (@HighamBench.p19IterationWellConditioned n
              (@HighamBench.P19Theorem31Family.system n semantics
                (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
              semantics
              (@HighamBench.P19Theorem31Family.basisFamily n semantics
                (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
              k
              (@HighamBench.P19Theorem31Family.iteration n semantics
                (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k))
            (HighamBench.p19FirstOrderLe semantics
              (@HighamBench.p19ForwardError n
                (@HighamBench.P19Theorem31System.xExact n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)))
                (@HighamBench.P19Algorithm2Iteration.xHat n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  k
                  (@HighamBench.P19Theorem31Family.iteration n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  k
                  (@HighamBench.P19Theorem31Family.iteration n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k))
                (@HighamBench.p19StaticFlexibleAttainableEnvelope choice n semantics
                  (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                  (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible)
                  (@HighamBench.P19StaticFixedRightCore.ug n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                    (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                    (@HighamBench.P19StaticFlexibleIteration.core n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                      (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                      (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)))
                  (@HighamBench.P19StaticFixedRightCore.ua n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                    (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                    (@HighamBench.P19StaticFlexibleIteration.core n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                      (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                      (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)))
                  (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                    (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                    (@HighamBench.P19StaticFlexibleIteration.core n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                      (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                      (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)))))))
      (∀ (family : HighamBench.P19Theorem31Family n semantics)
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family)
        (ug um ua etaR rhoAR : Real),
        @Eq.{1} Real
          (@HighamBench.p19StaticRightAttainableEnvelope choice n semantics family preconditioner ug um ua etaR rhoAR)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HighamBench.p19StaticFlexibleAttainableEnvelope choice n semantics family preconditioner ug ua rhoAR)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) um etaR)
              (@HighamBench.p19StaticRightPreconditionerKappa choice n semantics family preconditioner)))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.CStarAlgebra.Matrix`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P19Algorithm2Iteration.dimensionFactor`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bd61c8f1e579e2bc426d5a08c59735f265c1098959fb615dd750676b8f5f9f9`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.1
```

### D002: `HighamBench.P19Algorithm2Iteration.xHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0f616cd1d9ce48e6eb27c83d2c4a4c2df84dd67d173d645b05f7301f1c36da83`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.25
```

### D003: `HighamBench.P19FirstOrderSemantics`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a20664f9def445da45faf4e94b9d57628f2c92d716d878ab43853aebfc279a4f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D004: `HighamBench.P19MGSSelectionLaw`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b67e2d9f04acecbc78207a030a90d981c008234f8a4032f60100150823aba8a3`

Type:

```lean
{n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19Theorem31Family n semantics → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} → (family : HighamBench.P19Theorem31Family n semantics) → Prop
```

### D005: `HighamBench.P19StaticFixedRightCore.etaR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `47cbf6557fe561ebcc11b2ad8138d2cad06a5472576e89df0c25ebac8ef3acc7`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.4
```

### D006: `HighamBench.P19StaticFixedRightCore.rhoAR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5ef09099046905e7f89b56c7b82e67aca33f15eb3fe26814f1739d54a9095a6`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.5
```

### D007: `HighamBench.P19StaticFixedRightCore.ua`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8d5598ea0fc18200212c77bf981efeff17b3c27faf56e2668f59f9fcc446beab`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.3
```

### D008: `HighamBench.P19StaticFixedRightCore.ug`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `63e66824835046c6ada5feeb04d97ba1e14722f9603c523b70680071e0edeb7b`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D009: `HighamBench.P19StaticFixedRightCore.um`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `723d957713fb9b948ab2c8ab35a5d6e925676ed148fd8cc9a7bfbfabb30ad663`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D010: `HighamBench.P19StaticFixedRightPreconditioner`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f17c181eddba4babc040bf456a51f7a5f69f8e1086de922560b0f8450c333523`

Type:

```lean
{n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19Theorem31Family n semantics → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} → (family : HighamBench.P19Theorem31Family n semantics) → Type
```

### D011: `HighamBench.P19StaticFlexibleAppendixDTheory`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `d9cc418ff1028a4124ed7c3068c4aa6943c9cbb09b11534ae2656dc3721714e3`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19StaticFlexibleFamily n semantics → Type
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      (flexible : HighamBench.P19StaticFlexibleFamily n semantics) → Type
```

### D012: `HighamBench.P19StaticFlexibleConditions`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b088b3ad9a5dbc3d18d0ab445e99c4e27fe5796c6cf391a0d6f01541af0c619d`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
          {k : HighamBench.P19Theorem31Dimension n} →
            HighamBench.P19StaticFlexibleIteration family preconditioner k → Prop
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
          {k : HighamBench.P19Theorem31Dimension n} →
            (iteration : @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k) → Prop
```

### D013: `HighamBench.P19StaticFlexibleFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a98b45ef16ccad8799958db5b7f25acbf531bee95224288ef8b372f46f37f6b8`

Type:

```lean
Nat → HighamBench.P19FirstOrderSemantics → Type
```

Fully explicit type:

```lean
(n : Nat) → (semantics : HighamBench.P19FirstOrderSemantics) → Type
```

### D014: `HighamBench.P19StaticFlexibleFamily.family`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `58cb6cc8f5fdc4bf773f32d161a5300e3e79d8c8d9f7039dface49bedee1e298`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    HighamBench.P19StaticFlexibleFamily n semantics → HighamBench.P19Theorem31Family n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticFlexibleFamily n semantics) → HighamBench.P19Theorem31Family n semantics
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D015: `HighamBench.P19StaticFlexibleFamily.iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `aa4985b27b46324f206f6c068dc073d9b9df2d0659d3cf9326b6b1b946852298`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticFlexibleFamily n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        HighamBench.P19StaticFlexibleIteration self.family self.preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticFlexibleFamily n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        @HighamBench.P19StaticFlexibleIteration n semantics
          (@HighamBench.P19StaticFlexibleFamily.family n semantics self)
          (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics self) k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D016: `HighamBench.P19StaticFlexibleFamily.preconditioner`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `09d13f46802f29fe551c017f3df082e43ff5d3166886b9ce1a1dc24707738b20`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticFlexibleFamily n semantics) → HighamBench.P19StaticFixedRightPreconditioner self.family
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticFlexibleFamily n semantics) →
      @HighamBench.P19StaticFixedRightPreconditioner n semantics
        (@HighamBench.P19StaticFlexibleFamily.family n semantics self)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D017: `HighamBench.P19StaticFlexibleIteration.core`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `27a3180ca404d5342b624333ca0fcf379eee0d103cc4cda4fac240799e5fed44`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFlexibleIteration family preconditioner k →
            HighamBench.P19StaticFixedRightCore family preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k) →
            @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D018: `HighamBench.P19StaticRightAppendixCTheory`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `997f3e55531817475668d6b087dfce3587837fe6c2063db0295a6a1a536431c6`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19StaticRightFamily n semantics → Type
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} → (right : HighamBench.P19StaticRightFamily n semantics) → Type
```

### D019: `HighamBench.P19StaticRightConditions`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `c287fe1077604f3edf20e9207d23bd329281edb3a562cd23bfc003bb77580185`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
          {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticRightIteration family preconditioner k → Prop
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
          {k : HighamBench.P19Theorem31Dimension n} →
            (iteration : @HighamBench.P19StaticRightIteration n semantics family preconditioner k) → Prop
```

### D020: `HighamBench.P19StaticRightFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4167e6ef452a48ed9662303d633bbe76cdd69fd4e7ea64d4ff0ed76b13fcd642`

Type:

```lean
Nat → HighamBench.P19FirstOrderSemantics → Type
```

Fully explicit type:

```lean
(n : Nat) → (semantics : HighamBench.P19FirstOrderSemantics) → Type
```

### D021: `HighamBench.P19StaticRightFamily.family`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `30215e7975cb776aa7dd95938d4d39ea6fae480850b13dd0944ff9c48e059077`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    HighamBench.P19StaticRightFamily n semantics → HighamBench.P19Theorem31Family n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticRightFamily n semantics) → HighamBench.P19Theorem31Family n semantics
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D022: `HighamBench.P19StaticRightFamily.iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ad047aa332a5e9a4cbb1389d7474e47a1a833569fdbf8fdb45cb42527a879890`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticRightFamily n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) → HighamBench.P19StaticRightIteration self.family self.preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticRightFamily n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        @HighamBench.P19StaticRightIteration n semantics (@HighamBench.P19StaticRightFamily.family n semantics self)
          (@HighamBench.P19StaticRightFamily.preconditioner n semantics self) k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D023: `HighamBench.P19StaticRightFamily.preconditioner`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1bb04c0d8562112a011019f7c4302812716ad78cad5e42bc728ba28284934dfc`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticRightFamily n semantics) → HighamBench.P19StaticFixedRightPreconditioner self.family
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19StaticRightFamily n semantics) →
      @HighamBench.P19StaticFixedRightPreconditioner n semantics
        (@HighamBench.P19StaticRightFamily.family n semantics self)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D024: `HighamBench.P19StaticRightIteration.core`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `21b32a833e5358eeb0920cd6801fb2d7358b31600462f005ceed16178ecc0939`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticRightIteration family preconditioner k →
            HighamBench.P19StaticFixedRightCore family preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticRightIteration n semantics family preconditioner k) →
            @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D025: `HighamBench.P19StaticSquareKappaChoice`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4a5fc3461154e3dc86d003a2aa51f5e386d2e947f4ca5ff258b33546a4650226`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D026: `HighamBench.P19Theorem31Dimension`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ba4d761a25f81cfb346c892740752ac617f111a2ec0eef599d417bd7f7d3e658`

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
fun n => Subtype fun k => And (instLTNat.lt 0 k) (instLENat.le k n)
```

### D027: `HighamBench.P19Theorem31Family`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cc83d8798f9a47a79576057c89bdc261929f89427a25b80ab5445df3cd5f82a3`

Type:

```lean
Nat → HighamBench.P19FirstOrderSemantics → Type
```

Fully explicit type:

```lean
(n : Nat) → (semantics : HighamBench.P19FirstOrderSemantics) → Type
```

### D028: `HighamBench.P19Theorem31Family.basisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `48b8971fe31959b7c84e4fa154d6726a70bcbe3b6bc2717c09056064d86842e0`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) → HighamBench.P19Theorem31BasisFamily self.system
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      @HighamBench.P19Theorem31BasisFamily n (@HighamBench.P19Theorem31Family.system n semantics self)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D029: `HighamBench.P19Theorem31Family.iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `19b31c6eb7cb832d22efb7b1839ce0bc1843824506aa8009381c2a4b584f2da2`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        HighamBench.P19Algorithm2Iteration self.system semantics self.basisFamily k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) →
      (k : HighamBench.P19Theorem31Dimension n) →
        @HighamBench.P19Algorithm2Iteration n (@HighamBench.P19Theorem31Family.system n semantics self) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics self) k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D030: `HighamBench.P19Theorem31Family.system`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f9b5cc522a99882317f849e0f893e587ce7572ee9af8b6bcf8da993caceb2a83`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    HighamBench.P19Theorem31Family n semantics → HighamBench.P19Theorem31System n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (self : HighamBench.P19Theorem31Family n semantics) → HighamBench.P19Theorem31System n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D031: `HighamBench.P19Theorem31System.xExact`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c060fd2e6cb0459f8835569f03cacb0ab0a92b86296d51c2585bb7100236edd6`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D032: `HighamBench.p19FirstOrderLe`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `35e87ffbddb5973e07dcc90dac89a3894e57974b204159105b2394786a93ec95`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Real → Prop
```

Fully explicit type:

```lean
(semantics : HighamBench.P19FirstOrderSemantics) → (lhs rhs : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D033: `HighamBench.p19ForwardError`

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

### D034: `HighamBench.p19IterationWellConditioned`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837ad167b07baa790538584ded0302c4a219440403d2a43dfcb0dfd365ded950`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  And (Real.instLE.le (instHDiv.hDiv 1 iteration.vHatSpectrum.sigmaMin) (4 / 3))
    (Real.instLE.le iteration.vHatSpectrum.sigmaMax (4 / 3))
```

### D035: `HighamBench.p19MGSNearDependence`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bebe1d1e8d8d001aa18eb0792f2f6a1ee4a0fc6ffe41d08bf7c18d43bb054680`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Prop
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (iteration : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  ∀ (phi : Real),
    Real.instLT.lt 0 phi →
      HighamBench.p19NearRankDeficient
        (HighamBench.p19Augment (fun i => instHMul.hMul (HighamBench.p19StaticExactB system i) phi)
          (HighamBench.p19StaticExactC system (basisFamily.basis k.val)))
        (instHMul.hMul (instHMul.hMul iteration.dimensionFactor (instHAdd.hAdd iteration.ug iteration.epsilonC))
          (HighamBench.p19FrobNorm
            (HighamBench.p19Augment (fun i => instHMul.hMul (HighamBench.p19StaticExactB system i) phi)
              (HighamBench.p19StaticExactC system (basisFamily.basis k.val)))))
```

### D036: `HighamBench.p19StaticFlexibleAttainableEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a2ce6acd788e00e7620e8063f4d3f8deb6c7382205d0c02ff36ebba5c4a3664d`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        HighamBench.P19StaticFixedRightPreconditioner family → Real → Real → Real → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
          (ug ua rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug ua rhoAR =>
  instHAdd.hAdd
    (instHMul.hMul (instHMul.hMul ug (HighamBench.p19StaticRightOperatorKappa choice preconditioner))
      (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19StaticSystemKappa choice family)) rhoAR)
```

### D037: `HighamBench.p19StaticRightAttainableEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7b79ed05e7373af69a09c6ba9c4c34080bc6f953bbced1c2c89e8a1c29948b43`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        HighamBench.P19StaticFixedRightPreconditioner family → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
          (ug um ua etaR rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug um ua etaR rhoAR =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHMul.hMul (instHMul.hMul ug (HighamBench.p19StaticRightOperatorKappa choice preconditioner))
        (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner))
      (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner)))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19StaticSystemKappa choice family)) rhoAR)
```

### D038: `HighamBench.p19StaticRightPreconditionerKappa`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e4133ea733ea352df5df33d675a4002acd0a62046b66db4dd5d146ea095bff82`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        HighamBench.P19StaticFixedRightPreconditioner family → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner =>
  HighamBench.p19StaticKappa choice preconditioner.MR preconditioner.MRinv
```

### D039: `HighamBench.P19Algorithm2Iteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f4879bef746a587dacfe91ab1a424bce7078d52c23f5781d3d8d85d64b2e912e`

Type:

```lean
{n : Nat} →
  (system : HighamBench.P19Theorem31System n) →
    HighamBench.P19FirstOrderSemantics →
      HighamBench.P19Theorem31BasisFamily system → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  (system : HighamBench.P19Theorem31System n) →
    (semantics : HighamBench.P19FirstOrderSemantics) →
      (basisFamily : @HighamBench.P19Theorem31BasisFamily n system) → (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D040: `HighamBench.P19Algorithm2Iteration.epsilonC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fbab99a9750c59d1a1e583743df520e7d44c5cc91bb8f953dd579b781c71de46`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.3
```

### D041: `HighamBench.P19Algorithm2Iteration.ug`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4719f7a83a03368282078d24f181cee29a7a4a469c3c34d7ae10554be584afb9`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.5
```

### D042: `HighamBench.P19Algorithm2Iteration.vHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e8833827bd3a748534cb2317f9f1b570eb9df72748910ae72b2f34cd8d63c4a3`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.13
```

### D043: `HighamBench.P19Algorithm2Iteration.vHatSpectrum`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6c6a21a70e9a127eec34be18a02b5156e7c6fd3553d869f8a57f86ef151cbc57`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : HighamBench.P19Algorithm2Iteration system semantics basisFamily k) →
            HighamBench.P19SingularValueData self.vHat
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            @HighamBench.P19SingularValueData n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.P19Algorithm2Iteration.vHat n system semantics basisFamily k self)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.28
```

### D044: `HighamBench.P19FirstOrderSemantics.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a249dfd13648ccda052f87210f4319154f5c284c54962efd48e215532eae0d6b`

Type:

```lean
(Real → Prop) → (secondOrder : Real → Prop) → secondOrder 0 → HighamBench.P19FirstOrderSemantics
```

Fully explicit type:

```lean
(small secondOrder : Real → Prop) →
  (zero_secondOrder : secondOrder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    HighamBench.P19FirstOrderSemantics
```

### D045: `HighamBench.P19FirstOrderSemantics.secondOrder`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ddf671e3d58393ee511310b987314be908539f15467ae3cf73e66807e455755c`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P19FirstOrderSemantics) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D046: `HighamBench.P19MGSSelectionLaw.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1497d719068f8d8895ba60bd603e9d3c8c9016560b59759954bd461a979d201f`

Type:

```lean
∀ {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics} {family : HighamBench.P19Theorem31Family n semantics},
  HighamBench.p19IterationWellConditioned (family.iteration ⟨1, ⋯⟩) →
    (∀ (k : Nat) (hkpos : instLTNat.lt 0 k) (hklt : instLTNat.lt k n),
        let current := ⟨k, ⋯⟩;
        let next := ⟨instHAdd.hAdd k 1, ⋯⟩;
        Not (HighamBench.p19IterationWellConditioned (family.iteration next)) →
          HighamBench.p19MGSNearDependence (family.iteration current)) →
      HighamBench.P19MGSSelectionLaw family
```

Fully explicit type:

```lean
∀ {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics} {family : HighamBench.P19Theorem31Family n semantics}
  (first_dimension_good :
    @HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
      (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
      (@Subtype.mk.{1} Nat
        (fun (k : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@And.intro
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) Nat.zero_lt_one
          (@HighamBench.P19Theorem31System.dimension_pos n
            (@HighamBench.P19Theorem31Family.system n semantics family))))
      (@HighamBench.P19Theorem31Family.iteration n semantics family
        (@Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@And.intro
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n) Nat.zero_lt_one
            (@HighamBench.P19Theorem31System.dimension_pos n
              (@HighamBench.P19Theorem31Family.system n semantics family))))))
  (loss_implies_near_dependence :
    ∀ (k : Nat) (hkpos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
      (hklt : @LT.lt.{0} Nat instLTNat k n),
      let current : HighamBench.P19Theorem31Dimension n :=
        @Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          k
          (@And.intro (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n) hkpos (@Nat.le_of_lt k n hklt));
      let next : HighamBench.P19Theorem31Dimension n :=
        @Subtype.mk.{1} Nat
          (fun (k : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (@LE.le.{0} Nat instLENat k n))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@And.intro
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              n)
            (Nat.succ_pos k)
            (@Iff.mpr (@LE.le.{0} Nat instLENat (Nat.succ k) n) (@LT.lt.{0} Nat instLTNat k n) (@Nat.succ_le_iff k n)
              hklt));
      Not
          (@HighamBench.p19IterationWellConditioned n (@HighamBench.P19Theorem31Family.system n semantics family)
            semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) next
            (@HighamBench.P19Theorem31Family.iteration n semantics family next)) →
        @HighamBench.p19MGSNearDependence n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) current
          (@HighamBench.P19Theorem31Family.iteration n semantics family current)),
  @HighamBench.P19MGSSelectionLaw n semantics family
```

### D047: `HighamBench.P19SingularValueData.sigmaMax`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D048: `HighamBench.P19SingularValueData.sigmaMin`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D049: `HighamBench.P19StaticFixedRightCore`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1af16d2cd1d267ddac77353673fc4d8b8e1d6d44a927b0c54e52a3f25a9c5f1`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      HighamBench.P19StaticFixedRightPreconditioner family → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
        (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D050: `HighamBench.P19StaticFixedRightPreconditioner.MR`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `93922fa909bf0d374e24676a867543c8811c86c0647c04e53a44442909d17950`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      HighamBench.P19StaticFixedRightPreconditioner family → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (self : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.1
```

### D051: `HighamBench.P19StaticFixedRightPreconditioner.MRinv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4989d7a9188a57ee86d1f70d2de3270ae514c0a21799f0fc3cb6c57548d67c73`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      HighamBench.P19StaticFixedRightPreconditioner family → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (self : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.2
```

### D052: `HighamBench.P19StaticFixedRightPreconditioner.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `156e5be50a10502da40c3187d2166d6868740df4f6a4dde4a445176ea8a7b5a1`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (MR MRinv : HighamBench.P19Matrix n) →
        HighamBench.p19InversePair MR MRinv →
          HighamBench.p19InversePair (HighamBench.p19SquareRectMul family.system.A MRinv)
              (HighamBench.p19SquareRectMul MR family.system.Ainv) →
            Ne MR 1 →
              Eq family.system.ML 1 → Eq family.system.MLinv 1 → HighamBench.P19StaticFixedRightPreconditioner family
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      (MR MRinv : HighamBench.P19Matrix n) →
        (MR_inverse : @HighamBench.p19InversePair n MR MRinv) →
          (right_operator_inverse :
              @HighamBench.p19InversePair n
                (@HighamBench.p19SquareRectMul n n
                  (@HighamBench.P19Theorem31System.A n (@HighamBench.P19Theorem31Family.system n semantics family))
                  MRinv)
                (@HighamBench.p19SquareRectMul n n MR
                  (@HighamBench.P19Theorem31System.Ainv n
                    (@HighamBench.P19Theorem31Family.system n semantics family)))) →
            (nontrivial :
                @Ne.{1} (HighamBench.P19Matrix n) MR
                  (@OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 1)
                    (@One.toOfNat1.{0} (HighamBench.P19Matrix n)
                      (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne)))) →
              (left_preconditioner_identity :
                  @Eq.{1} (HighamBench.P19Matrix n)
                    (@HighamBench.P19Theorem31System.ML n (@HighamBench.P19Theorem31Family.system n semantics family))
                    (@OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 1)
                      (@One.toOfNat1.{0} (HighamBench.P19Matrix n)
                        (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne)))) →
                (left_preconditioner_inverse_identity :
                    @Eq.{1} (HighamBench.P19Matrix n)
                      (@HighamBench.P19Theorem31System.MLinv n
                        (@HighamBench.P19Theorem31Family.system n semantics family))
                      (@OfNat.ofNat.{0} (HighamBench.P19Matrix n) (nat_lit 1)
                        (@One.toOfNat1.{0} (HighamBench.P19Matrix n)
                          (@Matrix.one.{0, 0} (Fin n) Real (instDecidableEqFin n) Real.instZero Real.instOne)))) →
                  @HighamBench.P19StaticFixedRightPreconditioner n semantics family
```

### D053: `HighamBench.P19StaticFlexibleAppendixDTheory.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `78269f43236e9dfe8c665521211d36c0148823ae47c106abd084a025189da87d`

Type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {flexible : HighamBench.P19StaticFlexibleFamily n semantics} →
        ((k : HighamBench.P19Theorem31Dimension n) →
            HighamBench.p19IterationWellConditioned (flexible.family.iteration k) →
              Or (Eq k.val n) (HighamBench.p19MGSNearDependence (flexible.family.iteration k)) →
                HighamBench.P19StaticFlexibleConditions choice (flexible.iteration k) →
                  HighamBench.P19StaticFlexibleAppendixDExpansion choice flexible k) →
          HighamBench.P19StaticFlexibleAppendixDTheory choice flexible
```

Fully explicit type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {flexible : HighamBench.P19StaticFlexibleFamily n semantics} →
        (expansion :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.p19IterationWellConditioned n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                  k
                  (@HighamBench.P19Theorem31Family.iteration n semantics
                    (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k) →
                Or
                    (@Eq.{1} Nat
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      n)
                    (@HighamBench.p19MGSNearDependence n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                      semantics
                      (@HighamBench.P19Theorem31Family.basisFamily n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                      k
                      (@HighamBench.P19Theorem31Family.iteration n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k)) →
                  @HighamBench.P19StaticFlexibleConditions choice n semantics
                      (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                      (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                      (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k) →
                    @HighamBench.P19StaticFlexibleAppendixDExpansion choice n semantics flexible k) →
          @HighamBench.P19StaticFlexibleAppendixDTheory choice n semantics flexible
```

### D054: `HighamBench.P19StaticFlexibleConditions.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2c2a9c4116f616e9d400a20195748eade3a0b8e531efcec0e3b901bca268e8c6`

Type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} {k : HighamBench.P19Theorem31Dimension n}
  {iteration : HighamBench.P19StaticFlexibleIteration family preconditioner k},
  HighamBench.P19StaticFixedRightCoreConditions choice iteration.core →
    (∀ (i : Fin n) (j : Fin k.val),
        Real.instLE.le (abs (iteration.solutionBasisDelta i j))
          (instHMul.hMul iteration.core.gmresMagnitude (abs (iteration.core.zHat i j)))) →
      HighamBench.P19StaticFlexibleConditions choice iteration
```

Fully explicit type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family}
  {k : HighamBench.P19Theorem31Dimension n}
  {iteration : @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k}
  (core :
    @HighamBench.P19StaticFixedRightCoreConditions choice n semantics family preconditioner k
      (@HighamBench.P19StaticFlexibleIteration.core n semantics family preconditioner k iteration))
  (solution_basis_error_covered :
    ∀ (i : Fin n)
      (j :
        Fin
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HighamBench.P19StaticFlexibleIteration.solutionBasisDelta n semantics family preconditioner k iteration i
            j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics family preconditioner k
            (@HighamBench.P19StaticFlexibleIteration.core n semantics family preconditioner k iteration))
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HighamBench.P19StaticFixedRightCore.zHat n semantics family preconditioner k
              (@HighamBench.P19StaticFlexibleIteration.core n semantics family preconditioner k iteration) i j)))),
  @HighamBench.P19StaticFlexibleConditions choice n semantics family preconditioner k iteration
```

### D055: `HighamBench.P19StaticFlexibleFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `edebaabe72d1631e765a279660b7c46f44de870075a08afaaed29d85ea490984`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : HighamBench.P19StaticFixedRightPreconditioner family) →
        ((k : HighamBench.P19Theorem31Dimension n) → HighamBench.P19StaticFlexibleIteration family preconditioner k) →
          HighamBench.P19StaticFlexibleFamily n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
        (iteration :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k) →
          HighamBench.P19StaticFlexibleFamily n semantics
```

### D056: `HighamBench.P19StaticFlexibleIteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `5e9c08de7d5f874e9c5f183fe777a1f9219c2210175a15117429ee2d2418966c`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      HighamBench.P19StaticFixedRightPreconditioner family → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
        (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D057: `HighamBench.P19StaticRightAppendixCTheory.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `70b481668da33b5b6c0b6b1bb6200622496befc495c21c3c599f63d0852686e6`

Type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {right : HighamBench.P19StaticRightFamily n semantics} →
        ((k : HighamBench.P19Theorem31Dimension n) →
            HighamBench.p19IterationWellConditioned (right.family.iteration k) →
              Or (Eq k.val n) (HighamBench.p19MGSNearDependence (right.family.iteration k)) →
                HighamBench.P19StaticRightConditions choice (right.iteration k) →
                  HighamBench.P19StaticRightAppendixCExpansion choice right k) →
          HighamBench.P19StaticRightAppendixCTheory choice right
```

Fully explicit type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {right : HighamBench.P19StaticRightFamily n semantics} →
        (expansion :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.p19IterationWellConditioned n
                  (@HighamBench.P19Theorem31Family.system n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right))
                  semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right))
                  k
                  (@HighamBench.P19Theorem31Family.iteration n semantics
                    (@HighamBench.P19StaticRightFamily.family n semantics right) k) →
                Or
                    (@Eq.{1} Nat
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      n)
                    (@HighamBench.p19MGSNearDependence n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right))
                      semantics
                      (@HighamBench.P19Theorem31Family.basisFamily n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right))
                      k
                      (@HighamBench.P19Theorem31Family.iteration n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right) k)) →
                  @HighamBench.P19StaticRightConditions choice n semantics
                      (@HighamBench.P19StaticRightFamily.family n semantics right)
                      (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                      (@HighamBench.P19StaticRightFamily.iteration n semantics right k) →
                    @HighamBench.P19StaticRightAppendixCExpansion choice n semantics right k) →
          @HighamBench.P19StaticRightAppendixCTheory choice n semantics right
```

### D058: `HighamBench.P19StaticRightConditions.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c9329a86c1c2a0eec88310cb2ab7da37a17c3876e126d149860d1532d3f2d858`

Type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} {k : HighamBench.P19Theorem31Dimension n}
  {iteration : HighamBench.P19StaticRightIteration family preconditioner k},
  HighamBench.P19StaticFixedRightCoreConditions choice iteration.core →
    Real.instLE.le 0 iteration.reapplicationMagnitude →
      (∀ (i : Fin n) (j : Fin k.val),
          Real.instLE.le (abs (iteration.solutionBasisDelta i j))
            (instHMul.hMul iteration.core.gmresMagnitude (abs ((family.iteration k).vHat i j)))) →
        Real.instLE.le (HighamBench.p19FrobNorm iteration.solutionPreconditionerDelta)
            (instHMul.hMul iteration.reapplicationMagnitude (HighamBench.p19FrobNorm preconditioner.MRinv)) →
          Real.instLE.le iteration.reapplicationMagnitude
              (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor iteration.core.um)
                iteration.core.etaR) →
            HighamBench.P19StaticRightConditions choice iteration
```

Fully explicit type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family}
  {k : HighamBench.P19Theorem31Dimension n}
  {iteration : @HighamBench.P19StaticRightIteration n semantics family preconditioner k}
  (core :
    @HighamBench.P19StaticFixedRightCoreConditions choice n semantics family preconditioner k
      (@HighamBench.P19StaticRightIteration.core n semantics family preconditioner k iteration))
  (reapplication_magnitude_nonneg :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HighamBench.P19StaticRightIteration.reapplicationMagnitude n semantics family preconditioner k iteration))
  (solution_basis_error_covered :
    ∀ (i : Fin n)
      (j :
        Fin
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HighamBench.P19StaticRightIteration.solutionBasisDelta n semantics family preconditioner k iteration i j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics family preconditioner k
            (@HighamBench.P19StaticRightIteration.core n semantics family preconditioner k iteration))
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HighamBench.P19Algorithm2Iteration.vHat n (@HighamBench.P19Theorem31Family.system n semantics family)
              semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
              (@HighamBench.P19Theorem31Family.iteration n semantics family k) i j))))
  (solution_preconditioner_error_covered :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p19FrobNorm n n
        (@HighamBench.P19StaticRightIteration.solutionPreconditionerDelta n semantics family preconditioner k
          iteration))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19StaticRightIteration.reapplicationMagnitude n semantics family preconditioner k iteration)
        (@HighamBench.p19FrobNorm n n
          (@HighamBench.P19StaticFixedRightPreconditioner.MRinv n semantics family preconditioner))))
  (reapplication_magnitude_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.P19StaticRightIteration.reapplicationMagnitude n semantics family preconditioner k iteration)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
            (@HighamBench.P19Theorem31Family.system n semantics family) semantics
            (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
            (@HighamBench.P19Theorem31Family.iteration n semantics family k))
          (@HighamBench.P19StaticFixedRightCore.um n semantics family preconditioner k
            (@HighamBench.P19StaticRightIteration.core n semantics family preconditioner k iteration)))
        (@HighamBench.P19StaticFixedRightCore.etaR n semantics family preconditioner k
          (@HighamBench.P19StaticRightIteration.core n semantics family preconditioner k iteration)))),
  @HighamBench.P19StaticRightConditions choice n semantics family preconditioner k iteration
```

### D059: `HighamBench.P19StaticRightFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c49aa22ae2bc07d17255c2d9e29a3c4853a867118237d96c97008368111c1f1d`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : HighamBench.P19StaticFixedRightPreconditioner family) →
        ((k : HighamBench.P19Theorem31Dimension n) → HighamBench.P19StaticRightIteration family preconditioner k) →
          HighamBench.P19StaticRightFamily n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
        (iteration :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.P19StaticRightIteration n semantics family preconditioner k) →
          HighamBench.P19StaticRightFamily n semantics
```

### D060: `HighamBench.P19StaticRightIteration`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cabcb7d011f004389d989447b54059f8b7aad443bf361a37b16d687d792ee6cc`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      HighamBench.P19StaticFixedRightPreconditioner family → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (family : HighamBench.P19Theorem31Family n semantics) →
      (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
        (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D061: `HighamBench.P19StaticSquareKappaChoice.frobenius`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `427f84a86f30b1da6b07db6978118ff047b4de573aafbf63a8e16c908402fb45`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice
```

Fully explicit type:

```lean
HighamBench.P19StaticSquareKappaChoice
```

### D062: `HighamBench.P19StaticSquareKappaChoice.inducedTwo`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `6133bccfe81dd1501b725b08532f2d706adc78d227bbaac480b149b6dafc9b4f`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice
```

Fully explicit type:

```lean
HighamBench.P19StaticSquareKappaChoice
```

### D063: `HighamBench.P19Theorem31BasisFamily`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cd7346b530ce5e5d6ba1c2e5416ee7c43d715dd345875961bcce92cbe5f41e14`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → Type
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → Type
```

### D064: `HighamBench.P19Theorem31BasisFamily.basis`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e068250f38486d591a2adfb1d7f2c918bc70608277fca9f7321223a7e5e37cbb`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    HighamBench.P19Theorem31BasisFamily system → (k : Nat) → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (self : @HighamBench.P19Theorem31BasisFamily n system) → (k : Nat) → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun n system self => self.1
```

### D065: `HighamBench.P19Theorem31Family.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f076c552518a53410edcb7f11b49475fb90d812b0212bc30431c42bf011d836`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (system : HighamBench.P19Theorem31System n) →
      (basisFamily : HighamBench.P19Theorem31BasisFamily system) →
        ((k : HighamBench.P19Theorem31Dimension n) →
            HighamBench.P19Algorithm2Iteration system semantics basisFamily k) →
          HighamBench.P19Theorem31Family n semantics
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    (system : HighamBench.P19Theorem31System n) →
      (basisFamily : @HighamBench.P19Theorem31BasisFamily n system) →
        (iteration :
            (k : HighamBench.P19Theorem31Dimension n) →
              @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
          HighamBench.P19Theorem31Family n semantics
```

### D066: `HighamBench.P19Theorem31System`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1fc353b1b432c0c1ef430f4cf2ff9afcfbed92f49cf465d778ddda0a635dd4d`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D067: `HighamBench.P19Vector`

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

### D068: `HighamBench.p19Augment`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D069: `HighamBench.p19FrobNorm`

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

### D070: `HighamBench.p19IterationWellConditioned._proof_1`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e36ed6bfde9948e287453e8e216377bb07ab71b2d92789cf0f62d8ac7d27adbb`

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

### D071: `HighamBench.p19IterationWellConditioned._proof_2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `a53f13b94d3dbfd1b78203ce451bfa60bbd01b058daa3f65ff6c7d30ec55b8bd`

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

### D072: `HighamBench.p19NearRankDeficient`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `16466bbe231c4c118f1c0663cc1bb4687beb871eeebede56fe75c840088e6a50`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Real → Prop
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → (threshold : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A threshold =>
  Exists fun x =>
    And (Eq (HighamBench.p19VecNorm2 x) 1)
      (Real.instLT.lt (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec A x)) threshold)
```

### D073: `HighamBench.p19StaticExactB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4319e900a6bd10e9333ccb65413a9942cdbde8a752183b6e91ddff40f73fa205`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (system : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => HighamBench.p19MatVec system.MLinv system.b
```

### D074: `HighamBench.p19StaticExactC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `76bb6b06369be7ce2a16c093984eddc2dcc6362f2a005d765bda96800c51fcdd`

Type:

```lean
{n k : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19RectMatrix n k → HighamBench.P19RectMatrix n k
```

Fully explicit type:

```lean
{n k : Nat} →
  (system : HighamBench.P19Theorem31System n) → (Z : HighamBench.P19RectMatrix n k) → HighamBench.P19RectMatrix n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} system Z => HighamBench.p19SquareRectMul system.MLinv (HighamBench.p19SquareRectMul system.A Z)
```

### D075: `HighamBench.p19StaticKappa`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f1aafe62869eae454e5361ad332ad016bf64c6573c41182e21518b95d95352af`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice → {n : Nat} → HighamBench.P19Matrix n → HighamBench.P19Matrix n → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) → {n : Nat} → (A Ainv : HighamBench.P19Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} A Ainv =>
  HighamBench.p19StaticKappa.match_1 (fun choice => Real) choice (fun _ => HighamBench.p19ConditionNumberF A Ainv)
    fun _ => HighamBench.p19Kappa2 A Ainv
```

### D076: `HighamBench.p19StaticRightOperatorKappa`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1215f2f65acb45382e680f1efbcd34e8a8481f75d9eae7f9f998ad5589059c91`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        HighamBench.P19StaticFixedRightPreconditioner family → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner =>
  HighamBench.p19StaticKappa choice (HighamBench.p19SquareRectMul family.system.A preconditioner.MRinv)
    (HighamBench.p19SquareRectMul preconditioner.MR family.system.Ainv)
```

### D077: `HighamBench.p19StaticSystemKappa`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cdca3d40b1b6f6103929fa7a20cbb1b71a1a14af7a9c42f839dc4da0219d9b5e`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} → {semantics : HighamBench.P19FirstOrderSemantics} → HighamBench.P19Theorem31Family n semantics → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} → (family : HighamBench.P19Theorem31Family n semantics) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} family => HighamBench.p19StaticKappa choice family.system.A family.system.Ainv
```

### D078: `HighamBench.p19VecNorm2`

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

### D079: `HighamBench.P19Algorithm2Iteration.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7878f8fc84c9629c27889bbc10be4df2f10323a0af9ee7131d71f631b0264ce2`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (dimensionFactor : Real) →
            Real.instLE.le 1 dimensionFactor →
              Real →
                Real →
                  Real →
                    Real →
                      (computedC deltaC : HighamBench.P19RectMatrix n k.val) →
                        Eq computedC
                            (instHAdd.hAdd (HighamBench.p19StaticExactC system (basisFamily.basis k.val)) deltaC) →
                          (computedB deltaB : HighamBench.P19Vector n) →
                            Eq computedB (instHAdd.hAdd (HighamBench.p19StaticExactB system) deltaB) →
                              (vHat : HighamBench.P19RectMatrix n k.val) →
                                (vHatNext : HighamBench.P19RectMatrix n (instHAdd.hAdd k.val 1)) →
                                  (beta : Real) →
                                    (hessenberg : HighamBench.P19RectMatrix (instHAdd.hAdd k.val 1) k.val) →
                                      HighamBench.p19IsUpperHessenberg hessenberg →
                                        Eq (HighamBench.p19Augment computedB computedC)
                                            (HighamBench.p19RectMatMul vHatNext
                                              (HighamBench.p19Augment (HighamBench.p19ScaledFirstBasisVector beta)
                                                hessenberg)) →
                                          (∀ (i : Fin n) (j : Fin k.val), Eq (vHat i j) (vHatNext i j.castSucc)) →
                                            HighamBench.P19Vector n →
                                              HighamBench.P19RectMatrix n k.val →
                                                (yHat : HighamBench.P19Vector k.val) →
                                                  HighamBench.P19SingularValueData computedC →
                                                    HighamBench.P19SingularValueData
                                                        (HighamBench.p19StaticExactC system (basisFamily.basis k.val)) →
                                                      (xHat deltaX : HighamBench.P19Vector n) →
                                                        Eq xHat
                                                            (instHAdd.hAdd
                                                              (HighamBench.p19RectMatVec (basisFamily.basis k.val) yHat)
                                                              deltaX) →
                                                          HighamBench.P19SingularValueData vHat →
                                                            HighamBench.P19Algorithm2Iteration system semantics
                                                              basisFamily k
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (dimensionFactor : Real) →
            (dimensionFactor_one_le :
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  dimensionFactor) →
              (epsilonC epsilonB ug epsilonX : Real) →
                (computedC deltaC :
                    HighamBench.P19RectMatrix n
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)) →
                  (computation_equation :
                      @Eq.{1}
                        (HighamBench.P19RectMatrix n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))
                        computedC
                        (@HAdd.hAdd.{0, 0, 0}
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (@instHAdd.{0}
                            (HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            (@Matrix.add.{0, 0, 0} (Fin n)
                              (Fin
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k))
                              Real Real.instAdd))
                          (@HighamBench.p19StaticExactC n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k)
                            system
                            (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)))
                          deltaC)) →
                    (computedB deltaB : HighamBench.P19Vector n) →
                      (rhs_equation :
                          @Eq.{1} (HighamBench.P19Vector n) computedB
                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                              (HighamBench.P19Vector n)
                              (@instHAdd.{0} (HighamBench.P19Vector n)
                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                              (@HighamBench.p19StaticExactB n system) deltaB)) →
                        (vHat :
                            HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)) →
                          (vHatNext :
                              HighamBench.P19RectMatrix n
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            (beta : Real) →
                              (hessenberg :
                                  HighamBench.P19RectMatrix
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@Subtype.val.{1} Nat
                                      (fun (k : Nat) =>
                                        And
                                          (@LT.lt.{0} Nat instLTNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                          (@LE.le.{0} Nat instLENat k n))
                                      k)) →
                                (hessenberg_upper :
                                    @HighamBench.p19IsUpperHessenberg
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k)
                                      hessenberg) →
                                  (mgs_givens_relation :
                                      @Eq.{1}
                                        (HighamBench.P19RectMatrix n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@HighamBench.p19Augment n
                                          (@Subtype.val.{1} Nat
                                            (fun (k : Nat) =>
                                              And
                                                (@LT.lt.{0} Nat instLTNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                (@LE.le.{0} Nat instLENat k n))
                                            k)
                                          computedB computedC)
                                        (@HighamBench.p19RectMatMul n
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          vHatNext
                                          (@HighamBench.p19Augment
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@Subtype.val.{1} Nat
                                              (fun (k : Nat) =>
                                                And
                                                  (@LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                  (@LE.le.{0} Nat instLENat k n))
                                              k)
                                            (@HighamBench.p19ScaledFirstBasisVector
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)
                                              beta)
                                            hessenberg))) →
                                    (vHat_prefix :
                                        ∀ (i : Fin n)
                                          (j :
                                            Fin
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)),
                                          @Eq.{1} Real (vHat i j)
                                            (vHatNext i
                                              (@Fin.castSucc
                                                (@Subtype.val.{1} Nat
                                                  (fun (k : Nat) =>
                                                    And
                                                      (@LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                      (@LE.le.{0} Nat instLENat k n))
                                                  k)
                                                j))) →
                                      (leastSquaresDeltaB : HighamBench.P19Vector n) →
                                        (leastSquaresDeltaC :
                                            HighamBench.P19RectMatrix n
                                              (@Subtype.val.{1} Nat
                                                (fun (k : Nat) =>
                                                  And
                                                    (@LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                    (@LE.le.{0} Nat instLENat k n))
                                                k)) →
                                          (yHat :
                                              HighamBench.P19Vector
                                                (@Subtype.val.{1} Nat
                                                  (fun (k : Nat) =>
                                                    And
                                                      (@LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                                      (@LE.le.{0} Nat instLENat k n))
                                                  k)) →
                                            (computedCSpectrum :
                                                @HighamBench.P19SingularValueData n
                                                  (@Subtype.val.{1} Nat
                                                    (fun (k : Nat) =>
                                                      And
                                                        (@LT.lt.{0} Nat instLTNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                          k)
                                                        (@LE.le.{0} Nat instLENat k n))
                                                    k)
                                                  computedC) →
                                              (exactCSpectrum :
                                                  @HighamBench.P19SingularValueData n
                                                    (@Subtype.val.{1} Nat
                                                      (fun (k : Nat) =>
                                                        And
                                                          (@LT.lt.{0} Nat instLTNat
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                              (instOfNatNat (nat_lit 0)))
                                                            k)
                                                          (@LE.le.{0} Nat instLENat k n))
                                                      k)
                                                    (@HighamBench.p19StaticExactC n
                                                      (@Subtype.val.{1} Nat
                                                        (fun (k : Nat) =>
                                                          And
                                                            (@LT.lt.{0} Nat instLTNat
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                (instOfNatNat (nat_lit 0)))
                                                              k)
                                                            (@LE.le.{0} Nat instLENat k n))
                                                        k)
                                                      system
                                                      (@HighamBench.P19Theorem31BasisFamily.basis n system basisFamily
                                                        (@Subtype.val.{1} Nat
                                                          (fun (k : Nat) =>
                                                            And
                                                              (@LT.lt.{0} Nat instLTNat
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                  (instOfNatNat (nat_lit 0)))
                                                                k)
                                                              (@LE.le.{0} Nat instLENat k n))
                                                          k)))) →
                                                (xHat deltaX : HighamBench.P19Vector n) →
                                                  (solution_equation :
                                                      @Eq.{1} (HighamBench.P19Vector n) xHat
                                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n)
                                                          (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                                          (@instHAdd.{0} (HighamBench.P19Vector n)
                                                            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                              fun (i : Fin n) => Real.instAdd))
                                                          (@HighamBench.p19RectMatVec n
                                                            (@Subtype.val.{1} Nat
                                                              (fun (k : Nat) =>
                                                                And
                                                                  (@LT.lt.{0} Nat instLTNat
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                      (instOfNatNat (nat_lit 0)))
                                                                    k)
                                                                  (@LE.le.{0} Nat instLENat k n))
                                                              k)
                                                            (@HighamBench.P19Theorem31BasisFamily.basis n system
                                                              basisFamily
                                                              (@Subtype.val.{1} Nat
                                                                (fun (k : Nat) =>
                                                                  And
                                                                    (@LT.lt.{0} Nat instLTNat
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                        (instOfNatNat (nat_lit 0)))
                                                                      k)
                                                                    (@LE.le.{0} Nat instLENat k n))
                                                                k))
                                                            yHat)
                                                          deltaX)) →
                                                    (vHatSpectrum :
                                                        @HighamBench.P19SingularValueData n
                                                          (@Subtype.val.{1} Nat
                                                            (fun (k : Nat) =>
                                                              And
                                                                (@LT.lt.{0} Nat instLTNat
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                    (instOfNatNat (nat_lit 0)))
                                                                  k)
                                                                (@LE.le.{0} Nat instLENat k n))
                                                            k)
                                                          vHat) →
                                                      @HighamBench.P19Algorithm2Iteration n system semantics basisFamily
                                                        k
```

### D080: `HighamBench.P19Matrix`

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

### D081: `HighamBench.P19RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D082: `HighamBench.P19SingularValueData`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → HighamBench.P19RectMatrix m k → Type
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P19RectMatrix m k) → Type
```

### D083: `HighamBench.P19StaticFixedRightCore.gmresMagnitude`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4d2d968913ccc754c646d62d2bcf417cd5b9d4110b2be676bfd97d49874a8ef3`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.16
```

### D084: `HighamBench.P19StaticFixedRightCore.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `9350cce7e938e2c075e92242dd9895ea2ba02bdf411a808a1d46e8c300282be1`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          Real →
            Real →
              Real →
                Real →
                  Real →
                    (zHat : HighamBench.P19RectMatrix n k.val) →
                      (preconditionerDelta : Fin k.val → HighamBench.P19Matrix n) →
                        (∀ (j : Fin k.val),
                            Eq (HighamBench.p19Column zHat j)
                              (HighamBench.p19MatVec (instHAdd.hAdd preconditioner.MRinv (preconditionerDelta j))
                                (HighamBench.p19Column (family.iteration k).vHat j))) →
                          (matrixDelta : Fin k.val → HighamBench.P19Matrix n) →
                            (∀ (j : Fin k.val),
                                Eq (HighamBench.p19Column (family.iteration k).computedC j)
                                  (HighamBench.p19MatVec (instHAdd.hAdd family.system.A (matrixDelta j))
                                    (HighamBench.p19Column zHat j))) →
                              (∀ (j : Fin k.val),
                                  Eq (HighamBench.p19Column (family.basisFamily.basis k.val) j)
                                    (instHAdd.hAdd (HighamBench.p19Column zHat j)
                                      (HighamBench.p19MatVec family.system.Ainv
                                        (HighamBench.p19MatVec (matrixDelta j) (HighamBench.p19Column zHat j))))) →
                                Eq (family.iteration k).deltaC 0 →
                                  Eq (family.iteration k).epsilonC 0 →
                                    Eq (family.iteration k).deltaB 0 →
                                      Eq (family.iteration k).epsilonB 0 →
                                        Real → Real → Real → HighamBench.P19StaticFixedRightCore family preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (ug um ua etaR rhoAR : Real) →
            (zHat :
                HighamBench.P19RectMatrix n
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)) →
              (preconditionerDelta :
                  Fin
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k) →
                    HighamBench.P19Matrix n) →
                (preconditioner_application :
                    ∀
                      (j :
                        Fin
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k)),
                      @Eq.{1} (HighamBench.P19Vector n)
                        (@HighamBench.p19Column n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k)
                          zHat j)
                        (@HighamBench.p19MatVec n
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                            (HighamBench.P19Matrix n)
                            (@instHAdd.{0} (HighamBench.P19Matrix n)
                              (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                            (@HighamBench.P19StaticFixedRightPreconditioner.MRinv n semantics family preconditioner)
                            (preconditionerDelta j))
                          (@HighamBench.p19Column n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k)
                            (@HighamBench.P19Algorithm2Iteration.vHat n
                              (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                              (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                              (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                            j))) →
                  (matrixDelta :
                      Fin
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k) →
                        HighamBench.P19Matrix n) →
                    (matrix_application :
                        ∀
                          (j :
                            Fin
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)),
                          @Eq.{1} (HighamBench.P19Vector n)
                            (@HighamBench.p19Column n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k)
                              (@HighamBench.P19Algorithm2Iteration.computedC n
                                (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                              j)
                            (@HighamBench.p19MatVec n
                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                                (HighamBench.P19Matrix n)
                                (@instHAdd.{0} (HighamBench.P19Matrix n)
                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                (@HighamBench.P19Theorem31System.A n
                                  (@HighamBench.P19Theorem31Family.system n semantics family))
                                (matrixDelta j))
                              (@HighamBench.p19Column n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k)
                                zHat j))) →
                      (search_space_equation :
                          ∀
                            (j :
                              Fin
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k)),
                            @Eq.{1} (HighamBench.P19Vector n)
                              (@HighamBench.p19Column n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k)
                                (@HighamBench.P19Theorem31BasisFamily.basis n
                                  (@HighamBench.P19Theorem31Family.system n semantics family)
                                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family)
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k))
                                j)
                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                                (HighamBench.P19Vector n)
                                (@instHAdd.{0} (HighamBench.P19Vector n)
                                  (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAdd))
                                (@HighamBench.p19Column n
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k)
                                  zHat j)
                                (@HighamBench.p19MatVec n
                                  (@HighamBench.P19Theorem31System.Ainv n
                                    (@HighamBench.P19Theorem31Family.system n semantics family))
                                  (@HighamBench.p19MatVec n (matrixDelta j)
                                    (@HighamBench.p19Column n
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k)
                                      zHat j))))) →
                        (computation_exact :
                            @Eq.{1}
                              (HighamBench.P19RectMatrix n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k))
                              (@HighamBench.P19Algorithm2Iteration.deltaC n
                                (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                              (@OfNat.ofNat.{0}
                                (HighamBench.P19RectMatrix n
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k))
                                (nat_lit 0)
                                (@Zero.toOfNat0.{0}
                                  (HighamBench.P19RectMatrix n
                                    (@Subtype.val.{1} Nat
                                      (fun (k : Nat) =>
                                        And
                                          (@LT.lt.{0} Nat instLTNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                          (@LE.le.{0} Nat instLENat k n))
                                      k))
                                  (@Matrix.zero.{0, 0, 0} (Fin n)
                                    (Fin
                                      (@Subtype.val.{1} Nat
                                        (fun (k : Nat) =>
                                          And
                                            (@LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                            (@LE.le.{0} Nat instLENat k n))
                                        k))
                                    Real Real.instZero)))) →
                          (computation_accuracy_zero :
                              @Eq.{1} Real
                                (@HighamBench.P19Algorithm2Iteration.epsilonC n
                                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                  (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                            (rhs_exact :
                                @Eq.{1} (HighamBench.P19Vector n)
                                  (@HighamBench.P19Algorithm2Iteration.deltaB n
                                    (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                    (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                    (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                                  (@OfNat.ofNat.{0} (HighamBench.P19Vector n) (nat_lit 0)
                                    (@Zero.toOfNat0.{0} (HighamBench.P19Vector n)
                                      (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                        Real.instZero)))) →
                              (rhs_accuracy_zero :
                                  @Eq.{1} Real
                                    (@HighamBench.P19Algorithm2Iteration.epsilonB n
                                      (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                                      (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                                      (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                (gmresMagnitude basisPreconditionerMagnitude matrixMagnitude : Real) →
                                  @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k
```

### D085: `HighamBench.P19StaticFixedRightCore.zHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b56e2cbdae79a1e58d5c79b9e12a34b46e582903610864017bfea9b8e97c9713`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFixedRightCore family preconditioner k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.6
```

### D086: `HighamBench.P19StaticFixedRightCoreConditions`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `016be990d9e6562997c177aa1874f71efa7402ccc6972370d935b3f4dafea7a5`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
          {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Prop
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
          {k : HighamBench.P19Theorem31Dimension n} →
            (core : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Prop
```

### D087: `HighamBench.P19StaticFlexibleAppendixDExpansion`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `5cef23cfeb936e19b0b7988e63298cf52d29246a942e2901eb35bd8ab58fee68`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      HighamBench.P19StaticFlexibleFamily n semantics → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      (flexible : HighamBench.P19StaticFlexibleFamily n semantics) → (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D088: `HighamBench.P19StaticFlexibleIteration.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `87cf04a5e2068651a900467f8158ee477865ac28341036c97845ae083f25d796`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (core : HighamBench.P19StaticFixedRightCore family preconditioner k) →
            (solutionBasisDelta : HighamBench.P19RectMatrix n k.val) →
              Eq (family.iteration k).xHat
                  (HighamBench.p19RectMatVec (instHAdd.hAdd core.zHat solutionBasisDelta) (family.iteration k).yHat) →
                HighamBench.P19StaticFlexibleIteration family preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (core : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) →
            (solutionBasisDelta :
                HighamBench.P19RectMatrix n
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)) →
              (solution_equation :
                  @Eq.{1} (HighamBench.P19Vector n)
                    (@HighamBench.P19Algorithm2Iteration.xHat n
                      (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                      (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                      (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                    (@HighamBench.p19RectMatVec n
                      (@Subtype.val.{1} Nat
                        (fun (k : Nat) =>
                          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (@LE.le.{0} Nat instLENat k n))
                        k)
                      (@HAdd.hAdd.{0, 0, 0}
                        (HighamBench.P19RectMatrix n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))
                        (HighamBench.P19RectMatrix n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))
                        (HighamBench.P19RectMatrix n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k))
                        (@instHAdd.{0}
                          (HighamBench.P19RectMatrix n
                            (@Subtype.val.{1} Nat
                              (fun (k : Nat) =>
                                And
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                  (@LE.le.{0} Nat instLENat k n))
                              k))
                          (@Matrix.add.{0, 0, 0} (Fin n)
                            (Fin
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            Real Real.instAdd))
                        (@HighamBench.P19StaticFixedRightCore.zHat n semantics family preconditioner k core)
                        solutionBasisDelta)
                      (@HighamBench.P19Algorithm2Iteration.yHat n
                        (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                        (@HighamBench.P19Theorem31Family.iteration n semantics family k)))) →
                @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k
```

### D089: `HighamBench.P19StaticFlexibleIteration.solutionBasisDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b784e6b43783fd820c5c035d7b910e51529d7e16a921e8ffb3f3a23ab39f4f6c`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFlexibleIteration family preconditioner k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFlexibleIteration n semantics family preconditioner k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D090: `HighamBench.P19StaticRightAppendixCExpansion`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `4cde4ccc7bab7c66868f49ed20203d5fc92241921cf22fc6c8b0a001b613934b`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      HighamBench.P19StaticRightFamily n semantics → HighamBench.P19Theorem31Dimension n → Type
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      (right : HighamBench.P19StaticRightFamily n semantics) → (k : HighamBench.P19Theorem31Dimension n) → Type
```

### D091: `HighamBench.P19StaticRightIteration.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1ada26d0afe6a36a93c329bf7511d6ee605dbdb09560947e17203c3d31d3a79a`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFixedRightCore family preconditioner k →
            (solutionBasisDelta : HighamBench.P19RectMatrix n k.val) →
              (solutionPreconditionerDelta : HighamBench.P19Matrix n) →
                Eq (family.iteration k).xHat
                    (HighamBench.p19MatVec (instHAdd.hAdd preconditioner.MRinv solutionPreconditionerDelta)
                      (HighamBench.p19RectMatVec (instHAdd.hAdd (family.iteration k).vHat solutionBasisDelta)
                        (family.iteration k).yHat)) →
                  Real → HighamBench.P19StaticRightIteration family preconditioner k
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (core : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) →
            (solutionBasisDelta :
                HighamBench.P19RectMatrix n
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)) →
              (solutionPreconditionerDelta : HighamBench.P19Matrix n) →
                (solution_equation :
                    @Eq.{1} (HighamBench.P19Vector n)
                      (@HighamBench.P19Algorithm2Iteration.xHat n
                        (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                        (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                      (@HighamBench.p19MatVec n
                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Matrix n) (HighamBench.P19Matrix n)
                          (HighamBench.P19Matrix n)
                          (@instHAdd.{0} (HighamBench.P19Matrix n)
                            (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                          (@HighamBench.P19StaticFixedRightPreconditioner.MRinv n semantics family preconditioner)
                          solutionPreconditionerDelta)
                        (@HighamBench.p19RectMatVec n
                          (@Subtype.val.{1} Nat
                            (fun (k : Nat) =>
                              And
                                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  k)
                                (@LE.le.{0} Nat instLENat k n))
                            k)
                          (@HAdd.hAdd.{0, 0, 0}
                            (HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            (HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            (HighamBench.P19RectMatrix n
                              (@Subtype.val.{1} Nat
                                (fun (k : Nat) =>
                                  And
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                    (@LE.le.{0} Nat instLENat k n))
                                k))
                            (@instHAdd.{0}
                              (HighamBench.P19RectMatrix n
                                (@Subtype.val.{1} Nat
                                  (fun (k : Nat) =>
                                    And
                                      (@LT.lt.{0} Nat instLTNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                      (@LE.le.{0} Nat instLENat k n))
                                  k))
                              (@Matrix.add.{0, 0, 0} (Fin n)
                                (Fin
                                  (@Subtype.val.{1} Nat
                                    (fun (k : Nat) =>
                                      And
                                        (@LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                                        (@LE.le.{0} Nat instLENat k n))
                                    k))
                                Real Real.instAdd))
                            (@HighamBench.P19Algorithm2Iteration.vHat n
                              (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                              (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                              (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                            solutionBasisDelta)
                          (@HighamBench.P19Algorithm2Iteration.yHat n
                            (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                            (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                            (@HighamBench.P19Theorem31Family.iteration n semantics family k))))) →
                  (reapplicationMagnitude : Real) →
                    @HighamBench.P19StaticRightIteration n semantics family preconditioner k
```

### D092: `HighamBench.P19StaticRightIteration.reapplicationMagnitude`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `87c016c305345e674cfc17562e6417fa28c4f011d96f9c9668c558690209e001`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticRightIteration family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticRightIteration n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.5
```

### D093: `HighamBench.P19StaticRightIteration.solutionBasisDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cf09e35efe02c9c8e0dfca39c9c32922056955e832949936696a5292fb763d41`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticRightIteration family preconditioner k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticRightIteration n semantics family preconditioner k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D094: `HighamBench.P19StaticRightIteration.solutionPreconditionerDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5c63c83c2443351239918695b96d935028fbce761a000c12ef703ba7a99982f`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticRightIteration family preconditioner k → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticRightIteration n semantics family preconditioner k) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.3
```

### D095: `HighamBench.P19Theorem31BasisFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `436dbb701a39337ce5332902d90e6973e9b3a19d7776ff8eb60c5b47e5d23e93`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (basis : (k : Nat) → HighamBench.P19RectMatrix n k) →
      (∀ (k : Nat), instLTNat.lt 0 k → instLENat.le k n → HighamBench.p19FullColumnRank (basis k)) →
        (∀ (k : Nat),
            instLTNat.lt k n → ∀ (i : Fin n) (j : Fin k), Eq (basis k i j) (basis (instHAdd.hAdd k 1) i j.castSucc)) →
          HighamBench.P19Theorem31BasisFamily system
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    (basis : (k : Nat) → HighamBench.P19RectMatrix n k) →
      (full_rank :
          ∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
              @LE.le.{0} Nat instLENat k n → @HighamBench.p19FullColumnRank n k (basis k)) →
        (column_prefix :
            ∀ (k : Nat),
              @LT.lt.{0} Nat instLTNat k n →
                ∀ (i : Fin n) (j : Fin k),
                  @Eq.{1} Real (basis k i j)
                    (basis
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      i (@Fin.castSucc k j))) →
          @HighamBench.P19Theorem31BasisFamily n system
```

### D096: `HighamBench.P19Theorem31System.A`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4bfdf1aea21b236835dd2c7582c4c22271b794da188a0ba1ccc5a694afff4be4`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D097: `HighamBench.P19Theorem31System.Ainv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `5af7fc516b339d9009da5411f78f824a75063e508c6084b47f8ef7e44f62db8e`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D098: `HighamBench.P19Theorem31System.ML`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `49bf2034c91342a98820db7017c34f0a2e9d1c3aaff5c66811d036bd3b1a1dcf`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D099: `HighamBench.P19Theorem31System.MLinv`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef0cd4e713f0114adf6c09b9205814f09e9a4779fd1ba97cdfa6d00458ff172c`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D100: `HighamBench.P19Theorem31System.b`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f2a130fd36774a5574504267aaab72b46108b1c686d97df059b452f44cf66199`

Type:

```lean
{n : Nat} → HighamBench.P19Theorem31System n → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P19Theorem31System n) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D101: `HighamBench.P19Theorem31System.dimension_pos`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7bcc8692a7674f34e3a15ff70ef2f751cd9c1fac7daae1fce18d92dbba9eb545`

Type:

```lean
∀ {n : Nat} (self : HighamBench.P19Theorem31System n), instLTNat.lt 0 n
```

Fully explicit type:

```lean
∀ {n : Nat} (self : HighamBench.P19Theorem31System n),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n
```

### D102: `HighamBench.P19Theorem31System.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b6ce3331a8ec6712c83ccceaf2dca3a6a89ee6e003288845219a21bd32c3a9a7`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv ML MLinv : HighamBench.P19Matrix n) →
      (b xExact : HighamBench.P19Vector n) →
        HighamBench.p19InversePair A Ainv →
          HighamBench.p19InversePair ML MLinv →
            Ne b 0 → Eq (HighamBench.p19MatVec A xExact) b → HighamBench.P19Theorem31System n
```

Fully explicit type:

```lean
{n : Nat} →
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
                HighamBench.P19Theorem31System n
```

### D103: `HighamBench.p19ConditionNumberF`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D104: `HighamBench.p19InversePair`

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

### D105: `HighamBench.p19Kappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D106: `HighamBench.p19MatVec`

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

### D107: `HighamBench.p19RectMatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D108: `HighamBench.p19SquareRectMul`

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

### D109: `HighamBench.p19StaticKappa.match_1`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `83ccdc85da23e3fc059d5d5518c2749c7999b293db657535adaacd198c92d663`

Type:

```lean
(motive : HighamBench.P19StaticSquareKappaChoice → Sort u_1) →
  (choice : HighamBench.P19StaticSquareKappaChoice) →
    (Unit → motive HighamBench.P19StaticSquareKappaChoice.frobenius) →
      (Unit → motive HighamBench.P19StaticSquareKappaChoice.inducedTwo) → motive choice
```

Fully explicit type:

```lean
(motive : HighamBench.P19StaticSquareKappaChoice → Sort u_1) →
  (choice : HighamBench.P19StaticSquareKappaChoice) →
    (h_1 : (a : Unit) → motive HighamBench.P19StaticSquareKappaChoice.frobenius) →
      (h_2 : (a : Unit) → motive HighamBench.P19StaticSquareKappaChoice.inducedTwo) → motive choice
```

Definition body (one-level semantic boundary):

```lean
fun motive choice h_1 h_2 => HighamBench.P19StaticSquareKappaChoice.casesOn choice (h_1 Unit.unit) (h_2 Unit.unit)
```

### D110: `HighamBench.p19VecNorm2Sq`

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

### D111: `HighamBench.P19Algorithm2Iteration.computedC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `50a6535dd8ce1360428870bf95756a470737cd826b008cdbfad61b0808d02dee`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.7
```

### D112: `HighamBench.P19Algorithm2Iteration.deltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `737380e55e6f4d002c09906b6bcf025c9bda8e34cbadd9e15e1eacd15618ad5b`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.11
```

### D113: `HighamBench.P19Algorithm2Iteration.deltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `8b975d7f99cb27792acfddfe57d6c62419fd06a5e22f149738ab976b8c92053c`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.8
```

### D114: `HighamBench.P19Algorithm2Iteration.epsilonB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `f8030bfc92643eceb346f953d6858c99670b9bac33003239e0d7a3301ae7fe23`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.4
```

### D115: `HighamBench.P19Algorithm2Iteration.yHat`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `17f32ecc0179dc60da4f31e7911e5c48e15e77ecc3d4689d7406db80def04525`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19Vector
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.22
```

### D116: `HighamBench.P19SingularValueData.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
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

### D117: `HighamBench.P19StaticFixedRightCoreConditions.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `1e5461a9440d5db520105ad599559071d3c6c5eaba5025c2d2229bd770e0a7c2`

Type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} {k : HighamBench.P19Theorem31Dimension n}
  {core : HighamBench.P19StaticFixedRightCore family preconditioner k},
  And (Real.instLE.le 0 core.ug)
      (And (Real.instLE.le 0 core.um)
        (And (Real.instLE.le 0 core.ua) (And (Real.instLE.le 0 core.etaR) (Real.instLE.le 0 core.rhoAR)))) →
    And (Real.instLE.le 0 core.gmresMagnitude)
        (And (Real.instLE.le 0 core.basisPreconditionerMagnitude) (Real.instLE.le 0 core.matrixMagnitude)) →
      HighamBench.p19IsLeastSquaresSolution
          (instHAdd.hAdd (family.iteration k).computedC (family.iteration k).leastSquaresDeltaC)
          (instHAdd.hAdd (family.iteration k).computedB (family.iteration k).leastSquaresDeltaB)
          (family.iteration k).yHat →
        (∀ (j : Fin (instHAdd.hAdd k.val 1)),
            Real.instLE.le
              (HighamBench.p19VecNorm2
                (HighamBench.p19Column
                  (HighamBench.p19Augment (family.iteration k).leastSquaresDeltaB
                    (family.iteration k).leastSquaresDeltaC)
                  j))
              (instHMul.hMul core.gmresMagnitude
                (HighamBench.p19VecNorm2
                  (HighamBench.p19Column
                    (HighamBench.p19Augment (family.iteration k).computedB (family.iteration k).computedC) j)))) →
          (∀ (j : Fin k.val),
              Real.instLE.le (HighamBench.p19FrobNorm (core.preconditionerDelta j))
                (instHMul.hMul core.basisPreconditionerMagnitude (HighamBench.p19FrobNorm preconditioner.MRinv))) →
            (∀ (j : Fin k.val) (i q : Fin n),
                Real.instLE.le (abs (core.matrixDelta j i q))
                  (instHMul.hMul core.matrixMagnitude (abs (family.system.A i q)))) →
              Real.instLE.le core.gmresMagnitude (instHMul.hMul (family.iteration k).dimensionFactor core.ug) →
                Real.instLE.le core.basisPreconditionerMagnitude
                    (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor core.um) core.etaR) →
                  Real.instLE.le core.matrixMagnitude (instHMul.hMul (family.iteration k).dimensionFactor core.ua) →
                    Real.instLT.lt 0
                        (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec core.zHat (family.iteration k).yHat)) →
                      Eq core.rhoAR
                          (instHDiv.hDiv
                            (HighamBench.p19VecNorm2 (HighamBench.p19AbsRectMatVec core.zHat (family.iteration k).yHat))
                            (HighamBench.p19VecNorm2 (HighamBench.p19RectMatVec core.zHat (family.iteration k).yHat))) →
                        semantics.small
                            (HighamBench.p19StaticCondition316Value choice preconditioner core.ug core.um core.ua
                              core.etaR core.rhoAR) →
                          HighamBench.P19StaticFixedRightCoreConditions choice core
```

Fully explicit type:

```lean
∀ {choice : HighamBench.P19StaticSquareKappaChoice} {n : Nat} {semantics : HighamBench.P19FirstOrderSemantics}
  {family : HighamBench.P19Theorem31Family n semantics}
  {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family}
  {k : HighamBench.P19Theorem31Dimension n}
  {core : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k}
  (parameters_nonneg :
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HighamBench.P19StaticFixedRightCore.ug n semantics family preconditioner k core))
      (And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HighamBench.P19StaticFixedRightCore.um n semantics family preconditioner k core))
        (And
          (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HighamBench.P19StaticFixedRightCore.ua n semantics family preconditioner k core))
          (And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HighamBench.P19StaticFixedRightCore.etaR n semantics family preconditioner k core))
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics family preconditioner k core))))))
  (magnitudes_nonneg :
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics family preconditioner k core))
      (And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HighamBench.P19StaticFixedRightCore.basisPreconditionerMagnitude n semantics family preconditioner k core))
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HighamBench.P19StaticFixedRightCore.matrixMagnitude n semantics family preconditioner k core))))
  (least_squares_solution :
    @HighamBench.p19IsLeastSquaresSolution n
      (@Subtype.val.{1} Nat
        (fun (k : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (@LE.le.{0} Nat instLENat k n))
        k)
      (@HAdd.hAdd.{0, 0, 0}
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (HighamBench.P19RectMatrix n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
        (@instHAdd.{0}
          (HighamBench.P19RectMatrix n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k))
          (@Matrix.add.{0, 0, 0} (Fin n)
            (Fin
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k))
            Real Real.instAdd))
        (@HighamBench.P19Algorithm2Iteration.computedC n (@HighamBench.P19Theorem31Family.system n semantics family)
          semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k))
        (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC n
          (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
        (@instHAdd.{0} (HighamBench.P19Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        (@HighamBench.P19Algorithm2Iteration.computedB n (@HighamBench.P19Theorem31Family.system n semantics family)
          semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k))
        (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB n
          (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
      (@HighamBench.P19Algorithm2Iteration.yHat n (@HighamBench.P19Theorem31Family.system n semantics family) semantics
        (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
        (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
  (least_squares_error_covered :
    ∀
      (j :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @LE.le.{0} Real Real.instLE
        (@HighamBench.p19VecNorm2 n
          (@HighamBench.p19Column n
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HighamBench.p19Augment n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
              (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB n
                (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                (@HighamBench.P19Theorem31Family.iteration n semantics family k))
              (@HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC n
                (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
            j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics family preconditioner k core)
          (@HighamBench.p19VecNorm2 n
            (@HighamBench.p19Column n
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HighamBench.p19Augment n
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k)
                (@HighamBench.P19Algorithm2Iteration.computedB n
                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                  (@HighamBench.P19Theorem31Family.iteration n semantics family k))
                (@HighamBench.P19Algorithm2Iteration.computedC n
                  (@HighamBench.P19Theorem31Family.system n semantics family) semantics
                  (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
                  (@HighamBench.P19Theorem31Family.iteration n semantics family k)))
              j))))
  (basis_preconditioner_error_covered :
    ∀
      (j :
        Fin
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)),
      @LE.le.{0} Real Real.instLE
        (@HighamBench.p19FrobNorm n n
          (@HighamBench.P19StaticFixedRightCore.preconditionerDelta n semantics family preconditioner k core j))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19StaticFixedRightCore.basisPreconditionerMagnitude n semantics family preconditioner k core)
          (@HighamBench.p19FrobNorm n n
            (@HighamBench.P19StaticFixedRightPreconditioner.MRinv n semantics family preconditioner))))
  (matrix_error_covered :
    ∀
      (j :
        Fin
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k))
      (i q : Fin n),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HighamBench.P19StaticFixedRightCore.matrixDelta n semantics family preconditioner k core j i q))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19StaticFixedRightCore.matrixMagnitude n semantics family preconditioner k core)
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HighamBench.P19Theorem31System.A n (@HighamBench.P19Theorem31Family.system n semantics family) i q))))
  (gmres_magnitude_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics family preconditioner k core)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
          (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k))
        (@HighamBench.P19StaticFixedRightCore.ug n semantics family preconditioner k core)))
  (basis_preconditioner_magnitude_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.P19StaticFixedRightCore.basisPreconditionerMagnitude n semantics family preconditioner k core)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
            (@HighamBench.P19Theorem31Family.system n semantics family) semantics
            (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
            (@HighamBench.P19Theorem31Family.iteration n semantics family k))
          (@HighamBench.P19StaticFixedRightCore.um n semantics family preconditioner k core))
        (@HighamBench.P19StaticFixedRightCore.etaR n semantics family preconditioner k core)))
  (matrix_magnitude_bound :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.P19StaticFixedRightCore.matrixMagnitude n semantics family preconditioner k core)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.P19Algorithm2Iteration.dimensionFactor n
          (@HighamBench.P19Theorem31Family.system n semantics family) semantics
          (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
          (@HighamBench.P19Theorem31Family.iteration n semantics family k))
        (@HighamBench.P19StaticFixedRightCore.ua n semantics family preconditioner k core)))
  (rho_denominator_pos :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HighamBench.p19VecNorm2 n
        (@HighamBench.p19RectMatVec n
          (@Subtype.val.{1} Nat
            (fun (k : Nat) =>
              And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                (@LE.le.{0} Nat instLENat k n))
            k)
          (@HighamBench.P19StaticFixedRightCore.zHat n semantics family preconditioner k core)
          (@HighamBench.P19Algorithm2Iteration.yHat n (@HighamBench.P19Theorem31Family.system n semantics family)
            semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
            (@HighamBench.P19Theorem31Family.iteration n semantics family k)))))
  (rho_equation :
    @Eq.{1} Real (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics family preconditioner k core)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HighamBench.p19VecNorm2 n
          (@HighamBench.p19AbsRectMatVec n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@HighamBench.P19StaticFixedRightCore.zHat n semantics family preconditioner k core)
            (@HighamBench.P19Algorithm2Iteration.yHat n (@HighamBench.P19Theorem31Family.system n semantics family)
              semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
              (@HighamBench.P19Theorem31Family.iteration n semantics family k))))
        (@HighamBench.p19VecNorm2 n
          (@HighamBench.p19RectMatVec n
            (@Subtype.val.{1} Nat
              (fun (k : Nat) =>
                And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (@LE.le.{0} Nat instLENat k n))
              k)
            (@HighamBench.P19StaticFixedRightCore.zHat n semantics family preconditioner k core)
            (@HighamBench.P19Algorithm2Iteration.yHat n (@HighamBench.P19Theorem31Family.system n semantics family)
              semantics (@HighamBench.P19Theorem31Family.basisFamily n semantics family) k
              (@HighamBench.P19Theorem31Family.iteration n semantics family k))))))
  (condition316 :
    HighamBench.P19FirstOrderSemantics.small semantics
      (@HighamBench.p19StaticCondition316Value choice n semantics family preconditioner
        (@HighamBench.P19StaticFixedRightCore.ug n semantics family preconditioner k core)
        (@HighamBench.P19StaticFixedRightCore.um n semantics family preconditioner k core)
        (@HighamBench.P19StaticFixedRightCore.ua n semantics family preconditioner k core)
        (@HighamBench.P19StaticFixedRightCore.etaR n semantics family preconditioner k core)
        (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics family preconditioner k core))),
  @HighamBench.P19StaticFixedRightCoreConditions choice n semantics family preconditioner k core
```

### D118: `HighamBench.P19StaticFlexibleAppendixDExpansion.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `6108f0867ca7c4748ff0bdc401b9f44c593ecf6cb651694c00eaab4e73a79644`

Type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {flexible : HighamBench.P19StaticFlexibleFamily n semantics} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (gmresContribution matrixContribution remainder : HighamBench.P19Vector n) →
            Eq (instHSub.hSub (flexible.family.iteration k).xHat flexible.family.system.xExact)
                (instHAdd.hAdd (instHAdd.hAdd gmresContribution matrixContribution) remainder) →
              semantics.secondOrder
                  (instHDiv.hDiv (HighamBench.p19VecNorm2 remainder)
                    (HighamBench.p19VecNorm2 flexible.family.system.xExact)) →
                Real.instLE.le
                    (instHDiv.hDiv (HighamBench.p19VecNorm2 gmresContribution)
                      (HighamBench.p19VecNorm2 flexible.family.system.xExact))
                    (instHMul.hMul
                      (instHMul.hMul (flexible.iteration k).core.gmresMagnitude
                        (HighamBench.p19StaticRightOperatorKappa choice flexible.preconditioner))
                      (HighamBench.p19StaticRightPreconditionerKappa choice flexible.preconditioner)) →
                  Real.instLE.le
                      (instHDiv.hDiv (HighamBench.p19VecNorm2 matrixContribution)
                        (HighamBench.p19VecNorm2 flexible.family.system.xExact))
                      (instHMul.hMul
                        (instHMul.hMul (flexible.iteration k).core.matrixMagnitude
                          (HighamBench.p19StaticSystemKappa choice flexible.family))
                        (flexible.iteration k).core.rhoAR) →
                    HighamBench.P19StaticFlexibleAppendixDExpansion choice flexible k
```

Fully explicit type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {flexible : HighamBench.P19StaticFlexibleFamily n semantics} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (gmresContribution matrixContribution remainder : HighamBench.P19Vector n) →
            (error_decomposition :
                @Eq.{1} (HighamBench.P19Vector n)
                  (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                    (@instHSub.{0} (HighamBench.P19Vector n)
                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                    (@HighamBench.P19Algorithm2Iteration.xHat n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                      semantics
                      (@HighamBench.P19Theorem31Family.basisFamily n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))
                      k
                      (@HighamBench.P19Theorem31Family.iteration n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible) k))
                    (@HighamBench.P19Theorem31System.xExact n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible))))
                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                    (@instHAdd.{0} (HighamBench.P19Vector n)
                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                      (@instHAdd.{0} (HighamBench.P19Vector n)
                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                      gmresContribution matrixContribution)
                    remainder)) →
              (remainder_second_order :
                  HighamBench.P19FirstOrderSemantics.secondOrder semantics
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HighamBench.p19VecNorm2 n remainder)
                      (@HighamBench.p19VecNorm2 n
                        (@HighamBench.P19Theorem31System.xExact n
                          (@HighamBench.P19Theorem31Family.system n semantics
                            (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)))))) →
                (gmres_gain_bound :
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HighamBench.p19VecNorm2 n gmresContribution)
                        (@HighamBench.p19VecNorm2 n
                          (@HighamBench.P19Theorem31System.xExact n
                            (@HighamBench.P19Theorem31Family.system n semantics
                              (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics
                            (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                            (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                            (@HighamBench.P19StaticFlexibleIteration.core n semantics
                              (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                              (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                              (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)))
                          (@HighamBench.p19StaticRightOperatorKappa choice n semantics
                            (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                            (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible)))
                        (@HighamBench.p19StaticRightPreconditionerKappa choice n semantics
                          (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                          (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible)))) →
                  (matrix_gain_bound :
                      @LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HighamBench.p19VecNorm2 n matrixContribution)
                          (@HighamBench.p19VecNorm2 n
                            (@HighamBench.P19Theorem31System.xExact n
                              (@HighamBench.P19Theorem31Family.system n semantics
                                (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HighamBench.P19StaticFixedRightCore.matrixMagnitude n semantics
                              (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                              (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                              (@HighamBench.P19StaticFlexibleIteration.core n semantics
                                (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                                (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                                (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k)))
                            (@HighamBench.p19StaticSystemKappa choice n semantics
                              (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)))
                          (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics
                            (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                            (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                            (@HighamBench.P19StaticFlexibleIteration.core n semantics
                              (@HighamBench.P19StaticFlexibleFamily.family n semantics flexible)
                              (@HighamBench.P19StaticFlexibleFamily.preconditioner n semantics flexible) k
                              (@HighamBench.P19StaticFlexibleFamily.iteration n semantics flexible k))))) →
                    @HighamBench.P19StaticFlexibleAppendixDExpansion choice n semantics flexible k
```

### D119: `HighamBench.P19StaticRightAppendixCExpansion.mk`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `dec83b2bcce190dc8d99236513f01b0fcfa967640cfbf6b2cedd6b3064b9fa43`

Type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {right : HighamBench.P19StaticRightFamily n semantics} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (gmresContribution reapplicationContribution matrixContribution remainder : HighamBench.P19Vector n) →
            Eq (instHSub.hSub (right.family.iteration k).xHat right.family.system.xExact)
                (instHAdd.hAdd
                  (instHAdd.hAdd (instHAdd.hAdd gmresContribution reapplicationContribution) matrixContribution)
                  remainder) →
              semantics.secondOrder
                  (instHDiv.hDiv (HighamBench.p19VecNorm2 remainder)
                    (HighamBench.p19VecNorm2 right.family.system.xExact)) →
                Real.instLE.le
                    (instHDiv.hDiv (HighamBench.p19VecNorm2 gmresContribution)
                      (HighamBench.p19VecNorm2 right.family.system.xExact))
                    (instHMul.hMul
                      (instHMul.hMul (right.iteration k).core.gmresMagnitude
                        (HighamBench.p19StaticRightOperatorKappa choice right.preconditioner))
                      (HighamBench.p19StaticRightPreconditionerKappa choice right.preconditioner)) →
                  Real.instLE.le
                      (instHDiv.hDiv (HighamBench.p19VecNorm2 reapplicationContribution)
                        (HighamBench.p19VecNorm2 right.family.system.xExact))
                      (instHMul.hMul (right.iteration k).reapplicationMagnitude
                        (HighamBench.p19StaticRightPreconditionerKappa choice right.preconditioner)) →
                    Real.instLE.le
                        (instHDiv.hDiv (HighamBench.p19VecNorm2 matrixContribution)
                          (HighamBench.p19VecNorm2 right.family.system.xExact))
                        (instHMul.hMul
                          (instHMul.hMul (right.iteration k).core.matrixMagnitude
                            (HighamBench.p19StaticSystemKappa choice right.family))
                          (right.iteration k).core.rhoAR) →
                      HighamBench.P19StaticRightAppendixCExpansion choice right k
```

Fully explicit type:

```lean
{choice : HighamBench.P19StaticSquareKappaChoice} →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {right : HighamBench.P19StaticRightFamily n semantics} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (gmresContribution reapplicationContribution matrixContribution remainder : HighamBench.P19Vector n) →
            (error_decomposition :
                @Eq.{1} (HighamBench.P19Vector n)
                  (@HSub.hSub.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                    (@instHSub.{0} (HighamBench.P19Vector n)
                      (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
                    (@HighamBench.P19Algorithm2Iteration.xHat n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right))
                      semantics
                      (@HighamBench.P19Theorem31Family.basisFamily n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right))
                      k
                      (@HighamBench.P19Theorem31Family.iteration n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right) k))
                    (@HighamBench.P19Theorem31System.xExact n
                      (@HighamBench.P19Theorem31Family.system n semantics
                        (@HighamBench.P19StaticRightFamily.family n semantics right))))
                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                    (@instHAdd.{0} (HighamBench.P19Vector n)
                      (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                      (@instHAdd.{0} (HighamBench.P19Vector n)
                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P19Vector n) (HighamBench.P19Vector n)
                        (HighamBench.P19Vector n)
                        (@instHAdd.{0} (HighamBench.P19Vector n)
                          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                        gmresContribution reapplicationContribution)
                      matrixContribution)
                    remainder)) →
              (remainder_second_order :
                  HighamBench.P19FirstOrderSemantics.secondOrder semantics
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HighamBench.p19VecNorm2 n remainder)
                      (@HighamBench.p19VecNorm2 n
                        (@HighamBench.P19Theorem31System.xExact n
                          (@HighamBench.P19Theorem31Family.system n semantics
                            (@HighamBench.P19StaticRightFamily.family n semantics right)))))) →
                (gmres_gain_bound :
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HighamBench.p19VecNorm2 n gmresContribution)
                        (@HighamBench.p19VecNorm2 n
                          (@HighamBench.P19Theorem31System.xExact n
                            (@HighamBench.P19Theorem31Family.system n semantics
                              (@HighamBench.P19StaticRightFamily.family n semantics right)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HighamBench.P19StaticFixedRightCore.gmresMagnitude n semantics
                            (@HighamBench.P19StaticRightFamily.family n semantics right)
                            (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                            (@HighamBench.P19StaticRightIteration.core n semantics
                              (@HighamBench.P19StaticRightFamily.family n semantics right)
                              (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                              (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                          (@HighamBench.p19StaticRightOperatorKappa choice n semantics
                            (@HighamBench.P19StaticRightFamily.family n semantics right)
                            (@HighamBench.P19StaticRightFamily.preconditioner n semantics right)))
                        (@HighamBench.p19StaticRightPreconditionerKappa choice n semantics
                          (@HighamBench.P19StaticRightFamily.family n semantics right)
                          (@HighamBench.P19StaticRightFamily.preconditioner n semantics right)))) →
                  (reapplication_gain_bound :
                      @LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HighamBench.p19VecNorm2 n reapplicationContribution)
                          (@HighamBench.p19VecNorm2 n
                            (@HighamBench.P19Theorem31System.xExact n
                              (@HighamBench.P19Theorem31Family.system n semantics
                                (@HighamBench.P19StaticRightFamily.family n semantics right)))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HighamBench.P19StaticRightIteration.reapplicationMagnitude n semantics
                            (@HighamBench.P19StaticRightFamily.family n semantics right)
                            (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                            (@HighamBench.P19StaticRightFamily.iteration n semantics right k))
                          (@HighamBench.p19StaticRightPreconditionerKappa choice n semantics
                            (@HighamBench.P19StaticRightFamily.family n semantics right)
                            (@HighamBench.P19StaticRightFamily.preconditioner n semantics right)))) →
                    (matrix_gain_bound :
                        @LE.le.{0} Real Real.instLE
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HighamBench.p19VecNorm2 n matrixContribution)
                            (@HighamBench.p19VecNorm2 n
                              (@HighamBench.P19Theorem31System.xExact n
                                (@HighamBench.P19Theorem31Family.system n semantics
                                  (@HighamBench.P19StaticRightFamily.family n semantics right)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HighamBench.P19StaticFixedRightCore.matrixMagnitude n semantics
                                (@HighamBench.P19StaticRightFamily.family n semantics right)
                                (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                                (@HighamBench.P19StaticRightIteration.core n semantics
                                  (@HighamBench.P19StaticRightFamily.family n semantics right)
                                  (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                                  (@HighamBench.P19StaticRightFamily.iteration n semantics right k)))
                              (@HighamBench.p19StaticSystemKappa choice n semantics
                                (@HighamBench.P19StaticRightFamily.family n semantics right)))
                            (@HighamBench.P19StaticFixedRightCore.rhoAR n semantics
                              (@HighamBench.P19StaticRightFamily.family n semantics right)
                              (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                              (@HighamBench.P19StaticRightIteration.core n semantics
                                (@HighamBench.P19StaticRightFamily.family n semantics right)
                                (@HighamBench.P19StaticRightFamily.preconditioner n semantics right) k
                                (@HighamBench.P19StaticRightFamily.iteration n semantics right k))))) →
                      @HighamBench.P19StaticRightAppendixCExpansion choice n semantics right k
```

### D120: `HighamBench.P19StaticSquareKappaChoice.casesOn`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `db5b6b665da34fd4b2f2cfdd5c7b2ef00eb713f76f374592c931860a0ee13ab5`

Type:

```lean
{motive : HighamBench.P19StaticSquareKappaChoice → Sort u} →
  (t : HighamBench.P19StaticSquareKappaChoice) →
    motive HighamBench.P19StaticSquareKappaChoice.frobenius →
      motive HighamBench.P19StaticSquareKappaChoice.inducedTwo → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P19StaticSquareKappaChoice) → Sort u} →
  (t : HighamBench.P19StaticSquareKappaChoice) →
    (frobenius : motive HighamBench.P19StaticSquareKappaChoice.frobenius) →
      (inducedTwo : motive HighamBench.P19StaticSquareKappaChoice.inducedTwo) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t frobenius inducedTwo => HighamBench.P19StaticSquareKappaChoice.rec frobenius inducedTwo t
```

### D121: `HighamBench.p19Column`

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

### D122: `HighamBench.p19FullColumnRank`

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

### D123: `HighamBench.p19IsUpperHessenberg`

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

### D124: `HighamBench.p19OpNorm2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D125: `HighamBench.p19RectMatMul`

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

### D126: `HighamBench.p19ScaledFirstBasisVector`

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

### D127: `HighamBench.P19Algorithm2Iteration.computedB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `0a36228ab177e3d96350f260b42b0b39cdbb2e3af19df1b61a4bdbe4767eb7c1`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.10
```

### D128: `HighamBench.P19Algorithm2Iteration.leastSquaresDeltaB`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `09771da30686fc5e2cf381c4665caae33df2500d4d8fef9e37d1cf8a4130281b`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) → HighamBench.P19Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.20
```

### D129: `HighamBench.P19Algorithm2Iteration.leastSquaresDeltaC`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1474e23e024f85a3713cc0794a6573e2e4071d9d614f92fe14145947ab293054`

Type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : HighamBench.P19Theorem31BasisFamily system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19Algorithm2Iteration system semantics basisFamily k → HighamBench.P19RectMatrix n k.val
```

Fully explicit type:

```lean
{n : Nat} →
  {system : HighamBench.P19Theorem31System n} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {basisFamily : @HighamBench.P19Theorem31BasisFamily n system} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19Algorithm2Iteration n system semantics basisFamily k) →
            HighamBench.P19RectMatrix n
              (@Subtype.val.{1} Nat
                (fun (k : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                    (@LE.le.{0} Nat instLENat k n))
                k)
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.21
```

### D130: `HighamBench.P19FirstOrderSemantics.small`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1bc30297c5d6628f7a45cd5221fd0209542b9615afa5f93728f12b0e31dc32b5`

Type:

```lean
HighamBench.P19FirstOrderSemantics → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P19FirstOrderSemantics) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D131: `HighamBench.P19StaticFixedRightCore.basisPreconditionerMagnitude`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `3be4219195bebca31cbfaec9715d286b9adb4e354de2ccd68d15cad129666680`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.17
```

### D132: `HighamBench.P19StaticFixedRightCore.matrixDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `b66f88e8f2b37979a6cf8ac0604007746aa5a3ad0a7d9a915cf0d778e5f444e2`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFixedRightCore family preconditioner k → Fin k.val → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) →
            Fin
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k) →
              HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.9
```

### D133: `HighamBench.P19StaticFixedRightCore.matrixMagnitude`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bc8b23ced6076df849b4846f9edb6444c8d0f16683cd7ff75dd565a2147742ad`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} → HighamBench.P19StaticFixedRightCore family preconditioner k → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.18
```

### D134: `HighamBench.P19StaticFixedRightCore.preconditionerDelta`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `074af1cd613a8e30f1128a283b27720fed9a26a3f6414aa4a24a7a400215a951`

Type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : HighamBench.P19StaticFixedRightPreconditioner family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          HighamBench.P19StaticFixedRightCore family preconditioner k → Fin k.val → HighamBench.P19Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {semantics : HighamBench.P19FirstOrderSemantics} →
    {family : HighamBench.P19Theorem31Family n semantics} →
      {preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family} →
        {k : HighamBench.P19Theorem31Dimension n} →
          (self : @HighamBench.P19StaticFixedRightCore n semantics family preconditioner k) →
            Fin
                (@Subtype.val.{1} Nat
                  (fun (k : Nat) =>
                    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                      (@LE.le.{0} Nat instLENat k n))
                  k) →
              HighamBench.P19Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.7
```

### D135: `HighamBench.P19StaticSquareKappaChoice.rec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `recursor`
- Distance from target type: `5`
- Semantic SHA-256: `5eadb395765804172f60cffcf963e9e11b53ba0a106131d65ba628c848ca2cf5`

Type:

```lean
{motive : HighamBench.P19StaticSquareKappaChoice → Sort u} →
  motive HighamBench.P19StaticSquareKappaChoice.frobenius →
    motive HighamBench.P19StaticSquareKappaChoice.inducedTwo → (t : HighamBench.P19StaticSquareKappaChoice) → motive t
```

Fully explicit type:

```lean
{motive : (t : HighamBench.P19StaticSquareKappaChoice) → Sort u} →
  (frobenius : motive HighamBench.P19StaticSquareKappaChoice.frobenius) →
    (inducedTwo : motive HighamBench.P19StaticSquareKappaChoice.inducedTwo) →
      (t : HighamBench.P19StaticSquareKappaChoice) → motive t
```

### D136: `HighamBench.p19AbsRectMatVec`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D137: `HighamBench.p19IsLeastSquaresSolution`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D138: `HighamBench.p19StaticCondition316Value`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6c11ce8f32486a3c6e70c22d8f56aa5b74f2d37028a4a1c5593c73846e10d01d`

Type:

```lean
HighamBench.P19StaticSquareKappaChoice →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        HighamBench.P19StaticFixedRightPreconditioner family → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
(choice : HighamBench.P19StaticSquareKappaChoice) →
  {n : Nat} →
    {semantics : HighamBench.P19FirstOrderSemantics} →
      {family : HighamBench.P19Theorem31Family n semantics} →
        (preconditioner : @HighamBench.P19StaticFixedRightPreconditioner n semantics family) →
          (ug um ua etaR rhoAR : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug um ua etaR rhoAR =>
  Real.instMax.max (instHMul.hMul ug (HighamBench.p19StaticRightOperatorKappa choice preconditioner))
    (Real.instMax.max (instHMul.hMul ug (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner))
      (Real.instMax.max
        (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner))
        (Real.instMax.max (instHMul.hMul (instHMul.hMul ua (HighamBench.p19StaticSystemKappa choice family)) rhoAR)
          (instHMul.hMul (instHMul.hMul ua (HighamBench.p19StaticRightOperatorKappa choice preconditioner))
            (HighamBench.p19StaticRightPreconditionerKappa choice preconditioner)))))
```

### D139: `And`

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

### D140: `Eq`

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

### D141: `Exists`

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

### D142: `HAdd.hAdd`

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

### D143: `HMul.hMul`

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

### D144: `LE.le`

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

### D145: `LT.lt`

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

### D146: `Nat`

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

### D147: `OfNat.ofNat`

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

### D148: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D149: `Real`

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

### D150: `Real.instAdd`

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

### D151: `Real.instMul`

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

### D152: `Subtype.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `69c61ab82498e5563eaf5f0313ea7f2164c284c3dc742024a30332372a46663d`

Type:

```lean
{α : Sort u} → {p : α → Prop} → Subtype p → α
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (self : @Subtype.{u} α p) → α
```

Definition body (one-level semantic boundary):

```lean
fun α p self => self.1
```

### D153: `instHAdd`

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

### D154: `instHMul`

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

### D155: `instLENat`

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

### D156: `instLTNat`

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

### D157: `instOfNatNat`

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

### D158: `DivInvMonoid.toDiv`

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

### D159: `Fin`

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

### D160: `HDiv.hDiv`

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

### D161: `HSub.hSub`

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

### D162: `One.toOfNat1`

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

### D163: `Pi.instSub`

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

### D164: `Real.instAddGroup`

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

### D165: `Real.instDivInvMonoid`

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

### D166: `Real.instLE`

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

### D167: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D168: `Real.instNatCast`

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

### D169: `Real.instOne`

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

### D170: `Real.instSub`

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

### D171: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D172: `Real.lattice`

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

### D173: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Sort (max 1 u)
```

### D174: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D175: `abs`

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

### D176: `instAddNat`

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

### D177: `instHDiv`

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

### D178: `instHSub`

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

### D179: `instOfNatAtLeastTwo`

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

### D180: `And.intro`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `232593c5c388d46173a03223cb6b55ff2a132de1d4dfae47c09b5ba49b1e4f83`

Type:

```lean
∀ {a b : Prop}, a → b → And a b
```

Fully explicit type:

```lean
∀ {a b : Prop} (left : a) (right : b), And a b
```

### D181: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D182: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D183: `Iff.mpr`

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

### D184: `Matrix.frobeniusNormedAddCommGroup`

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

### D185: `Matrix.one`

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

### D186: `Nat.AtLeastTwo`

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

### D187: `Nat.le_of_lt`

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

### D188: `Nat.succ`

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

### D189: `Nat.succ_le_iff`

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

### D190: `Nat.succ_pos`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `0e7e3546875c3c758b7e9f771f5146afbe4374a7356e205021f87835237aeaa7`

Type:

```lean
∀ (n : Nat), instLTNat.lt 0 n.succ
```

Fully explicit type:

```lean
∀ (n : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.succ n)
```

### D191: `Nat.zero_lt_one`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7af00b6e71ddbd58776e8dc3a2c9845b1099ebd1b1c29b6b3d4e09c80c3bc1a7`

Type:

```lean
instLTNat.lt 0 1
```

Fully explicit type:

```lean
@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
```

### D192: `Ne`

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

### D193: `Norm.norm`

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

### D194: `NormedAddCommGroup.toNorm`

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

### D195: `Not`

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

### D196: `Real.normedAddCommGroup`

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

### D197: `Real.sqrt`

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

### D198: `Subtype.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `488ac61b6d3c07fb9a2f54a03a39e6001a4c7cedfd07515f0f9865e7fef9ef51`

Type:

```lean
{α : Sort u} → {p : α → Prop} → (val : α) → p val → Subtype p
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (val : α) → (property : p val) → @Subtype.{u} α p
```

### D199: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D200: `instDecidableEqFin`

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

### D201: `Fin.castSucc`

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

### D202: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D203: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D204: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D205: `Matrix`

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

### D206: `Matrix.add`

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

### D207: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D208: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D209: `Pi.instAdd`

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

### D210: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D211: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D212: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D213: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D214: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D215: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D216: `Function.Injective`

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

### D217: `Matrix.instL2OpNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.CStarAlgebra.Matrix`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D218: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D219: `instDecidableEqNat`

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

### D220: `ite`

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

### D221: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D222: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### `HighamBench.P19Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P19Definitions.lean`
SHA-256: `d1ee3760a4b34e9b845d1f5a65909aed6737cf7fb411c3607928aed8ed72ee27`

```lean
import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed

namespace HighamBench

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

/-- A finite square real matrix in the P19 model. -/
abbrev P19Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite rectangular real matrix in the P19 model. -/
abbrev P19RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

/-- A finite real vector in the P19 model. -/
abbrev P19Vector (n : ℕ) := Fin n → ℝ

/-- Paper-scoped squared Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Paper-scoped Euclidean norm for finite GMRES error vectors. -/
noncomputable def p19VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p19VecNorm2Sq x)

/-- Add two paper-scoped finite error vectors. -/
def p19Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

/-- Scale a paper-scoped finite error vector. -/
def p19Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

/-- Exact scalar envelope corresponding to `ξ` in equation (3.8). -/
def p19ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p19MatVec {n : ℕ} (A : P19Matrix n)
    (x : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Exact finite rectangular matrix-vector multiplication. -/
noncomputable def p19RectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

/-- Exact multiplication of a square matrix by a rectangular matrix. -/
noncomputable def p19SquareRectMul {n k : ℕ} (A : P19Matrix n)
    (B : P19RectMatrix n k) : P19RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

/-- Exact multiplication of two conforming rectangular matrices. -/
noncomputable def p19RectMatMul {m k q : ℕ} (A : P19RectMatrix m k)
    (B : P19RectMatrix k q) : P19RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

/-- The Frobenius norm used by the matrix perturbation models in (3.2)-(3.8). -/
noncomputable def p19FrobNorm {m k : ℕ} (A : P19RectMatrix m k) : ℝ :=
  ‖A‖

/-- A matrix column represented as a finite vector. -/
def p19Column {m k : ℕ} (A : P19RectMatrix m k) (j : Fin k) : P19Vector m :=
  fun i ↦ A i j

/-- Append a vector as the first column of a rectangular matrix. -/
noncomputable def p19Augment {n k : ℕ} (b : P19Vector n)
    (C : P19RectMatrix n k) : P19RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i) (fun j ↦ C i j)

/-- The vector `beta * e_1` in the MGS factorization (3.1). -/
def p19ScaledFirstBasisVector {k : ℕ} (beta : ℝ) : P19Vector (k + 1) :=
  fun i ↦ if i.val = 0 then beta else 0

/-- The structural upper-Hessenberg condition on the MGS factor. -/
def p19IsUpperHessenberg {k : ℕ}
    (H : P19RectMatrix (k + 1) k) : Prop :=
  ∀ i j, j.val + 1 < i.val → H i j = 0

/-- Two square matrices are certified inverses through their exact actions. -/
def p19InversePair {n : ℕ} (A Ainv : P19Matrix n) : Prop :=
  (∀ x : P19Vector n, p19MatVec Ainv (p19MatVec A x) = x) ∧
    ∀ x : P19Vector n, p19MatVec A (p19MatVec Ainv x) = x

/-- Exact least-squares optimality for line 3 of Algorithm 2. -/
def p19IsLeastSquaresSolution {m k : ℕ} (A : P19RectMatrix m k)
    (b : P19Vector m) (y : P19Vector k) : Prop :=
  ∀ z : P19Vector k,
    p19VecNorm2 (b - p19RectMatVec A y) ≤
      p19VecNorm2 (b - p19RectMatVec A z)

/-- A rectangular matrix has full column rank when its exact action is injective. -/
def p19FullColumnRank {m k : ℕ} (A : P19RectMatrix m k) : Prop :=
  Function.Injective (p19RectMatVec A)

/-- Certified extremal singular values for a finite real matrix. The gain and
attainment clauses give the exact Euclidean meanings of `sigma_min` and
`sigma_max` without depending on a particular SVD implementation. -/
structure P19SingularValueData {m k : ℕ} (A : P19RectMatrix m k) where
  sigmaMin : ℝ
  sigmaMax : ℝ
  sigmaMin_nonneg : 0 ≤ sigmaMin
  sigmaMax_nonneg : 0 ≤ sigmaMax
  lower_gain : ∀ x : P19Vector k,
    sigmaMin * p19VecNorm2 x ≤ p19VecNorm2 (p19RectMatVec A x)
  upper_gain : ∀ x : P19Vector k,
    p19VecNorm2 (p19RectMatVec A x) ≤ sigmaMax * p19VecNorm2 x
  min_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMin
  max_attained : 0 < k → ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧ p19VecNorm2 (p19RectMatVec A x) = sigmaMax

/-- One explicit nonnegative low-degree polynomial represented by `c(n,k)`. -/
structure P19PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

/-- Evaluation of the recorded low-degree polynomial factor. -/
noncomputable def p19PolynomialFactorValue (c : P19PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

/-- A scalar remainder that is second order in the combined precision scale. -/
def p19SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise version of the paper's `lesssim`: an inequality modulo an
otherwise unspecified second-order remainder. -/
def p19FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p19SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The paper's qualitative `theta << 1` along a precision regime. -/
def p19MuchLessThanOneAt {ι : Type*} (l : Filter ι)
    (theta : ι → ℝ) : Prop :=
  Filter.Tendsto theta l (nhds 0) ∧
    ∀ᶠ t in l, 0 ≤ theta t ∧ theta t < 1

/-- An increasing family of full-rank search bases. Successive members agree
on all previously present columns. -/
structure P19IncreasingBasisFamily (n : ℕ) (ι : Type*) where
  basis : (k : ℕ) → ι → P19RectMatrix n k
  full_rank : ∀ (k : ℕ), k ≤ n → ∀ (t : ι), p19FullColumnRank (basis k t)
  column_prefix : ∀ (k : ℕ) (t : ι) (i : Fin n) (j : Fin k), k < n →
    basis k t i j = basis (k + 1) t i j.castSucc

/-- Frobenius-to-smallest-singular-value condition measure for a rectangular
matrix. This is the paper's `kappa_F,2` interpretation of an unqualified
rectangular `kappa`. -/
noncomputable def p19RectConditionF2 {m k : ℕ}
    (A : P19RectMatrix m k) (sigmaMin : ℝ) : ℝ :=
  p19FrobNorm A / sigmaMin

/-- Frobenius condition number represented using a certified inverse. -/
noncomputable def p19ConditionNumberF {n : ℕ}
    (A Ainv : P19Matrix n) : ℝ :=
  p19FrobNorm Ainv * p19FrobNorm A

/-- One precision-parametrized execution of Algorithm 2 at the key dimension
selected by the MGS analysis used in Theorem 3.1. The fields through
`solution_small` are precisely the four modules (3.2)-(3.6). The final defect
fields record the near-orthogonality estimate recalled from the MGS analysis;
they do not assume either displayed `4/3` conclusion. -/
structure P19ModularGMRESRun {n : ℕ} {ι : Type*} (l : Filter ι) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  basisFamily : P19IncreasingBasisFamily n ι
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  epsilonC : ι → ℝ
  epsilonB : ι → ℝ
  ug : ι → ℝ
  epsilonX : ι → ℝ
  accuracy_nonneg : ∀ t,
    0 ≤ epsilonC t ∧ 0 ≤ epsilonB t ∧ 0 ≤ ug t ∧ 0 ≤ epsilonX t
  accuracy_tendsto_zero :
    Filter.Tendsto epsilonC l (nhds 0) ∧
      Filter.Tendsto epsilonB l (nhds 0) ∧
      Filter.Tendsto ug l (nhds 0) ∧
      Filter.Tendsto epsilonX l (nhds 0)
  computedC : ι → P19RectMatrix n keyDimension
  deltaC : ι → P19RectMatrix n keyDimension
  computation_equation : ∀ t,
    computedC t =
      p19SquareRectMul MLinv
          (p19SquareRectMul A (basisFamily.basis keyDimension t)) +
        deltaC t
  computation_error_bound : ∀ t,
    p19FrobNorm (deltaC t) ≤
      epsilonC t *
        p19FrobNorm
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  computedB : ι → P19Vector n
  deltaB : ι → P19Vector n
  rhs_equation : ∀ t,
    computedB t = p19MatVec MLinv b + deltaB t
  rhs_error_bound : ∀ t,
    p19VecNorm2 (deltaB t) ≤ epsilonB t * p19VecNorm2 (p19MatVec MLinv b)
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_givens_relation : ∀ t,
    p19Augment (computedB t) (computedC t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedC t + leastSquaresDeltaC t)
      (computedB t + leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column (p19Augment (computedB t) (computedC t)) j)
  computedCSpectrum : ∀ t, P19SingularValueData (computedC t)
  computedC_numerically_nonsingular :
    p19MuchLessThanOneAt l (fun t ↦
      ug t *
        p19RectConditionF2 (computedC t)
          (computedCSpectrum t).sigmaMin)
  exactCSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MLinv
        (p19SquareRectMul A (basisFamily.basis keyDimension t)))
  combined_model_small :
    p19MuchLessThanOneAt l (fun t ↦
      (epsilonC t + epsilonB t + ug t) *
        p19RectConditionF2
          (p19SquareRectMul MLinv
            (p19SquareRectMul A (basisFamily.basis keyDimension t)))
          (exactCSpectrum t).sigmaMin)
  xHat : ι → P19Vector n
  deltaX : ι → P19Vector n
  solution_equation : ∀ t,
    xHat t = p19RectMatVec (basisFamily.basis keyDimension t) (yHat t) + deltaX t
  solution_error_bound : ∀ t,
    p19VecNorm2 (deltaX t) ≤
      epsilonX t *
        p19VecNorm2
          (p19RectMatVec (basisFamily.basis keyDimension t) (yHat t))
  solution_small : p19MuchLessThanOneAt l epsilonX
  vHatSpectrum : ∀ t, P19SingularValueData (vHat t)
  mgsOrthogonalityDefect : ι → ℝ
  mgs_defect_nonneg : ∀ t, 0 ≤ mgsOrthogonalityDefect t
  mgs_defect_small : ∀ᶠ t in l, mgsOrthogonalityDefect t ≤ 7 / 16
  mgs_sigmaMin_sq_lower : ∀ t,
    1 - mgsOrthogonalityDefect t ≤ (vHatSpectrum t).sigmaMin ^ 2
  mgs_sigmaMax_sq_upper : ∀ t,
    (vHatSpectrum t).sigmaMax ^ 2 ≤ 1 + mgsOrthogonalityDefect t

/-- The combined precision scale used to classify the omitted second-order
terms in Theorem 3.1. -/
noncomputable def p19PrecisionScale {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ run.epsilonC t + run.epsilonB t + run.ug t + run.epsilonX t

/-- The exact left-preconditioned basis product in (3.2). -/
noncomputable def p19ExactC {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (t : ι) :
    P19RectMatrix n run.keyDimension :=
  p19SquareRectMul run.MLinv
    (p19SquareRectMul run.A (run.basisFamily.basis run.keyDimension t))

/-- The split-preconditioned operator `M_L^{-1} A M_R^{-1}`. -/
noncomputable def p19SplitOperator {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul run.MLinv (p19SquareRectMul run.A MRinv)

/-- Its certified inverse `M_R A^{-1} M_L`. -/
noncomputable def p19SplitInverse {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul run.Ainv run.ML)

/-- The normalized forward error (2.1). -/
noncomputable def p19ForwardError {n : ℕ}
    (x xHat : P19Vector n) : ℝ :=
  p19VecNorm2 (xHat - x) / p19VecNorm2 x

/-- Exact singular-value data needed to instantiate `alpha` and `beta` for one
arbitrary nonsingular analytical right preconditioner. -/
structure P19RightPreconditionedQuantities {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum : ∀ t,
    P19SingularValueData
      (p19SquareRectMul MR
        (run.basisFamily.basis run.keyDimension t))
  mrz_sigmaMin_pos : ∀ t, 0 < (mrzSpectrum t).sigmaMin

/-- The coefficient `alpha` below equation (3.8). -/
noncomputable def p19Alpha {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  (p19ConditionNumberF MR MRinv / (q.mrzSpectrum t).sigmaMin) *
    (p19FrobNorm (p19ExactC run t) /
      p19FrobNorm (p19SplitOperator run MRinv))

/-- The coefficient `beta` below equation (3.8). -/
noncomputable def p19Beta {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  max 1
      ((p19FrobNorm (p19ExactC run t) /
          p19FrobNorm (p19SplitOperator run MRinv)) /
        (q.mrzSpectrum t).sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- The coefficient `lambda` below equation (3.8). -/
noncomputable def p19Lambda {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19SplitOperator run MRinv) (p19SplitInverse run MR)

/-- The exact four-source quantity `xi` in equation (3.8). -/
noncomputable def p19Xi {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n)
    (q : P19RightPreconditionedQuantities run MR MRinv) (t : ι) : ℝ :=
  p19ModularEnvelope (p19Alpha run MR MRinv q t)
    (p19Beta run MR MRinv q t) (p19Lambda run MR MRinv)
    (run.epsilonC t) (run.epsilonB t) (run.ug t) (run.epsilonX t)

/-- Appendix-A propagation certificate for the four heterogeneous Algorithm 2
errors. Each contribution is formally tied to its source perturbation; their
sum, rather than the final forward-error inequality, is recorded. -/
structure P19ForwardAnalysis {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P19ModularGMRESRun (n := n) l)
    (MR MRinv : P19Matrix n) where
  quantities : P19RightPreconditionedQuantities run MR MRinv
  computationPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  rhsPropagation : ι → P19Vector n → P19Vector n
  leastSquaresBPropagation : ι → P19Vector n → P19Vector n
  leastSquaresCPropagation : ι →
    P19RectMatrix n run.keyDimension → P19Vector n
  solutionPropagation : ι → P19Vector n → P19Vector n
  computationContribution : ι → P19Vector n
  rhsContribution : ι → P19Vector n
  gmresContribution : ι → P19Vector n
  solutionContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  computation_link : ∀ t,
    computationContribution t = computationPropagation t (run.deltaC t)
  rhs_link : ∀ t, rhsContribution t = rhsPropagation t (run.deltaB t)
  gmres_link : ∀ t,
    gmresContribution t =
      leastSquaresBPropagation t (run.leastSquaresDeltaB t) +
        leastSquaresCPropagation t (run.leastSquaresDeltaC t)
  solution_link : ∀ t,
    solutionContribution t = solutionPropagation t (run.deltaX t)
  computationPropagation_zero : ∀ t, computationPropagation t 0 = 0
  rhsPropagation_zero : ∀ t, rhsPropagation t 0 = 0
  leastSquaresBPropagation_zero : ∀ t, leastSquaresBPropagation t 0 = 0
  leastSquaresCPropagation_zero : ∀ t, leastSquaresCPropagation t 0 = 0
  solutionPropagation_zero : ∀ t, solutionPropagation t 0 = 0
  error_decomposition : ∀ t,
    run.xHat t - run.xExact =
      computationContribution t + rhsContribution t + gmresContribution t +
        solutionContribution t + remainder t
  computation_bound : ∀ t,
    p19VecNorm2 (computationContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Alpha run MR MRinv quantities t * run.epsilonC t)
  rhs_bound : ∀ t,
    p19VecNorm2 (rhsContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.epsilonB t)
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Beta run MR MRinv quantities t * run.ug t)
  solution_bound : ∀ t,
    p19VecNorm2 (solutionContribution t) / p19VecNorm2 run.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        p19ConditionNumberF
          (p19SplitOperator run MRinv) (p19SplitInverse run MR) *
        (p19Lambda run MR MRinv * run.epsilonX t)
  remainder_second_order :
    p19SecondOrderAt l (p19PrecisionScale run)
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 run.xExact)

/-- A complete proof-carrying execution of the hypotheses and intermediate
Appendix-A propagation used by Theorem 3.1. -/
structure P19Theorem31Execution {n : ℕ} {ι : Type*} (l : Filter ι) where
  run : P19ModularGMRESRun (n := n) l
  forwardAnalysis : ∀ (MR MRinv : P19Matrix n),
    p19InversePair MR MRinv → P19ForwardAnalysis run MR MRinv

/-- Static semantics for the source's qualitative first-order notation. The
paper deliberately supplies neither a limiting parameter nor a numerical
smallness threshold, so both predicates remain part of the interpretation. -/
structure P19FirstOrderSemantics where
  small : ℝ → Prop
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

/-- The source relation `lhs lesssim rhs`: an exact inequality after retaining
one term classified as negligible and second order by the chosen semantics. -/
def p19FirstOrderLe (semantics : P19FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

/-- A ratio that remains defined when its reference magnitude is zero. Source
error inequalities force the numerator to vanish in that case. -/
noncomputable def p19SafeRelativeMagnitude (actual reference : ℝ) : ℝ :=
  if reference = 0 then 0 else actual / reference

/-- A dimension admitted by Theorem 3.1. -/
abbrev P19Theorem31Dimension (n : ℕ) :=
  {k : ℕ // 0 < k ∧ k ≤ n}

/-- Static nonsingular linear-system data shared by all Algorithm 2
dimensions. -/
structure P19Theorem31System (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  ML : P19Matrix n
  MLinv : P19Matrix n
  b : P19Vector n
  xExact : P19Vector n
  A_inverse : p19InversePair A Ainv
  ML_inverse : p19InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b

/-- The increasing full-rank search-space input from Theorem 3.1. -/
structure P19Theorem31BasisFamily {n : ℕ}
    (system : P19Theorem31System n) where
  basis : (k : ℕ) → P19RectMatrix n k
  full_rank : ∀ k, 0 < k → k ≤ n → p19FullColumnRank (basis k)
  column_prefix : ∀ k, k < n → ∀ i (j : Fin k),
    basis k i j = basis (k + 1) i j.castSucc

/-- Exact left-preconditioned basis product in equation (3.2). -/
noncomputable def p19StaticExactC {n k : ℕ}
    (system : P19Theorem31System n) (Z : P19RectMatrix n k) :
    P19RectMatrix n k :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A Z)

/-- Exact left-preconditioned right-hand side in equation (3.3). -/
noncomputable def p19StaticExactB {n : ℕ}
    (system : P19Theorem31System n) : P19Vector n :=
  p19MatVec system.MLinv system.b

/-- One fixed-precision execution of all four modules of Algorithm 2 at one
positive dimension. No selected key dimension or final error bound is stored. -/
structure P19Algorithm2Iteration {n : ℕ}
    (system : P19Theorem31System n)
    (semantics : P19FirstOrderSemantics)
    (basisFamily : P19Theorem31BasisFamily system)
    (k : P19Theorem31Dimension n) where
  dimensionFactor : ℝ
  dimensionFactor_one_le : 1 ≤ dimensionFactor
  epsilonC : ℝ
  epsilonB : ℝ
  ug : ℝ
  epsilonX : ℝ
  computedC : P19RectMatrix n k.1
  deltaC : P19RectMatrix n k.1
  computation_equation :
    computedC = p19StaticExactC system (basisFamily.basis k.1) + deltaC
  computedB : P19Vector n
  deltaB : P19Vector n
  rhs_equation : computedB = p19StaticExactB system + deltaB
  vHat : P19RectMatrix n k.1
  vHatNext : P19RectMatrix n (k.1 + 1)
  beta : ℝ
  hessenberg : P19RectMatrix (k.1 + 1) k.1
  hessenberg_upper : p19IsUpperHessenberg hessenberg
  mgs_givens_relation :
    p19Augment computedB computedC =
      p19RectMatMul vHatNext
        (p19Augment (p19ScaledFirstBasisVector beta) hessenberg)
  vHat_prefix : ∀ i (j : Fin k.1),
    vHat i j = vHatNext i j.castSucc
  leastSquaresDeltaB : P19Vector n
  leastSquaresDeltaC : P19RectMatrix n k.1
  yHat : P19Vector k.1
  computedCSpectrum : P19SingularValueData computedC
  exactCSpectrum :
    P19SingularValueData
      (p19StaticExactC system (basisFamily.basis k.1))
  xHat : P19Vector n
  deltaX : P19Vector n
  solution_equation :
    xHat = p19RectMatVec (basisFamily.basis k.1) yHat + deltaX
  vHatSpectrum : P19SingularValueData vHat

/-- Equations (3.2)-(3.6) and the MGS/Givens least-squares model at one
specific Algorithm 2 dimension. Theorem 3.1 requires these only at the
dimension selected by the MGS argument. -/
structure P19Algorithm2Conditions {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) where
  accuracy_nonneg :
    0 ≤ iteration.epsilonC ∧ 0 ≤ iteration.epsilonB ∧
      0 ≤ iteration.ug ∧ 0 ≤ iteration.epsilonX
  computation_error_bound :
    p19FrobNorm iteration.deltaC ≤
      iteration.epsilonC *
        p19FrobNorm (p19StaticExactC system (basisFamily.basis k.1))
  rhs_error_bound :
    p19VecNorm2 iteration.deltaB ≤
      iteration.epsilonB * p19VecNorm2 (p19StaticExactB system)
  least_squares_solution :
    p19IsLeastSquaresSolution
      (iteration.computedC + iteration.leastSquaresDeltaC)
      (iteration.computedB + iteration.leastSquaresDeltaB) iteration.yHat
  least_squares_column_bound : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment iteration.leastSquaresDeltaB
            iteration.leastSquaresDeltaC) j) ≤
      iteration.dimensionFactor * iteration.ug *
        p19VecNorm2
          (p19Column
            (p19Augment iteration.computedB iteration.computedC) j)
  computedC_numerically_nonsingular :
    semantics.small
      (iteration.ug *
        p19RectConditionF2 iteration.computedC
          iteration.computedCSpectrum.sigmaMin)
  combined_model_small :
    semantics.small
      ((iteration.epsilonC + iteration.epsilonB + iteration.ug) *
        p19RectConditionF2
          (p19StaticExactC system (basisFamily.basis k.1))
          iteration.exactCSpectrum.sigmaMin)
  solution_error_bound :
    p19VecNorm2 iteration.deltaX ≤
      iteration.epsilonX *
        p19VecNorm2 (p19RectMatVec (basisFamily.basis k.1) iteration.yHat)
  solution_small : semantics.small iteration.epsilonX

/-- The two explicit conditioning inequalities in equation (3.7). -/
def p19IterationWellConditioned {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  1 / iteration.vHatSpectrum.sigmaMin ≤ 4 / 3 ∧
    iteration.vHatSpectrum.sigmaMax ≤ 4 / 3

/-- Witness form of an upper bound on the smallest singular value. -/
def p19NearRankDeficient {m k : ℕ} (A : P19RectMatrix m k)
    (threshold : ℝ) : Prop :=
  ∃ x : P19Vector k,
    p19VecNorm2 x = 1 ∧
      p19VecNorm2 (p19RectMatVec A x) < threshold

/-- The input-near-dependence alternative (A.1), required only before the
full dimension. -/
def p19MGSNearDependence {n : ℕ}
    {system : P19Theorem31System n}
    {semantics : P19FirstOrderSemantics}
    {basisFamily : P19Theorem31BasisFamily system}
    {k : P19Theorem31Dimension n}
    (iteration : P19Algorithm2Iteration system semantics basisFamily k) : Prop :=
  ∀ phi : ℝ, 0 < phi →
    p19NearRankDeficient
      (p19Augment
        (fun i ↦ p19StaticExactB system i * phi)
        (p19StaticExactC system (basisFamily.basis k.1)))
      (iteration.dimensionFactor * (iteration.ug + iteration.epsilonC) *
        p19FrobNorm
          (p19Augment
            (fun i ↦ p19StaticExactB system i * phi)
            (p19StaticExactC system (basisFamily.basis k.1))))

/-- Static Algorithm 2 executions at every increasing dimension. -/
structure P19Theorem31Family (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  system : P19Theorem31System n
  basisFamily : P19Theorem31BasisFamily system
  iteration : ∀ k : P19Theorem31Dimension n,
    P19Algorithm2Iteration system semantics basisFamily k

/-- The reusable MGS result invoked through [11, equations (5.15)-(5.17)] and
the Paige MGS analysis: the first basis is well conditioned, and loss at the
next dimension forces (A.1) for the current input. It contains no selected
dimension. -/
structure P19MGSSelectionLaw {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  first_dimension_good :
    p19IterationWellConditioned
      (family.iteration
        ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩)
  loss_implies_near_dependence : ∀ (k : ℕ)
      (hkpos : 0 < k) (hklt : k < n),
    let current : P19Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    let next : P19Theorem31Dimension n :=
      ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
    ¬ p19IterationWellConditioned (family.iteration next) →
      p19MGSNearDependence (family.iteration current)

/-- The split-preconditioned operator for the static Theorem 3.1 model. -/
noncomputable def p19StaticSplitOperator {n : ℕ}
    (system : P19Theorem31System n) (MRinv : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul system.MLinv (p19SquareRectMul system.A MRinv)

/-- A certified inverse of the static split-preconditioned operator. -/
noncomputable def p19StaticSplitInverse {n : ℕ}
    (system : P19Theorem31System n) (MR : P19Matrix n) :
    P19Matrix n :=
  p19SquareRectMul MR (p19SquareRectMul system.Ainv system.ML)

/-- Singular-value and positivity evidence used to interpret the displayed
`alpha`, `beta`, and `lambda` for one analytical right preconditioner. -/
structure P19StaticRightQuantities {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n) where
  mrzSpectrum :
    P19SingularValueData
      (p19SquareRectMul MR (family.basisFamily.basis k.1))
  mrz_sigmaMin_pos : 0 < mrzSpectrum.sigmaMin
  exactC_norm_pos :
    0 < p19FrobNorm
      (p19StaticExactC family.system (family.basisFamily.basis k.1))
  split_operator_norm_pos :
    0 < p19FrobNorm (p19StaticSplitOperator family.system MRinv)
  mr_condition_pos : 0 < p19ConditionNumberF MR MRinv
  split_condition_pos :
    0 < p19ConditionNumberF
      (p19StaticSplitOperator family.system MRinv)
      (p19StaticSplitInverse family.system MR)

/-- `alpha` below equation (3.8), with the paper-authorized Frobenius
interpretation of unqualified square condition numbers. -/
noncomputable def p19StaticAlpha {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  (p19ConditionNumberF MR MRinv / q.mrzSpectrum.sigmaMin) *
    (p19FrobNorm
        (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
      p19FrobNorm (p19StaticSplitOperator family.system MRinv))

/-- `beta` below equation (3.8). -/
noncomputable def p19StaticBeta {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  max 1
      ((p19FrobNorm
          (p19StaticExactC family.system (family.basisFamily.basis k.1)) /
          p19FrobNorm (p19StaticSplitOperator family.system MRinv)) /
        q.mrzSpectrum.sigmaMin) *
    p19ConditionNumberF MR MRinv

/-- `lambda` below equation (3.8). -/
noncomputable def p19StaticLambda {n : ℕ}
    (system : P19Theorem31System n) (MR MRinv : P19Matrix n) : ℝ :=
  1 /
    p19ConditionNumberF
      (p19StaticSplitOperator system MRinv)
      (p19StaticSplitInverse system MR)

/-- The exact four-source coefficient `xi` in equation (3.8). -/
noncomputable def p19StaticXi {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {k : P19Theorem31Dimension n}
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) : ℝ :=
  let run := family.iteration k
  p19ModularEnvelope (p19StaticAlpha MR MRinv q)
    (p19StaticBeta MR MRinv q)
    (p19StaticLambda family.system MR MRinv)
    run.epsilonC run.epsilonB run.ug run.epsilonX

/-- Raw Appendix-A first-order expansion. Its gain bounds are expressed in
terms of the actual module-relative errors. In particular, none of the four
source epsilons and no final Theorem 3.1 inequality is stored here. -/
structure P19StaticAppendixAExpansion {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (k : P19Theorem31Dimension n)
    (MR MRinv : P19Matrix n)
    (q : P19StaticRightQuantities family k MR MRinv) where
  computationContribution : P19Vector n
  rhsContribution : P19Vector n
  gmresContribution : P19Vector n
  solutionContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (family.iteration k).xHat - family.system.xExact =
      computationContribution + rhsContribution + gmresContribution +
        solutionContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 family.system.xExact)
  computation_gain_bound :
    p19VecNorm2 computationContribution /
          p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticAlpha MR MRinv q *
          p19SafeRelativeMagnitude
            (p19FrobNorm (family.iteration k).deltaC)
            (p19FrobNorm
              (p19StaticExactC family.system
                (family.basisFamily.basis k.1))))
  rhs_gain_bound :
    p19VecNorm2 rhsContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaB)
            (p19VecNorm2 (p19StaticExactB family.system)))
  gmres_gain_bound :
    p19VecNorm2 gmresContribution / p19VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticBeta MR MRinv q * (family.iteration k).ug)
  solution_gain_bound :
    p19VecNorm2 solutionContribution /
          p19VecNorm2 family.system.xExact ≤
      p19ConditionNumberF
          (p19StaticSplitOperator family.system MRinv)
          (p19StaticSplitInverse family.system MR) *
        (p19StaticLambda family.system MR MRinv *
          p19SafeRelativeMagnitude
            (p19VecNorm2 (family.iteration k).deltaX)
            (p19VecNorm2
              (p19RectMatVec (family.basisFamily.basis k.1)
                (family.iteration k).yHat)))

/-- The reusable Appendix-A analysis invoked by Theorem 3.1. It is uniform in
the dimension and right preconditioner and supplies only the raw expansion
above, not a selected dimension or the theorem's collected bound. -/
structure P19StaticAppendixATheory {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  rightQuantities : ∀ (k : P19Theorem31Dimension n)
      (MR MRinv : P19Matrix n), p19InversePair MR MRinv →
    P19StaticRightQuantities family k MR MRinv
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) →
    P19Algorithm2Conditions (family.iteration k) →
    ∀ (MR MRinv : P19Matrix n) (hMR : p19InversePair MR MRinv),
      P19StaticAppendixAExpansion family k MR MRinv
        (rightQuantities k MR MRinv hMR)

/-- Paper-scoped exact matrix operator 2-norm. -/
noncomputable def p19OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

/-- Paper-scoped condition-number product for a matrix and inverse candidate. -/
noncomputable def p19Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p19OpNorm2 A * p19OpNorm2 Ainv

/-- The initial residual used when Algorithm 1 is read as Algorithm 2 applied
to the correction equation. -/
noncomputable def p19InitialResidual {n : ℕ} (A : P19Matrix n)
    (b xInitial : P19Vector n) : P19Vector n :=
  b - p19MatVec A xInitial

/-- Componentwise absolute matrix-vector product from equation (3.15). -/
noncomputable def p19AbsRectMatVec {m k : ℕ} (A : P19RectMatrix m k)
    (x : P19Vector k) : P19Vector m :=
  fun i ↦ ∑ j : Fin k, |A i j| * |x j|

/-- A nonsingular system with one fixed, nonsingular, nonidentity right
preconditioner. The product-inverse certificate prevents condition numbers
from being formed from unrelated matrices. -/
structure P19FixedRightSystem (n : ℕ) where
  dimension_pos : 0 < n
  A : P19Matrix n
  Ainv : P19Matrix n
  MR : P19Matrix n
  MRinv : P19Matrix n
  A_inverse : p19InversePair A Ainv
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul A MRinv) (p19SquareRectMul MR Ainv)
  right_preconditioner_nontrivial : MR ≠ 1
  b : P19Vector n
  xExact : P19Vector n
  xInitial : P19Vector n
  b_nonzero : b ≠ 0
  exact_solution : p19MatVec A xExact = b
  initial_residual_nonzero : p19InitialResidual A b xInitial ≠ 0

/-- The actual right-preconditioned operator `A M_R^{-1}`. -/
noncomputable def p19RightOperator {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.A system.MRinv

/-- The certified inverse `M_R A^{-1}` of the right-preconditioned operator. -/
noncomputable def p19RightOperatorInverse {n : ℕ}
    (system : P19FixedRightSystem n) : P19Matrix n :=
  p19SquareRectMul system.MR system.Ainv

/-- Induced-2 condition number of `A M_R^{-1}`. -/
noncomputable def p19RightOperatorKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 (p19RightOperator system) (p19RightOperatorInverse system)

/-- Induced-2 condition number of the fixed right preconditioner. -/
noncomputable def p19RightPreconditionerKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.MR system.MRinv

/-- Induced-2 condition number of the original system matrix. -/
noncomputable def p19SystemKappa2 {n : ℕ}
    (system : P19FixedRightSystem n) : ℝ :=
  p19Kappa2 system.A system.Ainv

/-- The five-term maximum in condition (3.16). -/
noncomputable def p19Condition316Value {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19RightOperatorKappa2 system)
    (max (ug * p19RightPreconditionerKappa2 system)
      (max (um * etaR * p19RightPreconditionerKappa2 system)
        (max (ua * p19SystemKappa2 system * rhoAR)
          (ua * p19RightOperatorKappa2 system *
            p19RightPreconditionerKappa2 system))))

/-- The three first-order sources in the right-preconditioned bound (3.17). -/
noncomputable def p19RightAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    um * etaR * p19RightPreconditionerKappa2 system +
      ua * p19SystemKappa2 system * rhoAR

/-- The two first-order sources in the flexible-preconditioned bound (3.20). -/
noncomputable def p19FlexibleAttainableEnvelope {n : ℕ}
    (system : P19FixedRightSystem n)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19RightOperatorKappa2 system *
      p19RightPreconditionerKappa2 system +
    ua * p19SystemKappa2 system * rhoAR

/-- A computed right-preconditioned MGS-GMRES transcript through the least-
squares stage. It records (3.14), the products with `A`, equation (3.15), and
the complete condition (3.16). -/
structure P19FixedRightGMRESRun {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  polynomialFactor : P19PolynomialFactor
  ug : ι → ℝ
  um : ι → ℝ
  ua : ι → ℝ
  etaR : ι → ℝ
  rhoAR : ι → ℝ
  parameters_nonneg : ∀ t,
    0 ≤ ug t ∧ 0 ≤ um t ∧ 0 ≤ ua t ∧ 0 ≤ etaR t ∧ 0 ≤ rhoAR t
  vHat : ι → P19RectMatrix n keyDimension
  vHatNext : ι → P19RectMatrix n (keyDimension + 1)
  zHat : ι → P19RectMatrix n keyDimension
  computedAZ : ι → P19RectMatrix n keyDimension
  beta : ι → ℝ
  hessenberg : ι → P19RectMatrix (keyDimension + 1) keyDimension
  hessenberg_upper : ∀ t, p19IsUpperHessenberg (hessenberg t)
  mgs_relation : ∀ t,
    p19Augment (p19InitialResidual system.A system.b system.xInitial)
        (computedAZ t) =
      p19RectMatMul (vHatNext t)
        (p19Augment (p19ScaledFirstBasisVector (beta t)) (hessenberg t))
  vHat_prefix : ∀ t i (j : Fin keyDimension),
    vHat t i j = vHatNext t i j.castSucc
  leastSquaresDeltaB : ι → P19Vector n
  leastSquaresDeltaC : ι → P19RectMatrix n keyDimension
  yHat : ι → P19Vector keyDimension
  least_squares_solution : ∀ t,
    p19IsLeastSquaresSolution
      (computedAZ t + leastSquaresDeltaC t)
      (p19InitialResidual system.A system.b system.xInitial +
        leastSquaresDeltaB t) (yHat t)
  least_squares_column_bound : ∀ t (j : Fin (keyDimension + 1)),
    p19VecNorm2
        (p19Column
          (p19Augment (leastSquaresDeltaB t) (leastSquaresDeltaC t)) j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension * ug t *
        p19VecNorm2
          (p19Column
            (p19Augment
              (p19InitialResidual system.A system.b system.xInitial)
              (computedAZ t)) j)
  zHat_full_rank : ∀ t, p19FullColumnRank (zHat t)
  preconditionerDelta : ι → Fin keyDimension → P19Matrix n
  preconditioner_application : ∀ t j,
    p19Column (zHat t) j =
      p19MatVec (system.MRinv + preconditionerDelta t j)
        (p19Column (vHat t) j)
  preconditioner_error_bound : ∀ t j,
    p19FrobNorm (preconditionerDelta t j) ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        um t * etaR t * p19FrobNorm system.MRinv
  matrixDelta : ι → Fin keyDimension → P19Matrix n
  matrix_application : ∀ t j,
    p19Column (computedAZ t) j =
      p19MatVec (system.A + matrixDelta t j) (p19Column (zHat t) j)
  matrix_error_bound : ∀ t j i q,
    |matrixDelta t j i q| ≤
      p19PolynomialFactorValue polynomialFactor n keyDimension *
        ua t * |system.A i q|
  rho_denominator_pos : ∀ t,
    0 < p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  rho_equation : ∀ t,
    rhoAR t =
      p19VecNorm2 (p19AbsRectMatVec (zHat t) (yHat t)) /
        p19VecNorm2 (p19RectMatVec (zHat t) (yHat t))
  condition316 :
    p19MuchLessThanOneAt l (fun t ↦
      p19Condition316Value system (ug t) (um t) (ua t) (etaR t) (rhoAR t))

/-- Right-preconditioned line 4: form `V_hat y_hat` in precision `u_g` and
then apply the fixed right preconditioner again in precision `u_m`. -/
structure P19RightGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  solutionPreconditionerDelta : ι → P19Matrix n
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.vHat t i j|
  solution_preconditioner_error_bound : ∀ t,
    p19FrobNorm (solutionPreconditionerDelta t) ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.um t * run.etaR t * p19FrobNorm system.MRinv
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19MatVec (system.MRinv + solutionPreconditionerDelta t)
        (p19RectMatVec (run.vHat t + solutionBasisDelta t) (run.yHat t)))

/-- Flexible line 4: reuse the stored preconditioned basis and form
`Z_hat y_hat` directly in precision `u_g`, with no fresh preconditioner
application. -/
structure P19FlexibleGMRESRun {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    (run : P19FixedRightGMRESRun system l) where
  solutionBasisDelta : ι → P19RectMatrix n run.keyDimension
  xHat : ι → P19Vector n
  solution_basis_error_bound : ∀ t i j,
    |solutionBasisDelta t i j| ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        run.ug t * |run.zHat t i j|
  solution_equation : ∀ t,
    xHat t = p19Add system.xInitial
      (p19RectMatVec (run.zHat t + solutionBasisDelta t) (run.yHat t))

/-- Appendix-C contribution certificate. Each first-order contribution is
linked to the perturbation family that generates it; the final three-term
forward-error inequality is not stored. -/
structure P19RightForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19RightGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  reapplicationPropagation : ι → P19Matrix n → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  reapplicationContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  reapplication_link : ∀ t,
    reapplicationContribution t =
      reapplicationPropagation t (algorithm.solutionPreconditionerDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  reapplicationPropagation_zero : ∀ t, reapplicationPropagation t 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + reapplicationContribution t +
        matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  reapplication_bound : ∀ t,
    p19VecNorm2 (reapplicationContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.um t * run.etaR t * p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- Appendix-D contribution certificate for flexible GMRES. Its first-order
decomposition has no preconditioner-reapplication contribution. -/
structure P19FlexibleForwardAnalysis {n : ℕ} {ι : Type*}
    {system : P19FixedRightSystem n} {l : Filter ι}
    {run : P19FixedRightGMRESRun system l}
    (algorithm : P19FlexibleGMRESRun run) where
  gmresPropagation : ι → P19Vector n →
    P19RectMatrix n run.keyDimension →
    P19RectMatrix n run.keyDimension → P19Vector n
  matrixPropagation : ι →
    (Fin run.keyDimension → P19Matrix n) → P19Vector n
  gmresContribution : ι → P19Vector n
  matrixContribution : ι → P19Vector n
  remainder : ι → P19Vector n
  gmres_link : ∀ t,
    gmresContribution t =
      gmresPropagation t (run.leastSquaresDeltaB t)
        (run.leastSquaresDeltaC t) (algorithm.solutionBasisDelta t)
  matrix_link : ∀ t,
    matrixContribution t = matrixPropagation t (run.matrixDelta t)
  gmresPropagation_zero : ∀ t, gmresPropagation t 0 0 0 = 0
  matrixPropagation_zero : ∀ t,
    matrixPropagation t (fun _ ↦ 0) = 0
  error_decomposition : ∀ t,
    algorithm.xHat t - system.xExact =
      gmresContribution t + matrixContribution t + remainder t
  gmres_bound : ∀ t,
    p19VecNorm2 (gmresContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ug t * p19RightOperatorKappa2 system *
          p19RightPreconditionerKappa2 system)
  matrix_bound : ∀ t,
    p19VecNorm2 (matrixContribution t) / p19VecNorm2 system.xExact ≤
      p19PolynomialFactorValue run.polynomialFactor n run.keyDimension *
        (run.ua t * p19SystemKappa2 system * run.rhoAR t)
  remainder_second_order :
    p19SecondOrderAt l
      (fun t ↦ p19Condition316Value system
        (run.ug t) (run.um t) (run.ua t) (run.etaR t) (run.rhoAR t))
      (fun t ↦ p19VecNorm2 (remainder t) / p19VecNorm2 system.xExact)

/-- A proof-carrying right-preconditioned execution of Theorem 3.3. -/
structure P19RightTheorem33Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19RightGMRESRun run
  analysis : P19RightForwardAnalysis algorithm

/-- A proof-carrying fixed-preconditioner flexible execution of Theorem 3.4. -/
structure P19FlexibleTheorem34Execution {n : ℕ} {ι : Type*}
    (system : P19FixedRightSystem n) (l : Filter ι) where
  run : P19FixedRightGMRESRun system l
  algorithm : P19FlexibleGMRESRun run
  analysis : P19FlexibleForwardAnalysis algorithm

/-- The two square-matrix condition-number readings that Section 2 explicitly
allows when it subsequently writes an unqualified `kappa`. -/
inductive P19StaticSquareKappaChoice where
  | frobenius
  | inducedTwo

/-- A source-authorized interpretation of an unqualified square condition
number. The inverse argument remains attached to the matrix it inverts. -/
noncomputable def p19StaticKappa (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) : ℝ :=
  match choice with
  | .frobenius => p19ConditionNumberF A Ainv
  | .inducedTwo => p19Kappa2 A Ainv

/-- One fixed nonsingular right preconditioner for a static Algorithm 2
family. The two identity equations express `M_L = I`. -/
structure P19StaticFixedRightPreconditioner {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) where
  MR : P19Matrix n
  MRinv : P19Matrix n
  MR_inverse : p19InversePair MR MRinv
  right_operator_inverse :
    p19InversePair (p19SquareRectMul family.system.A MRinv)
      (p19SquareRectMul MR family.system.Ainv)
  nontrivial : MR ≠ 1
  left_preconditioner_identity : family.system.ML = 1
  left_preconditioner_inverse_identity : family.system.MLinv = 1

/-- The condition number of the original matrix in Theorems 3.3-3.4. -/
noncomputable def p19StaticSystemKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) : ℝ :=
  p19StaticKappa choice family.system.A family.system.Ainv

/-- The condition number of the fixed right preconditioner. -/
noncomputable def p19StaticRightPreconditionerKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice preconditioner.MR preconditioner.MRinv

/-- The condition number of `A M_R^{-1}`. -/
noncomputable def p19StaticRightOperatorKappa
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) : ℝ :=
  p19StaticKappa choice
    (p19SquareRectMul family.system.A preconditioner.MRinv)
    (p19SquareRectMul preconditioner.MR family.system.Ainv)

/-- The complete five-entry maximum in condition (3.16), with no numerical
threshold added to the paper's qualitative smallness notation. -/
noncomputable def p19StaticCondition316Value
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p19StaticRightOperatorKappa choice preconditioner)
    (max (ug * p19StaticRightPreconditionerKappa choice preconditioner)
      (max (um * etaR *
          p19StaticRightPreconditionerKappa choice preconditioner)
        (max (ua * p19StaticSystemKappa choice family * rhoAR)
          (ua * p19StaticRightOperatorKappa choice preconditioner *
            p19StaticRightPreconditionerKappa choice preconditioner))))

/-- The three source terms in equation (3.17). -/
noncomputable def p19StaticRightAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    um * etaR * p19StaticRightPreconditionerKappa choice preconditioner +
      ua * p19StaticSystemKappa choice family * rhoAR

/-- The two source terms in equation (3.20). -/
noncomputable def p19StaticFlexibleAttainableEnvelope
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p19StaticRightOperatorKappa choice preconditioner *
      p19StaticRightPreconditionerKappa choice preconditioner +
    ua * p19StaticSystemKappa choice family * rhoAR

/-- Raw fixed-preconditioner data shared by the right and flexible paths at
one dimension. The inaccessible basis is linked by (C.2); no error bound or
attainable dimension is stored. -/
structure P19StaticFixedRightCore {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  ug : ℝ
  um : ℝ
  ua : ℝ
  etaR : ℝ
  rhoAR : ℝ
  zHat : P19RectMatrix n k.1
  preconditionerDelta : Fin k.1 → P19Matrix n
  preconditioner_application : ∀ j,
    p19Column zHat j =
      p19MatVec (preconditioner.MRinv + preconditionerDelta j)
        (p19Column (family.iteration k).vHat j)
  matrixDelta : Fin k.1 → P19Matrix n
  matrix_application : ∀ j,
    p19Column (family.iteration k).computedC j =
      p19MatVec (family.system.A + matrixDelta j) (p19Column zHat j)
  search_space_equation : ∀ j,
    p19Column (family.basisFamily.basis k.1) j =
      p19Column zHat j +
        p19MatVec family.system.Ainv
          (p19MatVec (matrixDelta j) (p19Column zHat j))
  computation_exact : (family.iteration k).deltaC = 0
  computation_accuracy_zero : (family.iteration k).epsilonC = 0
  rhs_exact : (family.iteration k).deltaB = 0
  rhs_accuracy_zero : (family.iteration k).epsilonB = 0
  gmresMagnitude : ℝ
  basisPreconditionerMagnitude : ℝ
  matrixMagnitude : ℝ

/-- The source models (3.14), (C.1), (3.15), the MGS/Givens perturbation,
and the full qualitative condition (3.16) at one candidate dimension. These
bound actual perturbations, not propagated forward-error contributions. -/
structure P19StaticFixedRightCoreConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (core : P19StaticFixedRightCore family preconditioner k) where
  parameters_nonneg :
    0 ≤ core.ug ∧ 0 ≤ core.um ∧ 0 ≤ core.ua ∧ 0 ≤ core.etaR ∧
      0 ≤ core.rhoAR
  magnitudes_nonneg :
    0 ≤ core.gmresMagnitude ∧ 0 ≤ core.basisPreconditionerMagnitude ∧
      0 ≤ core.matrixMagnitude
  least_squares_solution :
    p19IsLeastSquaresSolution
      ((family.iteration k).computedC +
        (family.iteration k).leastSquaresDeltaC)
      ((family.iteration k).computedB +
        (family.iteration k).leastSquaresDeltaB)
      (family.iteration k).yHat
  least_squares_error_covered : ∀ j : Fin (k.1 + 1),
    p19VecNorm2
        (p19Column
          (p19Augment (family.iteration k).leastSquaresDeltaB
            (family.iteration k).leastSquaresDeltaC) j) ≤
      core.gmresMagnitude *
        p19VecNorm2
          (p19Column
            (p19Augment (family.iteration k).computedB
              (family.iteration k).computedC) j)
  basis_preconditioner_error_covered : ∀ j,
    p19FrobNorm (core.preconditionerDelta j) ≤
      core.basisPreconditionerMagnitude * p19FrobNorm preconditioner.MRinv
  matrix_error_covered : ∀ j i q,
    |core.matrixDelta j i q| ≤ core.matrixMagnitude * |family.system.A i q|
  gmres_magnitude_bound :
    core.gmresMagnitude ≤ (family.iteration k).dimensionFactor * core.ug
  basis_preconditioner_magnitude_bound :
    core.basisPreconditionerMagnitude ≤
      (family.iteration k).dimensionFactor * core.um * core.etaR
  matrix_magnitude_bound :
    core.matrixMagnitude ≤ (family.iteration k).dimensionFactor * core.ua
  rho_denominator_pos :
    0 < p19VecNorm2
      (p19RectMatVec core.zHat (family.iteration k).yHat)
  rho_equation :
    core.rhoAR =
      p19VecNorm2 (p19AbsRectMatVec core.zHat (family.iteration k).yHat) /
        p19VecNorm2 (p19RectMatVec core.zHat (family.iteration k).yHat)
  condition316 :
    semantics.small
      (p19StaticCondition316Value choice preconditioner
        core.ug core.um core.ua core.etaR core.rhoAR)

/-- Right-preconditioned solution formation: a product with `V_hat` followed
by a fresh application of `M_R^{-1}`. -/
structure P19StaticRightIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solutionPreconditionerDelta : P19Matrix n
  solution_equation :
    (family.iteration k).xHat =
      p19MatVec (preconditioner.MRinv + solutionPreconditionerDelta)
        (p19RectMatVec
          ((family.iteration k).vHat + solutionBasisDelta)
          (family.iteration k).yHat)
  reapplicationMagnitude : ℝ

/-- Fixed-precision source error bounds for right solution formation. -/
structure P19StaticRightConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticRightIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  reapplication_magnitude_nonneg : 0 ≤ iteration.reapplicationMagnitude
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |(family.iteration k).vHat i j|
  solution_preconditioner_error_covered :
    p19FrobNorm iteration.solutionPreconditionerDelta ≤
      iteration.reapplicationMagnitude * p19FrobNorm preconditioner.MRinv
  reapplication_magnitude_bound :
    iteration.reapplicationMagnitude ≤
      (family.iteration k).dimensionFactor *
        iteration.core.um * iteration.core.etaR

/-- Flexible solution formation: a direct product with the persistently stored
computed basis `Z_hat`, with no fresh preconditioner application. -/
structure P19StaticFlexibleIteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (preconditioner : P19StaticFixedRightPreconditioner family)
    (k : P19Theorem31Dimension n) where
  core : P19StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P19RectMatrix n k.1
  solution_equation :
    (family.iteration k).xHat =
      p19RectMatVec (core.zHat + solutionBasisDelta)
        (family.iteration k).yHat

/-- Fixed-precision source error bounds for flexible solution formation. -/
structure P19StaticFlexibleConditions
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    {preconditioner : P19StaticFixedRightPreconditioner family}
    {k : P19Theorem31Dimension n}
    (iteration : P19StaticFlexibleIteration family preconditioner k) where
  core : P19StaticFixedRightCoreConditions choice iteration.core
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |iteration.core.zHat i j|

/-- Static right-preconditioned executions at all admissible dimensions. -/
structure P19StaticRightFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticRightIteration family preconditioner k

/-- Static fixed-preconditioner flexible executions at all admissible
dimensions. -/
structure P19StaticFlexibleFamily (n : ℕ)
    (semantics : P19FirstOrderSemantics) where
  family : P19Theorem31Family n semantics
  preconditioner : P19StaticFixedRightPreconditioner family
  iteration : ∀ k : P19Theorem31Dimension n,
    P19StaticFlexibleIteration family preconditioner k

/-- Raw Appendix-C propagation at one dimension. The gains multiply actual
source-error magnitudes; neither `c(n,k)` nor (3.17) is stored. -/
structure P19StaticRightAppendixCExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  reapplicationContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (right.family.iteration k).xHat - right.family.system.xExact =
      gmresContribution + reapplicationContribution + matrixContribution +
        remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 right.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice right.preconditioner *
          p19StaticRightPreconditionerKappa choice right.preconditioner
  reapplication_gain_bound :
    p19VecNorm2 reapplicationContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).reapplicationMagnitude *
        p19StaticRightPreconditionerKappa choice right.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR

/-- Raw Appendix-D propagation at one dimension. It has no reapplication
contribution and stores neither `c(n,k)` nor (3.20). -/
structure P19StaticFlexibleAppendixDExpansion
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics)
    (k : P19Theorem31Dimension n) where
  gmresContribution : P19Vector n
  matrixContribution : P19Vector n
  remainder : P19Vector n
  error_decomposition :
    (flexible.family.iteration k).xHat - flexible.family.system.xExact =
      gmresContribution + matrixContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 flexible.family.system.xExact)
  gmres_gain_bound :
    p19VecNorm2 gmresContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.gmresMagnitude *
        p19StaticRightOperatorKappa choice flexible.preconditioner *
          p19StaticRightPreconditionerKappa choice flexible.preconditioner
  matrix_gain_bound :
    p19VecNorm2 matrixContribution /
          p19VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.matrixMagnitude *
        p19StaticSystemKappa choice flexible.family *
          (flexible.iteration k).core.rhoAR

/-- Uniform Appendix-C dependency. It receives the MGS-selected dimension and
the source conditions and supplies only the raw propagation above. -/
structure P19StaticRightAppendixCTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (right.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (right.family.iteration k)) →
    P19StaticRightConditions choice (right.iteration k) →
      P19StaticRightAppendixCExpansion choice right k

/-- Uniform Appendix-D dependency, again without a selected dimension or the
collected theorem bound. -/
structure P19StaticFlexibleAppendixDTheory
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics) where
  expansion : ∀ (k : P19Theorem31Dimension n),
    p19IterationWellConditioned (flexible.family.iteration k) →
    (k.1 = n ∨ p19MGSNearDependence (flexible.family.iteration k)) →
    P19StaticFlexibleConditions choice (flexible.iteration k) →
      P19StaticFlexibleAppendixDExpansion choice flexible k

end HighamBench
```
