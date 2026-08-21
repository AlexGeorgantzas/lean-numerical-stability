# Declaration dossier for P11-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p11_t3_orthogonality_defect_bound {m n : ℕ}
    (run : P11CGSPTheorem1Run m n) :
    ∀ k : Fin n,
      p11OpNorm2
          (p11RectOrthogonalityDefect (p11ColumnPrefix run.Q k)) ≤
        p11C4 m (k.val + 1) *
              p11Kappa2 (p11LeadingBlock run.R k)
                  (run.leadingInverse k) ^ 2 *
            run.epsilonM +
          p11Theorem1OrthogonalityRemainderCoeff run k *
            run.epsilonM ^ 2
```

## Elaborated target type

```lean
∀ {m n : Nat} (run : HighamBench.P11CGSPTheorem1Run m n) (k : Fin n),
  Real.instLE.le (HighamBench.p11OpNorm2 (HighamBench.p11RectOrthogonalityDefect (HighamBench.p11ColumnPrefix run.Q k)))
    (instHAdd.hAdd
      (instHMul.hMul
        (instHMul.hMul (HighamBench.p11C4 m (instHAdd.hAdd k.val 1))
          (instHPow.hPow (HighamBench.p11Kappa2 (HighamBench.p11LeadingBlock run.R k) (run.leadingInverse k)) 2))
        run.epsilonM)
      (instHMul.hMul (HighamBench.p11Theorem1OrthogonalityRemainderCoeff run k) (instHPow.hPow run.epsilonM 2)))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (run : HighamBench.P11CGSPTheorem1Run m n) (k : Fin n),
  @LE.le.{0} Real Real.instLE
    (@HighamBench.p11OpNorm2
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HighamBench.p11RectOrthogonalityDefect m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.p11ColumnPrefix m n (@HighamBench.P11CGSPTheorem1Run.Q m n run) k)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (HighamBench.p11C4 m
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HighamBench.p11Kappa2
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HighamBench.p11LeadingBlock n (@HighamBench.P11CGSPTheorem1Run.R m n run) k)
              (@HighamBench.P11CGSPTheorem1Run.leadingInverse m n run k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HighamBench.P11CGSPTheorem1Run.epsilonM m n run))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.p11Theorem1OrthogonalityRemainderCoeff m n run k)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (@HighamBench.P11CGSPTheorem1Run.epsilonM m n run)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P11Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P11Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.CStarAlgebra.Matrix`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P11CGSPTheorem1Run`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `42844110370a2d08e8b33dc425a7c8906b46f2f13beefe01c915c765a2044e22`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(m n : Nat) → Type
```

### D002: `HighamBench.P11CGSPTheorem1Run.Q`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `968d297b07b9e9043d0b255726394b0cabe6a4b1ab48bad42dc2270cfdbdba7f`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → HighamBench.P11RectMatrix m n
```

Fully explicit type:

```lean
{m n : Nat} → (self : HighamBench.P11CGSPTheorem1Run m n) → HighamBench.P11RectMatrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.5
```

### D003: `HighamBench.P11CGSPTheorem1Run.R`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `12b7d00b54c4e4d203038ad90549de5ea0186d0ea5f8298250bf2f836eb3cfa6`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
{m n : Nat} → (self : HighamBench.P11CGSPTheorem1Run m n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.6
```

### D004: `HighamBench.P11CGSPTheorem1Run.epsilonM`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d37dcbd78f5e0cf51b01fe51020b651b96d534f55739e70a303191649b8cc4ab`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (self : HighamBench.P11CGSPTheorem1Run m n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.9
```

### D005: `HighamBench.P11CGSPTheorem1Run.leadingInverse`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f796d1993b87ae8b4f28ee378b372e8b04f73dbd508077ba2be2f4e2634dc46a`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → (k : Fin n) → HighamBench.P11Matrix (instHAdd.hAdd k.val 1)
```

Fully explicit type:

```lean
{m n : Nat} →
  (self : HighamBench.P11CGSPTheorem1Run m n) →
    (k : Fin n) →
      HighamBench.P11Matrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.12
```

### D006: `HighamBench.p11C4`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8f2c155c77d4c16aea80738b5ae7b604b872a12e62760f1c0ac8a302fbc4f743`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(m k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k => instHAdd.hAdd (HighamBench.p11C2 m k) (instHMul.hMul 2 (HighamBench.p11C1 m k))
```

### D007: `HighamBench.p11ColumnPrefix`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c78c40f5672660e00e3a8b29d027870cd22b7a49d516a1e5098f2d8afa8d83e`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → (k : Fin n) → HighamBench.P11RectMatrix m (instHAdd.hAdd k.val 1)
```

Fully explicit type:

```lean
{m n : Nat} →
  (A : HighamBench.P11RectMatrix m n) →
    (k : Fin n) →
      HighamBench.P11RectMatrix m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A k i j => A i (Fin.castLE ⋯ j)
```

### D008: `HighamBench.p11Kappa2`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1f027b9831ac4b41c191c8155e75d236b1c2a94366da21461f0895f5a074537d`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → HighamBench.P11Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (R Rinv : HighamBench.P11Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R Rinv => instHMul.hMul (HighamBench.p11OpNorm2 R) (HighamBench.p11OpNorm2 Rinv)
```

### D009: `HighamBench.p11LeadingBlock`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1efb31586e183a13446325718b87a7358f5cc51a349c897b72d2e1837e075d2a`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → (k : Fin n) → HighamBench.P11Matrix (instHAdd.hAdd k.val 1)
```

Fully explicit type:

```lean
{n : Nat} →
  (R : HighamBench.P11Matrix n) →
    (k : Fin n) →
      HighamBench.P11Matrix
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

Definition body (one-level semantic boundary):

```lean
fun {n} R k i j => R (Fin.castLE ⋯ i) (Fin.castLE ⋯ j)
```

### D010: `HighamBench.p11OpNorm2`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9e3c517d428a26eec754111d483048d655c05f52bfdd2a9013cb15cff394ccee`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P11Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D011: `HighamBench.p11RectOrthogonalityDefect`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cf3a0f08435f90398f8b694ecf96446b253704af09c791b454e534eea2c5f7f8`

Type:

```lean
{m k : Nat} → HighamBench.P11RectMatrix m k → HighamBench.P11Matrix k
```

Fully explicit type:

```lean
{m k : Nat} → (Q : HighamBench.P11RectMatrix m k) → HighamBench.P11Matrix k
```

Definition body (one-level semantic boundary):

```lean
fun {m k} Q => instHSub.hSub (HighamBench.p11Identity k) (HighamBench.p11RectMatMul (HighamBench.p11RectTranspose Q) Q)
```

### D012: `HighamBench.p11Theorem1OrthogonalityRemainderCoeff`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6fd1c901671b0d677ada4d15c4a1cc50dfaaba0549610420f3f02584a5f67a4e`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (run : HighamBench.P11CGSPTheorem1Run m n) → (k : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} run k =>
  have certificate := run.prefixCertificate k;
  have a := HighamBench.p11RectOpNorm2 (HighamBench.p11ColumnPrefix run.A k);
  have r := HighamBench.p11OpNorm2 (HighamBench.p11LeadingBlock run.R k);
  have rinv := HighamBench.p11OpNorm2 (run.leadingInverse k);
  have normSlope :=
    instHAdd.hAdd (instHMul.hMul (HighamBench.p11C3 m (instHAdd.hAdd k.val 1)) r)
      certificate.reverseNormSecondOrderCoeff;
  have aSquareRemainder := instHAdd.hAdd (instHMul.hMul (instHMul.hMul 2 r) normSlope) (instHPow.hPow normSlope 2);
  have coreRemainder :=
    instHAdd.hAdd
      (instHAdd.hAdd certificate.normalEquationSecondOrderCoeff
        (instHMul.hMul (instHMul.hMul 2 a) certificate.factorizationSecondOrderCoeff))
      (instHPow.hPow
        (instHAdd.hAdd (instHMul.hMul (HighamBench.p11C1 m (instHAdd.hAdd k.val 1)) a)
          certificate.factorizationSecondOrderCoeff)
        2);
  instHMul.hMul (instHPow.hPow rinv 2)
    (instHAdd.hAdd (instHMul.hMul (HighamBench.p11C4 m (instHAdd.hAdd k.val 1)) aSquareRemainder) coreRemainder)
```

### D013: `HighamBench.P11CGSPTheorem1Run.A`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a580e1dd68785592879c4aea4503d8facbb2593f63fd1b5932714bf6b8c76dcc`

Type:

```lean
{m n : Nat} → HighamBench.P11CGSPTheorem1Run m n → HighamBench.P11RectMatrix m n
```

Fully explicit type:

```lean
{m n : Nat} → (self : HighamBench.P11CGSPTheorem1Run m n) → HighamBench.P11RectMatrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.4
```

### D014: `HighamBench.P11CGSPTheorem1Run.mk`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `fab0e9bf713d88b0bf7f6887c3542a8d81af310b305f39cf67e46749970b6574`

Type:

```lean
{m n : Nat} →
  instLTNat.lt 0 m →
    instLTNat.lt 0 n →
      instLENat.le n m →
        (A Q : HighamBench.P11RectMatrix m n) →
          (R : HighamBench.P11Matrix n) →
            Function.Injective (Matrix.mulVec A) →
              (∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (R i j) 0) →
                (epsilonM : Real) →
                  Real.instLT.lt 0 epsilonM →
                    Real.instLT.lt epsilonM 1 →
                      (leadingInverse : (k : Fin n) → HighamBench.P11Matrix (instHAdd.hAdd k.val 1)) →
                        (∀ (k : Fin n),
                            Eq
                              (HighamBench.p11MatMul (instHAdd.hAdd k.val 1) (leadingInverse k)
                                (HighamBench.p11LeadingBlock R k))
                              (HighamBench.p11Identity (instHAdd.hAdd k.val 1))) →
                          (∀ (k : Fin n),
                              Eq
                                (HighamBench.p11MatMul (instHAdd.hAdd k.val 1) (HighamBench.p11LeadingBlock R k)
                                  (leadingInverse k))
                                (HighamBench.p11Identity (instHAdd.hAdd k.val 1))) →
                            (∀ (k : Fin n),
                                Real.instLT.lt
                                  (instHMul.hMul (instHMul.hMul (HighamBench.p11C4 m (instHAdd.hAdd k.val 1)) epsilonM)
                                    (instHPow.hPow
                                      (HighamBench.p11Kappa2 (HighamBench.p11LeadingBlock R k) (leadingInverse k)) 2))
                                  1) →
                              ((k : Fin n) → HighamBench.P11CGSPColumnTrace A Q R epsilonM k) →
                                ((k : Fin n) →
                                    HighamBench.P11Theorem1PrefixCertificate (HighamBench.p11ColumnPrefix A k)
                                      (HighamBench.p11ColumnPrefix Q k) (HighamBench.p11LeadingBlock R k) epsilonM) →
                                  HighamBench.P11CGSPTheorem1Run m n
```

Fully explicit type:

```lean
{m n : Nat} →
  (row_dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) →
    (column_dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
      (columns_le_rows : @LE.le.{0} Nat instLENat n m) →
        (A Q : HighamBench.P11RectMatrix m n) →
          (R : HighamBench.P11Matrix n) →
            (full_column_rank :
                @Function.Injective.{1, 1} (Fin n → Real) (Fin m → Real)
                  (@Matrix.mulVec.{0, 0, 0} (Fin m) (Fin n) Real
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@NonUnitalNormedCommRing.toNonUnitalCommRing.{0} Real
                            (@NormedCommRing.toNonUnitalNormedCommRing.{0} Real Real.normedCommRing)))))
                    (Fin.fintype n) A)) →
              (R_upper_triangular :
                  ∀ (i j : Fin n),
                    @LT.lt.{0} Nat instLTNat (@Fin.val n j) (@Fin.val n i) →
                      @Eq.{1} Real (R i j)
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                (epsilonM : Real) →
                  (epsilonM_pos :
                      @LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonM) →
                    (epsilonM_lt_one :
                        @LT.lt.{0} Real Real.instLT epsilonM
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                      (leadingInverse :
                          (k : Fin n) →
                            HighamBench.P11Matrix
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        (leading_left_inverse :
                            ∀ (k : Fin n),
                              @Eq.{1}
                                (HighamBench.P11Matrix
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (HighamBench.p11MatMul
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (leadingInverse k) (@HighamBench.p11LeadingBlock n R k))
                                (HighamBench.p11Identity
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                          (leading_right_inverse :
                              ∀ (k : Fin n),
                                @Eq.{1}
                                  (HighamBench.P11Matrix
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (HighamBench.p11MatMul
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@HighamBench.p11LeadingBlock n R k) (leadingInverse k))
                                  (HighamBench.p11Identity
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                            (condition_3 :
                                ∀ (k : Fin n),
                                  @LT.lt.{0} Real Real.instLT
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (HighamBench.p11C4 m
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Fin.val n k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        epsilonM)
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                        (@HighamBench.p11Kappa2
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Fin.val n k)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@HighamBench.p11LeadingBlock n R k) (leadingInverse k))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                              (algorithm2_trace : (k : Fin n) → @HighamBench.P11CGSPColumnTrace m n A Q R epsilonM k) →
                                (prefixCertificate :
                                    (k : Fin n) →
                                      @HighamBench.P11Theorem1PrefixCertificate m
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@HighamBench.p11ColumnPrefix m n A k) (@HighamBench.p11ColumnPrefix m n Q k)
                                        (@HighamBench.p11LeadingBlock n R k) epsilonM) →
                                  HighamBench.P11CGSPTheorem1Run m n
```

### D015: `HighamBench.P11CGSPTheorem1Run.prefixCertificate`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `61d1d0afa5493ee94b18352912800461c2fb442c4b9b93066a965f441bb44f34`

Type:

```lean
{m n : Nat} →
  (self : HighamBench.P11CGSPTheorem1Run m n) →
    (k : Fin n) →
      HighamBench.P11Theorem1PrefixCertificate (HighamBench.p11ColumnPrefix self.A k)
        (HighamBench.p11ColumnPrefix self.Q k) (HighamBench.p11LeadingBlock self.R k) self.epsilonM
```

Fully explicit type:

```lean
{m n : Nat} →
  (self : HighamBench.P11CGSPTheorem1Run m n) →
    (k : Fin n) →
      @HighamBench.P11Theorem1PrefixCertificate m
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.p11ColumnPrefix m n (@HighamBench.P11CGSPTheorem1Run.A m n self) k)
        (@HighamBench.p11ColumnPrefix m n (@HighamBench.P11CGSPTheorem1Run.Q m n self) k)
        (@HighamBench.p11LeadingBlock n (@HighamBench.P11CGSPTheorem1Run.R m n self) k)
        (@HighamBench.P11CGSPTheorem1Run.epsilonM m n self)
```

Definition body (one-level semantic boundary):

```lean
fun m n self => self.17
```

### D016: `HighamBench.P11Matrix`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `36cb62df059104618b8f64e14d1c7515ec97591f02a19d69708a101cde0e7dce`

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

### D017: `HighamBench.P11RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `157fc1c63f67a701a836e52c7a1efe6c7c8816987afb4e184e7e849df6494e90`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(m n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D018: `HighamBench.P11Theorem1PrefixCertificate`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6f5c90db1f66d3db450aed8dab8ad7a55be652ceb40604dc9ca384b59a55b76e`

Type:

```lean
{m k : Nat} → HighamBench.P11RectMatrix m k → HighamBench.P11RectMatrix m k → HighamBench.P11Matrix k → Real → Type
```

Fully explicit type:

```lean
{m k : Nat} → (A Q : HighamBench.P11RectMatrix m k) → (R : HighamBench.P11Matrix k) → (epsilonM : Real) → Type
```

### D019: `HighamBench.P11Theorem1PrefixCertificate.factorizationSecondOrderCoeff`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fa9a66ac6f8c5329d359228cf5570c1de3bbb93a557326181598797b9c11be35`

Type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} → {epsilonM : Real} → HighamBench.P11Theorem1PrefixCertificate A Q R epsilonM → Real
```

Fully explicit type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} →
      {epsilonM : Real} → (self : @HighamBench.P11Theorem1PrefixCertificate m k A Q R epsilonM) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A Q R epsilonM self => self.3
```

### D020: `HighamBench.P11Theorem1PrefixCertificate.normalEquationSecondOrderCoeff`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `380a214414f38413479bbb67da6310aafe2a86ac903156cb7e4ceca854725c7e`

Type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} → {epsilonM : Real} → HighamBench.P11Theorem1PrefixCertificate A Q R epsilonM → Real
```

Fully explicit type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} →
      {epsilonM : Real} → (self : @HighamBench.P11Theorem1PrefixCertificate m k A Q R epsilonM) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A Q R epsilonM self => self.4
```

### D021: `HighamBench.P11Theorem1PrefixCertificate.reverseNormSecondOrderCoeff`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2b3bf759cd4e849b2bede2c39aee1f644705c279ae862d405be4c1e50eee0915`

Type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} → {epsilonM : Real} → HighamBench.P11Theorem1PrefixCertificate A Q R epsilonM → Real
```

Fully explicit type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} →
      {epsilonM : Real} → (self : @HighamBench.P11Theorem1PrefixCertificate m k A Q R epsilonM) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A Q R epsilonM self => self.5
```

### D022: `HighamBench.p11C1`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a7ae047fbf6313935e520d17845cb69e0cd9566b671867985a99185edf24e2d5`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(m k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k =>
  ite (Eq k 1) 1
    (instHAdd.hAdd (instHMul.hMul (instHMul.hMul 2 (instHMul.hMul 2 m.cast).sqrt) k.cast) (instHMul.hMul 2 k.cast.sqrt))
```

### D023: `HighamBench.p11C1._proof_1`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `52067e5a77dcfefcf6fcc3dd88352b7497aba5f0a24254ae20d387e9e2f2faf7`

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

### D024: `HighamBench.p11C2`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d798e6a8b8ba59dbcb92ee2cfc3d3d4168700ab660301680a184a00da12fe4b1`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(m k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k =>
  ite (Eq k 1) (instHAdd.hAdd m.cast 2)
    (instHAdd.hAdd
      (instHSub.hSub (instHMul.hMul (instHMul.hMul (7 / 2) m.cast) (instHPow.hPow k.cast 2))
        (instHMul.hMul (instHMul.hMul (3 / 2) m.cast) k.cast))
      (instHMul.hMul 16 k.cast))
```

### D025: `HighamBench.p11C3`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c0ecb567dcc422d45ddb50bd71c12eace0cf0bad73f7974c28e5b5fc39325954`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(m k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k => instHMul.hMul (1 / 2) (HighamBench.p11C2 m k)
```

### D026: `HighamBench.p11Identity`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `00a8fef3c8e11f6c84bb5d143a23f246869ac3bd80853c7ec3de93f1add99fda`

Type:

```lean
(n : Nat) → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n => 1
```

### D027: `HighamBench.p11LeadingBlock._proof_1`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `60564d03e1dd6754e3f768cd633cfa899d84059307025fff5d0e1d2c20189049`

Type:

```lean
∀ {n : Nat} (k : Fin n), instLENat.le k.val.succ n
```

Fully explicit type:

```lean
∀ {n : Nat} (k : Fin n), @LE.le.{0} Nat instLENat (Nat.succ (@Fin.val n k)) n
```

### D028: `HighamBench.p11RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `45dbaf27eb1bfa2cd0daa5ab3a20f4c59e27000bb35c7e9ee94b4e37d117677d`

Type:

```lean
{m n p : Nat} → HighamBench.P11RectMatrix m n → HighamBench.P11RectMatrix n p → HighamBench.P11RectMatrix m p
```

Fully explicit type:

```lean
{m n p : Nat} →
  (A : HighamBench.P11RectMatrix m n) → (B : HighamBench.P11RectMatrix n p) → HighamBench.P11RectMatrix m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D029: `HighamBench.p11RectOpNorm2`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1b2d7c2d7e8f4d40657845bb9aa69ad3127ead898c03c302f25c632a978029d0`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P11RectMatrix m n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D030: `HighamBench.p11RectTranspose`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6e4fb23abd6b03197c4fe854dbe27e151d6ef4dbe4698963a4bedfa69b00bee2`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → HighamBench.P11RectMatrix n m
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P11RectMatrix m n) → HighamBench.P11RectMatrix n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => Matrix.transpose A
```

### D031: `HighamBench.P11CGSPColumnTrace`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `709a4b6df878964e20af6a8aaac451ec5f6ab915672c6b5525c949ff34b99582`

Type:

```lean
{m n : Nat} →
  HighamBench.P11RectMatrix m n → HighamBench.P11RectMatrix m n → HighamBench.P11Matrix n → Real → Fin n → Type
```

Fully explicit type:

```lean
{m n : Nat} →
  (A Q : HighamBench.P11RectMatrix m n) → (R : HighamBench.P11Matrix n) → (epsilonM : Real) → (k : Fin n) → Type
```

### D032: `HighamBench.P11Theorem1PrefixCertificate.mk`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `dae41e053aa1476a3e94c73e07012760fbb97e3129f9447316fba107980fd072`

Type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} →
      {epsilonM : Real} →
        (deltaA : HighamBench.P11RectMatrix m k) →
          (normalEquationResidual : HighamBench.P11Matrix k) →
            (factorizationSecondOrderCoeff normalEquationSecondOrderCoeff reverseNormSecondOrderCoeff : Real) →
              Real.instLE.le 0 factorizationSecondOrderCoeff →
                Real.instLE.le 0 normalEquationSecondOrderCoeff →
                  Real.instLE.le 0 reverseNormSecondOrderCoeff →
                    Eq (HighamBench.p11RectMatMul Q R) (instHAdd.hAdd A deltaA) →
                      Eq normalEquationResidual (HighamBench.p11RectNormalEquationResidual A R) →
                        Real.instLE.le (HighamBench.p11RectOpNorm2 deltaA)
                            (instHAdd.hAdd
                              (instHMul.hMul (instHMul.hMul (HighamBench.p11C1 m k) (HighamBench.p11RectOpNorm2 A))
                                epsilonM)
                              (instHMul.hMul factorizationSecondOrderCoeff (instHPow.hPow epsilonM 2))) →
                          Real.instLE.le (HighamBench.p11OpNorm2 normalEquationResidual)
                              (instHAdd.hAdd
                                (instHMul.hMul
                                  (instHMul.hMul (HighamBench.p11C2 m k)
                                    (instHPow.hPow (HighamBench.p11RectOpNorm2 A) 2))
                                  epsilonM)
                                (instHMul.hMul normalEquationSecondOrderCoeff (instHPow.hPow epsilonM 2))) →
                            Real.instLE.le (HighamBench.p11RectOpNorm2 A)
                                (instHAdd.hAdd
                                  (instHMul.hMul (instHAdd.hAdd 1 (instHMul.hMul (HighamBench.p11C3 m k) epsilonM))
                                    (HighamBench.p11OpNorm2 R))
                                  (instHMul.hMul reverseNormSecondOrderCoeff (instHPow.hPow epsilonM 2))) →
                              HighamBench.P11Theorem1PrefixCertificate A Q R epsilonM
```

Fully explicit type:

```lean
{m k : Nat} →
  {A Q : HighamBench.P11RectMatrix m k} →
    {R : HighamBench.P11Matrix k} →
      {epsilonM : Real} →
        (deltaA : HighamBench.P11RectMatrix m k) →
          (normalEquationResidual : HighamBench.P11Matrix k) →
            (factorizationSecondOrderCoeff normalEquationSecondOrderCoeff reverseNormSecondOrderCoeff : Real) →
              (factorization_second_order_nonneg :
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    factorizationSecondOrderCoeff) →
                (normal_equation_second_order_nonneg :
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      normalEquationSecondOrderCoeff) →
                  (reverse_norm_second_order_nonneg :
                      @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        reverseNormSecondOrderCoeff) →
                    (factorization_relation :
                        @Eq.{1} (HighamBench.P11RectMatrix m k) (@HighamBench.p11RectMatMul m k k Q R)
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P11RectMatrix m k) (HighamBench.P11RectMatrix m k)
                            (HighamBench.P11RectMatrix m k)
                            (@instHAdd.{0} (HighamBench.P11RectMatrix m k)
                              (@Matrix.add.{0, 0, 0} (Fin m) (Fin k) Real Real.instAdd))
                            A deltaA)) →
                      (normal_equation_relation :
                          @Eq.{1} (HighamBench.P11Matrix k) normalEquationResidual
                            (@HighamBench.p11RectNormalEquationResidual m k A R)) →
                        (factorization_bound :
                            @LE.le.{0} Real Real.instLE (@HighamBench.p11RectOpNorm2 m k deltaA)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (HighamBench.p11C1 m k) (@HighamBench.p11RectOpNorm2 m k A))
                                  epsilonM)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  factorizationSecondOrderCoeff
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) epsilonM
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                          (normal_equation_bound :
                              @LE.le.{0} Real Real.instLE (@HighamBench.p11OpNorm2 k normalEquationResidual)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (HighamBench.p11C2 m k)
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                        (@HighamBench.p11RectOpNorm2 m k A)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    epsilonM)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    normalEquationSecondOrderCoeff
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) epsilonM
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                            (reverse_norm_bound :
                                @LE.le.{0} Real Real.instLE (@HighamBench.p11RectOpNorm2 m k A)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (HighamBench.p11C3 m k) epsilonM))
                                      (@HighamBench.p11OpNorm2 k R))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      reverseNormSecondOrderCoeff
                                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                                        (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) epsilonM
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                              @HighamBench.P11Theorem1PrefixCertificate m k A Q R epsilonM
```

### D033: `HighamBench.p11C2._proof_1`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7c4860c0f215e578204f5411971cf76e3cca164a37651cfc446acaa760c945e4`

Type:

```lean
(instHAdd.hAdd 6 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D034: `HighamBench.p11C2._proof_2`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `43da9e2478acfcc10315652cd8017ae5008c9946f416851d0614bcf8778b9474`

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

### D035: `HighamBench.p11C2._proof_3`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `1aa79886ab5282243bf93d3fba3d63ed20aa22eb2ac713e36b95342b25d8a763`

Type:

```lean
(instHAdd.hAdd 15 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D036: `HighamBench.p11MatMul`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5a88abf3460b515aae8930a3c3f8e801fd2d6dc6711b9f813b357ae40f5166b9`

Type:

```lean
(n : Nat) → HighamBench.P11Matrix n → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
(n : Nat) → (A B : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D037: `HighamBench.P11CGSPColumnTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `00980d2f09c32c990f3fdbc35864f990bb3941739c697b17968e800900316340`

Type:

```lean
{m n : Nat} →
  {A Q : HighamBench.P11RectMatrix m n} →
    {R : HighamBench.P11Matrix n} →
      {epsilonM : Real} →
        {k : Fin n} →
          (s : Fin n → Real) →
            (v : Fin m → Real) →
              (psi phi : Real) →
                (projectionError : Fin n → Real) →
                  (residualError : Fin m → Real) →
                    (psiError phiError diagonalError : Real) →
                      (normalizationError : Fin m → Real) →
                        (localErrorScale : Real) →
                          Real.instLE.le 0 localErrorScale →
                            (∀ (j : Fin n), instLENat.le k.val j.val → Eq (s j) 0) →
                              (Eq k.val 0 →
                                  Eq (R k k) (instHAdd.hAdd (HighamBench.p11CGSPColumnNorm A k) diagonalError)) →
                                (Eq k.val 0 →
                                    ∀ (i : Fin m),
                                      Eq (Q i k)
                                        (instHAdd.hAdd (instHDiv.hDiv (A i k) (R k k)) (normalizationError i))) →
                                  (instLTNat.lt 0 k.val →
                                      ∀ (j : Fin n),
                                        instLTNat.lt j.val k.val →
                                          Eq (s j)
                                            (instHAdd.hAdd (HighamBench.p11CGSPProjectionEntry A Q j k)
                                              (projectionError j))) →
                                    (instLTNat.lt 0 k.val →
                                        ∀ (j : Fin n), instLTNat.lt j.val k.val → Eq (R j k) (s j)) →
                                      (instLTNat.lt 0 k.val →
                                          ∀ (i : Fin m),
                                            Eq (v i)
                                              (instHAdd.hAdd (HighamBench.p11CGSPResidualEntry A Q s i k)
                                                (residualError i))) →
                                        (instLTNat.lt 0 k.val →
                                            Eq psi (instHAdd.hAdd (HighamBench.p11CGSPColumnNorm A k) psiError)) →
                                          (instLTNat.lt 0 k.val →
                                              Eq phi (instHAdd.hAdd (HighamBench.p11VecNorm s) phiError)) →
                                            (instLTNat.lt 0 k.val → Real.instLE.le 0 psi) →
                                              (instLTNat.lt 0 k.val → Real.instLE.le 0 phi) →
                                                (instLTNat.lt 0 k.val → Real.instLE.le 0 (instHSub.hSub psi phi)) →
                                                  (instLTNat.lt 0 k.val →
                                                      Eq (R k k)
                                                        (instHAdd.hAdd
                                                          (instHMul.hMul (instHSub.hSub psi phi).sqrt
                                                            (instHAdd.hAdd psi phi).sqrt)
                                                          diagonalError)) →
                                                    (instLTNat.lt 0 k.val →
                                                        ∀ (i : Fin m),
                                                          Eq (Q i k)
                                                            (instHAdd.hAdd (instHDiv.hDiv (v i) (R k k))
                                                              (normalizationError i))) →
                                                      Real.instLT.lt 0 (R k k) →
                                                        (∀ (j : Fin n),
                                                            Real.instLE.le (abs (projectionError j))
                                                              (instHMul.hMul localErrorScale epsilonM)) →
                                                          (∀ (i : Fin m),
                                                              Real.instLE.le (abs (residualError i))
                                                                (instHMul.hMul localErrorScale epsilonM)) →
                                                            Real.instLE.le (abs psiError)
                                                                (instHMul.hMul localErrorScale epsilonM) →
                                                              Real.instLE.le (abs phiError)
                                                                  (instHMul.hMul localErrorScale epsilonM) →
                                                                Real.instLE.le (abs diagonalError)
                                                                    (instHMul.hMul localErrorScale epsilonM) →
                                                                  (∀ (i : Fin m),
                                                                      Real.instLE.le (abs (normalizationError i))
                                                                        (instHMul.hMul localErrorScale epsilonM)) →
                                                                    HighamBench.P11CGSPColumnTrace A Q R epsilonM k
```

Fully explicit type:

```lean
{m n : Nat} →
  {A Q : HighamBench.P11RectMatrix m n} →
    {R : HighamBench.P11Matrix n} →
      {epsilonM : Real} →
        {k : Fin n} →
          (s : Fin n → Real) →
            (v : Fin m → Real) →
              (psi phi : Real) →
                (projectionError : Fin n → Real) →
                  (residualError : Fin m → Real) →
                    (psiError phiError diagonalError : Real) →
                      (normalizationError : Fin m → Real) →
                        (localErrorScale : Real) →
                          (local_error_scale_nonneg :
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                localErrorScale) →
                            (projection_support :
                                ∀ (j : Fin n),
                                  @LE.le.{0} Nat instLENat (@Fin.val n k) (@Fin.val n j) →
                                    @Eq.{1} Real (s j)
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                              (first_diagonal_relation :
                                  @Eq.{1} Nat (@Fin.val n k)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                    @Eq.{1} Real (R k k)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@HighamBench.p11CGSPColumnNorm m n A k) diagonalError)) →
                                (first_normalization_relation :
                                    @Eq.{1} Nat (@Fin.val n k)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                      ∀ (i : Fin m),
                                        @Eq.{1} Real (Q i k)
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                              (A i k) (R k k))
                                            (normalizationError i))) →
                                  (later_projection_relation :
                                      @LT.lt.{0} Nat instLTNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.val n k) →
                                        ∀ (j : Fin n),
                                          @LT.lt.{0} Nat instLTNat (@Fin.val n j) (@Fin.val n k) →
                                            @Eq.{1} Real (s j)
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@HighamBench.p11CGSPProjectionEntry m n A Q j k)
                                                (projectionError j))) →
                                    (later_upper_factor_relation :
                                        @LT.lt.{0} Nat instLTNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                            (@Fin.val n k) →
                                          ∀ (j : Fin n),
                                            @LT.lt.{0} Nat instLTNat (@Fin.val n j) (@Fin.val n k) →
                                              @Eq.{1} Real (R j k) (s j)) →
                                      (later_residual_relation :
                                          @LT.lt.{0} Nat instLTNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              (@Fin.val n k) →
                                            ∀ (i : Fin m),
                                              @Eq.{1} Real (v i)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HighamBench.p11CGSPResidualEntry m n A Q s i k)
                                                  (residualError i))) →
                                        (later_psi_relation :
                                            @LT.lt.{0} Nat instLTNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@Fin.val n k) →
                                              @Eq.{1} Real psi
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HighamBench.p11CGSPColumnNorm m n A k) psiError)) →
                                          (later_phi_relation :
                                              @LT.lt.{0} Nat instLTNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                  (@Fin.val n k) →
                                                @Eq.{1} Real phi
                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                    (@HighamBench.p11VecNorm n s) phiError)) →
                                            (later_psi_nonneg :
                                                @LT.lt.{0} Nat instLTNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                    (@Fin.val n k) →
                                                  @LE.le.{0} Real Real.instLE
                                                    (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                      (@Zero.toOfNat0.{0} Real Real.instZero))
                                                    psi) →
                                              (later_phi_nonneg :
                                                  @LT.lt.{0} Nat instLTNat
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                      (@Fin.val n k) →
                                                    @LE.le.{0} Real Real.instLE
                                                      (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                        (@Zero.toOfNat0.{0} Real Real.instZero))
                                                      phi) →
                                                (later_pythagorean_domain :
                                                    @LT.lt.{0} Nat instLTNat
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                        (@Fin.val n k) →
                                                      @LE.le.{0} Real Real.instLE
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))
                                                        (@HSub.hSub.{0, 0, 0} Real Real Real
                                                          (@instHSub.{0} Real Real.instSub) psi phi)) →
                                                  (later_diagonal_relation :
                                                      @LT.lt.{0} Nat instLTNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                          (@Fin.val n k) →
                                                        @Eq.{1} Real (R k k)
                                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd)
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (Real.sqrt
                                                                (@HSub.hSub.{0, 0, 0} Real Real Real
                                                                  (@instHSub.{0} Real Real.instSub) psi phi))
                                                              (Real.sqrt
                                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                  (@instHAdd.{0} Real Real.instAdd) psi phi)))
                                                            diagonalError)) →
                                                    (later_normalization_relation :
                                                        @LT.lt.{0} Nat instLTNat
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                              (instOfNatNat (nat_lit 0)))
                                                            (@Fin.val n k) →
                                                          ∀ (i : Fin m),
                                                            @Eq.{1} Real (Q i k)
                                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                (@instHAdd.{0} Real Real.instAdd)
                                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                  (@instHDiv.{0} Real
                                                                    (@DivInvMonoid.toDiv.{0} Real
                                                                      Real.instDivInvMonoid))
                                                                  (v i) (R k k))
                                                                (normalizationError i))) →
                                                      (diagonal_pos :
                                                          @LT.lt.{0} Real Real.instLT
                                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                              (@Zero.toOfNat0.{0} Real Real.instZero))
                                                            (R k k)) →
                                                        (projection_error_bound :
                                                            ∀ (j : Fin n),
                                                              @LE.le.{0} Real Real.instLE
                                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                  (projectionError j))
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul) localErrorScale
                                                                  epsilonM)) →
                                                          (residual_error_bound :
                                                              ∀ (i : Fin m),
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    (residualError i))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul) localErrorScale
                                                                    epsilonM)) →
                                                            (psi_error_bound :
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    psiError)
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul) localErrorScale
                                                                    epsilonM)) →
                                                              (phi_error_bound :
                                                                  @LE.le.{0} Real Real.instLE
                                                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                      phiError)
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul) localErrorScale
                                                                      epsilonM)) →
                                                                (diagonal_error_bound :
                                                                    @LE.le.{0} Real Real.instLE
                                                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                        diagonalError)
                                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                        (@instHMul.{0} Real Real.instMul)
                                                                        localErrorScale epsilonM)) →
                                                                  (normalization_error_bound :
                                                                      ∀ (i : Fin m),
                                                                        @LE.le.{0} Real Real.instLE
                                                                          (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                            (normalizationError i))
                                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                            (@instHMul.{0} Real Real.instMul)
                                                                            localErrorScale epsilonM)) →
                                                                    @HighamBench.P11CGSPColumnTrace m n A Q R epsilonM k
```

### D038: `HighamBench.p11RectNormalEquationResidual`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `06dacf14b4a26dd49f7011d96c291c69e6764b535d764a9c3677303af781b31f`

Type:

```lean
{m k : Nat} → HighamBench.P11RectMatrix m k → HighamBench.P11Matrix k → HighamBench.P11Matrix k
```

Fully explicit type:

```lean
{m k : Nat} → (A : HighamBench.P11RectMatrix m k) → (R : HighamBench.P11Matrix k) → HighamBench.P11Matrix k
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A R =>
  instHSub.hSub (HighamBench.p11MatMul k (HighamBench.p11Transpose R) R)
    (HighamBench.p11RectMatMul (HighamBench.p11RectTranspose A) A)
```

### D039: `HighamBench.p11CGSPColumnNorm`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `99fe77ccf9737a94b82317491c1334cf7cfe793d722977a87a1a2115c1f149b5`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P11RectMatrix m n) → (k : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A k => HighamBench.p11VecNorm fun i => A i k
```

### D040: `HighamBench.p11CGSPProjectionEntry`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `dca32c61dee9c90e394aae47d5d2e590f908f116a6215a5d22cf0a8c416196d3`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → HighamBench.P11RectMatrix m n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A Q : HighamBench.P11RectMatrix m n) → (j k : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A Q j k => Finset.univ.sum fun i => instHMul.hMul (Q i j) (A i k)
```

### D041: `HighamBench.p11CGSPResidualEntry`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a676408fc9e88ec153fd942b4bb8e72a40b00f2efa8fc9778c3a4302aaa10278`

Type:

```lean
{m n : Nat} → HighamBench.P11RectMatrix m n → HighamBench.P11RectMatrix m n → (Fin n → Real) → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A Q : HighamBench.P11RectMatrix m n) → (s : Fin n → Real) → (i : Fin m) → (k : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A Q s i k =>
  instHSub.hSub (A i k)
    ((Finset.filter (fun j => instLTNat.lt j.val k.val) Finset.univ).sum fun j => instHMul.hMul (Q i j) (s j))
```

### D042: `HighamBench.p11Transpose`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `df902c1363a2c4d532efa052274ff9934e76027f6f628e6b7d8cbc207418820a`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.transpose A
```

### D043: `HighamBench.p11VecNorm`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ee71eed419dd20d9388ea70276d8f8cce111468786138bd0438db1313846d0c6`

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

### D044: `Fin`

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

### D045: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D046: `HAdd.hAdd`

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

### D047: `HMul.hMul`

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

### D048: `HPow.hPow`

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

### D049: `LE.le`

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

### D050: `Monoid.toNatPow`

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

### D051: `Nat`

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

### D052: `OfNat.ofNat`

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

### D053: `Real`

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

### D054: `Real.instAdd`

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

### D055: `Real.instLE`

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

### D056: `Real.instMonoid`

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

### D057: `Real.instMul`

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

### D058: `instAddNat`

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

### D059: `instHAdd`

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

### D060: `instHMul`

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

### D061: `instHPow`

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

### D062: `instOfNatNat`

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

### D063: `Fin.castLE`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `741eedcc1330cedb8ff0a69095d6df1438c40a8c734f1526dc385e45bb9ae135`

Type:

```lean
{n m : Nat} → instLENat.le n m → Fin n → Fin m
```

Fully explicit type:

```lean
{n m : Nat} → (h : @LE.le.{0} Nat instLENat n m) → (i : Fin n) → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} h i => ⟨i.val, ⋯⟩
```

### D064: `Fin.fintype`

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

### D065: `HSub.hSub`

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

### D066: `Matrix`

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

### D067: `Matrix.instL2OpNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.CStarAlgebra.Matrix`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D068: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D069: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D070: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D071: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D072: `Real.instNatCast`

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

### D073: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D074: `Real.instSub`

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

### D075: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D076: `instHSub`

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

### D077: `instOfNatAtLeastTwo`

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

### D078: `DivInvMonoid.toDiv`

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

### D079: `Eq`

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

### D080: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D081: `HDiv.hDiv`

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

### D082: `LT.lt`

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

### D083: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D084: `Matrix.mulVec`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `715de3f0bd9e7bcf034726e1efbf1b4dad42a16e2ce790d4403774d16ed5b549`

Type:

```lean
{m : Type u_2} →
  {n : Type u_3} → {α : Type v} → [NonUnitalNonAssocSemiring α] → [Fintype n] → Matrix m n α → (n → α) → m → α
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} →
      [NonUnitalNonAssocSemiring.{v} α] → [Fintype.{u_3} n] → (M : Matrix.{u_2, u_3, v} m n α) → (v : n → α) → m → α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [NonUnitalNonAssocSemiring α] [Fintype n] M v x =>
  have i := x;
  dotProduct (fun j => M i j) v
```

### D085: `Matrix.one`

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

### D086: `Matrix.transpose`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a0ee2c3649fa412f4b56ce3f375ef2f2d84b6b21507e1c4a93e90d3b9562973e`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Matrix m n α → Matrix n m α
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → (M : Matrix.{u_2, u_3, v} m n α) → Matrix.{u_3, u_2, v} n m α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} M => EquivLike.toFunLike.coe Matrix.of fun x y => M y x
```

### D087: `Nat.AtLeastTwo`

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

### D088: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D089: `NonUnitalCommRing.toNonUnitalNonAssocCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3bd70454a5180abed6221bb3f73922ebc30c10136298d23eb30d358cdd2fdb82`

Type:

```lean
{α : Type u} → [self : NonUnitalCommRing α] → NonUnitalNonAssocCommRing α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalCommRing.{u} α] → NonUnitalNonAssocCommRing.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalNonAssocRing := self.toNonUnitalNonAssocRing, mul_comm := ⋯ }
```

### D090: `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1082112ee2b1424cb7e1eff69df85640d23793811157d8a4401f364710bc21d2`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing α] → NonUnitalNonAssocRing α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing.{u} α] → NonUnitalNonAssocRing.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocCommRing α] => self.1
```

### D091: `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ffc3b0b49d777bb976662d9282026e03ef869205e45f90008bd1659a4e78f2d7`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocRing α] → NonUnitalNonAssocSemiring α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocRing.{u} α] → NonUnitalNonAssocSemiring.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toAddMonoid := self.toAddMonoid, add_comm := ⋯, toMul := self.toMul, left_distrib := ⋯, right_distrib := ⋯,
    zero_mul := ⋯, mul_zero := ⋯ }
```

### D092: `NonUnitalNormedCommRing.toNonUnitalCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4a44c0a0630b1766c12bb0c5456f4f914c813b6dcb179e8b3d87084d495efd1f`

Type:

```lean
{α : Type u_5} → [self : NonUnitalNormedCommRing α] → NonUnitalCommRing α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : NonUnitalNormedCommRing.{u_5} α] → NonUnitalCommRing.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalRing := self.toNonUnitalRing, mul_comm := ⋯ }
```

### D093: `NormedCommRing.toNonUnitalNormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ce5ba4f454145f64923f4d555eb95891cb66dc2df21d2ef730bfa600ea6a22e5`

Type:

```lean
{α : Type u_2} → [β : NormedCommRing α] → NonUnitalNormedCommRing α
```

Fully explicit type:

```lean
{α : Type u_2} → [β : NormedCommRing.{u_2} α] → NonUnitalNormedCommRing.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : NormedCommRing α] =>
  { toNorm := β.toNorm, toAddMonoid := β.toAddMonoid, toNeg := β.toNeg, toSub := β.toSub, sub_eq_add_neg := ⋯,
    zsmul := β.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯,
    toMul := β.toMul, left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    toMetricSpace := β.toMetricSpace, dist_eq := ⋯, norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D094: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D095: `Real.instAddCommMonoid`

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

### D096: `Real.instDivInvMonoid`

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

### D097: `Real.instLT`

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

### D098: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D099: `Real.instZero`

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

### D100: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `69cccc1e864661e103785f4a2712b9ad164d845c03b7737801c37e5ac852bad7`

Type:

```lean
NormedCommRing Real
```

Fully explicit type:

```lean
NormedCommRing.{0} Real
```

Definition body (one-level semantic boundary):

```lean
let __src := Real.normedAddCommGroup;
let __src_1 := Real.commRing;
{ toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := Real.normedCommRing._proof_1,
  toMul := __src_1.toMul, left_distrib := Real.normedCommRing._proof_2, right_distrib := Real.normedCommRing._proof_3,
  zero_mul := Real.normedCommRing._proof_4, mul_zero := Real.normedCommRing._proof_5,
  mul_assoc := Real.normedCommRing._proof_6, toOne := __src_1.toOne, one_mul := Real.normedCommRing._proof_7,
  mul_one := Real.normedCommRing._proof_8, toNatCast := __src_1.toNatCast, natCast_zero := Real.normedCommRing._proof_9,
  natCast_succ := Real.normedCommRing._proof_10, npow := __src_1.npow, npow_zero := Real.normedCommRing._proof_11,
  npow_succ := Real.normedCommRing._proof_12, toNeg := __src.toNeg, toSub := __src.toSub,
  sub_eq_add_neg := Real.normedCommRing._proof_13, zsmul := __src.zsmul, zsmul_zero' := Real.normedCommRing._proof_14,
  zsmul_succ' := Real.normedCommRing._proof_15, zsmul_neg' := Real.normedCommRing._proof_16,
  neg_add_cancel := Real.normedCommRing._proof_17, toIntCast := __src_1.toIntCast,
  intCast_ofNat := Real.normedCommRing._proof_18, intCast_negSucc := Real.normedCommRing._proof_19,
  toMetricSpace := __src.toMetricSpace, dist_eq := ⋯, norm_mul_le := Real.normedCommRing._proof_20, mul_comm := ⋯ }
```

### D101: `Real.sqrt`

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

### D102: `Zero.toOfNat0`

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

### D103: `instDecidableEqNat`

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

### D104: `instHDiv`

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

### D105: `instLENat`

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

### D106: `instLTNat`

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

### D107: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D108: `Matrix.add`

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

### D109: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D110: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D111: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D112: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `cc2bad5c5cc6aa2b196abe33b9083d127ab69155f1189766c3500bb83412c7df`

Type:

```lean
{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
```

Fully explicit type:

```lean
{α : Type u_1} → (p : α → Prop) → [@DecidablePred.{u_1 + 1} α p] → (s : Finset.{u_1} α) → Finset.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p [DecidablePred p] s => { val := Multiset.filter p s.val, nodup := ⋯ }
```

### D113: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D114: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D115: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Fully explicit type:

```lean
(n m : Nat) → Decidable (@LT.lt.{0} Nat instLTNat n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
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

### `HighamBench.P11Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P11Definitions.lean`
SHA-256: `6756f18215387ae4f685e6cd69598895af8117ed6fe81c264b4591f04d20e40d`

```lean
import HighamBench.Core
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

namespace HighamBench

/-- Square real matrices used for the finite P11 certificates. -/
abbrev P11Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Rectangular real matrices used by the P11 CGS-P execution model. -/
abbrev P11RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Matrix multiplication in the P11 setting. -/
noncomputable def p11MatMul (n : ℕ) (A B : P11Matrix n) : P11Matrix n :=
  A * B

/-- Matrix transpose in the P11 setting. -/
def p11Transpose {n : ℕ} (A : P11Matrix n) : P11Matrix n :=
  A.transpose

/-- The identity matrix. -/
def p11Identity (n : ℕ) : P11Matrix n :=
  1

/-- Explicit Frobenius norm for the condition-neutral public statements. -/
noncomputable def p11FrobNorm {n : ℕ} (A : P11Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- Explicit Euclidean norm for a finite real vector. -/
noncomputable def p11VecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Matrix-vector multiplication. -/
noncomputable def p11MatVec {n : ℕ} (A : P11Matrix n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  A.mulVec x

/-- The first valid column index of a nonempty finite matrix. -/
def p11FirstIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- The leading `(k+1) x (k+1)` block of a square matrix. -/
def p11LeadingBlock {n : ℕ} (R : P11Matrix n) (k : Fin n) :
    P11Matrix (k.val + 1) :=
  fun i j =>
    R (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) i)
      (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) j)

/-- The first `k+1` columns of a rectangular matrix. A `Fin n` index is
zero-based and therefore represents the paper's positive prefix index `k+1`. -/
def p11ColumnPrefix {m n : ℕ} (A : P11RectMatrix m n) (k : Fin n) :
    P11RectMatrix m (k.val + 1) :=
  fun i j => A i (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) j)

/-- Exact induced spectral 2-norm used in P11. -/
noncomputable def p11OpNorm2 {n : ℕ} (A : P11Matrix n) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- Exact rectangular spectral 2-norm used for the prefixes in Theorem 1. -/
noncomputable def p11RectOpNorm2 {m n : ℕ}
    (A : P11RectMatrix m n) : ℝ :=
  @norm (Matrix (Fin m) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- The paper's first residual coefficient `c1(m,k)`. -/
noncomputable def p11C1 (m k : ℕ) : ℝ :=
  if k = 1 then 1
  else
    2 * Real.sqrt (2 * (m : ℝ)) * (k : ℝ) +
      2 * Real.sqrt (k : ℝ)

/-- The paper's normal-equations coefficient `c2(m,k)`. -/
noncomputable def p11C2 (m k : ℕ) : ℝ :=
  if k = 1 then (m : ℝ) + 2
  else
    ((7 : ℝ) / 2) * (m : ℝ) * (k : ℝ) ^ 2 -
      ((3 : ℝ) / 2) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ)

/-- The paper's condition-(3) coefficient `c4 = c2 + 2*c1`. -/
noncomputable def p11C4 (m k : ℕ) : ℝ :=
  p11C2 m k + 2 * p11C1 m k

/-- The paper's norm-comparison coefficient `c3 = c2/2`. -/
noncomputable def p11C3 (m k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * p11C2 m k

/-- Exact spectral condition number represented by a matrix and certified inverse. -/
noncomputable def p11Kappa2 {n : ℕ} (R Rinv : P11Matrix n) : ℝ :=
  p11OpNorm2 R * p11OpNorm2 Rinv

/-- Normalized-range floating-point certificate for Algorithm 2's first
column division. It is exactly the standard-error-bound representation used
immediately before equation (16), without assigning unprinted entries to G1. -/
structure P11NormalizedFirstColumn {m : ℕ}
    (a q : Fin m → ℝ) (r11 epsilonM : ℝ) where
  G1 : P11Matrix m
  denominator_pos : 0 < r11
  representation : ∀ i : Fin m,
    q i = (a i + p11MatVec G1 a i) / r11
  opNorm_bound : p11OpNorm2 G1 ≤ epsilonM

/-- Proof-carrying execution contract for the first column of CGS-P under the
standing hypotheses of Theorem 1. Real-valued error equations represent only
the normalized finite regime assumed by the paper. -/
structure P11CGSPFirstColumnRun (m n : ℕ) where
  row_dimension_pos : 0 < m
  column_dimension_pos : 0 < n
  columns_le_rows : n ≤ m
  A : P11RectMatrix m n
  Q : P11RectMatrix m n
  R : P11Matrix n
  full_column_rank : Function.Injective A.mulVec
  R_upper_triangular : ∀ i j : Fin n, j.val < i.val → R i j = 0
  epsilonM : ℝ
  epsilonM_nonneg : 0 ≤ epsilonM
  leadingInverse : ∀ k : Fin n, P11Matrix (k.val + 1)
  leading_left_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (leadingInverse k) (p11LeadingBlock R k) =
      p11Identity (k.val + 1)
  leading_right_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (p11LeadingBlock R k) (leadingInverse k) =
      p11Identity (k.val + 1)
  condition_3 : ∀ k : Fin n,
    p11C4 m (k.val + 1) * epsilonM *
        p11Kappa2 (p11LeadingBlock R k) (leadingInverse k) ^ 2 < 1
  first_normalization :
    P11NormalizedFirstColumn
      (fun i => A i (p11FirstIndex column_dimension_pos))
      (fun i => Q i (p11FirstIndex column_dimension_pos))
      (R (p11FirstIndex column_dimension_pos)
        (p11FirstIndex column_dimension_pos))
      epsilonM

/-- The one-column input matrix `A1`. -/
def p11A1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11RectMatrix m 1 :=
  fun i _ => run.A i (p11FirstIndex run.column_dimension_pos)

/-- The one-column computed matrix `Q1`. -/
def p11Q1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11RectMatrix m 1 :=
  fun i _ => run.Q i (p11FirstIndex run.column_dimension_pos)

/-- The one-by-one computed leading factor `R1`. -/
def p11R1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11Matrix 1 :=
  fun _ _ => run.R (p11FirstIndex run.column_dimension_pos)
    (p11FirstIndex run.column_dimension_pos)

/-- Rectangular matrix multiplication for the P11 first-column residual. -/
noncomputable def p11RectMatMul {m n p : ℕ}
    (A : P11RectMatrix m n) (B : P11RectMatrix n p) : P11RectMatrix m p :=
  A * B

/-- The exact post-analysis one-column residual `A1 - Q1*R1`. -/
noncomputable def p11FirstColumnFactorizationResidual {m n : ℕ}
    (run : P11CGSPFirstColumnRun m n) : P11RectMatrix m 1 :=
  p11A1 run - p11RectMatMul (p11Q1 run) (p11R1 run)

/-- The exact vector residual `a1 - q1*r11`. -/
noncomputable def p11FirstColumnResidualVector {m n : ℕ}
    (run : P11CGSPFirstColumnRun m n) : Fin m → ℝ :=
  fun i =>
    run.A i (p11FirstIndex run.column_dimension_pos) -
      run.Q i (p11FirstIndex run.column_dimension_pos) *
        run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos)

/-- The spectral 2-norm of a one-column matrix, exactly its column's Euclidean norm. -/
noncomputable def p11FirstColumnMatrixNorm2 {m : ℕ}
    (A : P11RectMatrix m 1) : ℝ :=
  p11VecNorm (fun i => A i 0)

/-- The complete exact first-column residual identity and norm chain in (16). -/
structure P11Equation16 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) : Prop where
  normalization_relation : ∀ i : Fin m,
    run.Q i (p11FirstIndex run.column_dimension_pos) =
      (run.A i (p11FirstIndex run.column_dimension_pos) +
          p11MatVec run.first_normalization.G1
            (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i) /
        run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos)
  perturbation_opNorm_bound :
    p11OpNorm2 run.first_normalization.G1 ≤ run.epsilonM
  factorization_residual_identity :
    p11FirstColumnFactorizationResidual run =
      fun i _ => p11FirstColumnResidualVector run i
  residual_action_identity :
    p11FirstColumnResidualVector run =
      fun i =>
        -p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i
  matrix_vector_norm_identity :
    p11FirstColumnMatrixNorm2 (p11FirstColumnFactorizationResidual run) =
      p11VecNorm (p11FirstColumnResidualVector run)
  residual_action_norm_identity :
    p11VecNorm (p11FirstColumnResidualVector run) =
      p11VecNorm
        (p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)))
  operator_action_bound :
    p11VecNorm
        (p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos))) ≤
      p11OpNorm2 run.first_normalization.G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))
  machine_unit_bound :
    p11OpNorm2 run.first_normalization.G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) ≤
      run.epsilonM *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))

/-- The loss-of-orthogonality matrix appearing in Theorem 1(7). -/
noncomputable def p11OrthogonalityDefect {n : ℕ}
    (Q : P11Matrix n) : P11Matrix n :=
  p11Identity n - p11MatMul n (p11Transpose Q) Q

/-- The normal-equations residual in Theorem 1(5). -/
noncomputable def p11NormalEquationResidual {n : ℕ}
    (A R : P11Matrix n) : P11Matrix n :=
  p11MatMul n (p11Transpose R) R -
    p11MatMul n (p11Transpose A) A

/-- The exact inner residual in the appendix derivation of Theorem 1(7). -/
noncomputable def p11DefectCore {n : ℕ}
    (A dA R : P11Matrix n) : P11Matrix n :=
  p11NormalEquationResidual A R -
    p11MatMul n (p11Transpose A) dA -
    p11MatMul n (p11Transpose dA) A -
    p11MatMul n (p11Transpose dA) dA

/-- Transpose of a rectangular P11 matrix. -/
def p11RectTranspose {m n : ℕ}
    (A : P11RectMatrix m n) : P11RectMatrix n m :=
  A.transpose

/-- The rectangular loss-of-orthogonality matrix `I - Q^T Q`. -/
noncomputable def p11RectOrthogonalityDefect {m k : ℕ}
    (Q : P11RectMatrix m k) : P11Matrix k :=
  p11Identity k - p11RectMatMul (p11RectTranspose Q) Q

/-- The rectangular normal-equations residual `R^T R - A^T A`. -/
noncomputable def p11RectNormalEquationResidual {m k : ℕ}
    (A : P11RectMatrix m k) (R : P11Matrix k) : P11Matrix k :=
  p11MatMul k (p11Transpose R) R -
    p11RectMatMul (p11RectTranspose A) A

/-- The exact rectangular inner residual in the derivation of Theorem 1(7). -/
noncomputable def p11RectDefectCore {m k : ℕ}
    (A dA : P11RectMatrix m k) (R : P11Matrix k) : P11Matrix k :=
  p11RectNormalEquationResidual A R -
    p11RectMatMul (p11RectTranspose A) dA -
    p11RectMatMul (p11RectTranspose dA) A -
    p11RectMatMul (p11RectTranspose dA) dA

/-- Exact Euclidean norm of one input column in Algorithm 2. -/
noncomputable def p11CGSPColumnNorm {m n : ℕ}
    (A : P11RectMatrix m n) (k : Fin n) : ℝ :=
  p11VecNorm fun i ↦ A i k

/-- Exact inner product underlying one entry of `s_k = Q_(k-1)^T a_k`. -/
noncomputable def p11CGSPProjectionEntry {m n : ℕ}
    (A Q : P11RectMatrix m n) (j k : Fin n) : ℝ :=
  ∑ i : Fin m, Q i j * A i k

/-- Exact residual underlying `v_k = a_k - Q_(k-1) s_k`. -/
noncomputable def p11CGSPResidualEntry {m n : ℕ}
    (A Q : P11RectMatrix m n) (s : Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  A i k - ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < k.val),
    Q i j * s j

/-- One column of a successful normalized-range CGS-P execution. The named
local errors expose a permissive first-order envelope for the pseudo-code
operations whose primitive evaluation order the paper leaves unspecified. -/
structure P11CGSPColumnTrace {m n : ℕ}
    (A Q : P11RectMatrix m n) (R : P11Matrix n)
    (epsilonM : ℝ) (k : Fin n) where
  s : Fin n → ℝ
  v : Fin m → ℝ
  psi : ℝ
  phi : ℝ
  projectionError : Fin n → ℝ
  residualError : Fin m → ℝ
  psiError : ℝ
  phiError : ℝ
  diagonalError : ℝ
  normalizationError : Fin m → ℝ
  localErrorScale : ℝ
  local_error_scale_nonneg : 0 ≤ localErrorScale
  projection_support : ∀ j : Fin n, k.val ≤ j.val → s j = 0
  first_diagonal_relation : k.val = 0 →
    R k k = p11CGSPColumnNorm A k + diagonalError
  first_normalization_relation : k.val = 0 → ∀ i : Fin m,
    Q i k = A i k / R k k + normalizationError i
  later_projection_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val →
      s j = p11CGSPProjectionEntry A Q j k + projectionError j
  later_upper_factor_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val → R j k = s j
  later_residual_relation : 0 < k.val → ∀ i : Fin m,
    v i = p11CGSPResidualEntry A Q s i k + residualError i
  later_psi_relation : 0 < k.val →
    psi = p11CGSPColumnNorm A k + psiError
  later_phi_relation : 0 < k.val →
    phi = p11VecNorm s + phiError
  later_psi_nonneg : 0 < k.val → 0 ≤ psi
  later_phi_nonneg : 0 < k.val → 0 ≤ phi
  later_pythagorean_domain : 0 < k.val → 0 ≤ psi - phi
  later_diagonal_relation : 0 < k.val →
    R k k = Real.sqrt (psi - phi) * Real.sqrt (psi + phi) + diagonalError
  later_normalization_relation : 0 < k.val → ∀ i : Fin m,
    Q i k = v i / R k k + normalizationError i
  diagonal_pos : 0 < R k k
  projection_error_bound : ∀ j,
    |projectionError j| ≤ localErrorScale * epsilonM
  residual_error_bound : ∀ i,
    |residualError i| ≤ localErrorScale * epsilonM
  psi_error_bound : |psiError| ≤ localErrorScale * epsilonM
  phi_error_bound : |phiError| ≤ localErrorScale * epsilonM
  diagonal_error_bound : |diagonalError| ≤ localErrorScale * epsilonM
  normalization_error_bound : ∀ i,
    |normalizationError i| ≤ localErrorScale * epsilonM

/-- The source-level data used for one prefix in the proof of Theorem 1(7).
The three coefficients expose the otherwise unspecified finite constants in
the `O(epsilonM^2)` terms of (4), (5), and the reversed form of (6). -/
structure P11Theorem1PrefixCertificate {m k : ℕ}
    (A Q : P11RectMatrix m k) (R : P11Matrix k) (epsilonM : ℝ) where
  deltaA : P11RectMatrix m k
  normalEquationResidual : P11Matrix k
  factorizationSecondOrderCoeff : ℝ
  normalEquationSecondOrderCoeff : ℝ
  reverseNormSecondOrderCoeff : ℝ
  factorization_second_order_nonneg : 0 ≤ factorizationSecondOrderCoeff
  normal_equation_second_order_nonneg :
    0 ≤ normalEquationSecondOrderCoeff
  reverse_norm_second_order_nonneg : 0 ≤ reverseNormSecondOrderCoeff
  factorization_relation : p11RectMatMul Q R = A + deltaA
  normal_equation_relation :
    normalEquationResidual = p11RectNormalEquationResidual A R
  factorization_bound :
    p11RectOpNorm2 deltaA ≤
      p11C1 m k * p11RectOpNorm2 A * epsilonM +
        factorizationSecondOrderCoeff * epsilonM ^ 2
  normal_equation_bound :
    p11OpNorm2 normalEquationResidual ≤
      p11C2 m k * p11RectOpNorm2 A ^ 2 * epsilonM +
        normalEquationSecondOrderCoeff * epsilonM ^ 2
  reverse_norm_bound :
    p11RectOpNorm2 A ≤
      (1 + p11C3 m k * epsilonM) * p11OpNorm2 R +
        reverseNormSecondOrderCoeff * epsilonM ^ 2

/-- A proof-carrying successful normalized-range CGS-P execution in the
analytic model of Theorem 1. It keeps one rectangular input and one computed
`Q,R` pair, then links every positive leading prefix to equations (3)--(6).
The paper does not specify a complete primitive-operation semantics, so this
contract records exactly the real-valued execution facts used to derive (7). -/
structure P11CGSPTheorem1Run (m n : ℕ) where
  row_dimension_pos : 0 < m
  column_dimension_pos : 0 < n
  columns_le_rows : n ≤ m
  A : P11RectMatrix m n
  Q : P11RectMatrix m n
  R : P11Matrix n
  full_column_rank : Function.Injective A.mulVec
  R_upper_triangular : ∀ i j : Fin n, j.val < i.val → R i j = 0
  epsilonM : ℝ
  epsilonM_pos : 0 < epsilonM
  epsilonM_lt_one : epsilonM < 1
  leadingInverse : ∀ k : Fin n, P11Matrix (k.val + 1)
  leading_left_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (leadingInverse k) (p11LeadingBlock R k) =
      p11Identity (k.val + 1)
  leading_right_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (p11LeadingBlock R k) (leadingInverse k) =
      p11Identity (k.val + 1)
  condition_3 : ∀ k : Fin n,
    p11C4 m (k.val + 1) * epsilonM *
        p11Kappa2 (p11LeadingBlock R k) (leadingInverse k) ^ 2 < 1
  algorithm2_trace : ∀ k : Fin n,
    P11CGSPColumnTrace A Q R epsilonM k
  prefixCertificate : ∀ k : Fin n,
    P11Theorem1PrefixCertificate
      (p11ColumnPrefix A k) (p11ColumnPrefix Q k)
      (p11LeadingBlock R k) epsilonM

/-- The explicit finite coefficient multiplying `epsilonM^2` in the repaired
form of Theorem 1(7). It is derived from the three source-level remainder
coefficients fixed by the prefix certificate. -/
noncomputable def p11Theorem1OrthogonalityRemainderCoeff {m n : ℕ}
    (run : P11CGSPTheorem1Run m n) (k : Fin n) : ℝ :=
  let certificate := run.prefixCertificate k
  let a := p11RectOpNorm2 (p11ColumnPrefix run.A k)
  let r := p11OpNorm2 (p11LeadingBlock run.R k)
  let rinv := p11OpNorm2 (run.leadingInverse k)
  let normSlope :=
    p11C3 m (k.val + 1) * r + certificate.reverseNormSecondOrderCoeff
  let aSquareRemainder := 2 * r * normSlope + normSlope ^ 2
  let coreRemainder :=
    certificate.normalEquationSecondOrderCoeff +
      2 * a * certificate.factorizationSecondOrderCoeff +
      (p11C1 m (k.val + 1) * a +
          certificate.factorizationSecondOrderCoeff) ^ 2
  rinv ^ 2 *
    (p11C4 m (k.val + 1) * aSquareRemainder + coreRemainder)

end HighamBench
```
