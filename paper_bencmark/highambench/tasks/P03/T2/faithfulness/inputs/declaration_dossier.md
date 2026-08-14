# Declaration dossier for P03-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p03_t2_normwise_residual_contraction
    {n : ℕ} (run : P03NormwiseIRRun n) (i : ℕ) :
    p03VecInfNorm (p03ExactResidual run (i + 1)) ≤
      p03Alpha run i * p03VecInfNorm (p03ExactResidual run i) +
        p03Beta run i
```

## Elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P03NormwiseIRRun n) (i : Nat),
  Real.instLE.le (HighamBench.p03VecInfNorm (HighamBench.p03ExactResidual run (instHAdd.hAdd i 1)))
    (instHAdd.hAdd
      (instHMul.hMul (HighamBench.p03Alpha run i) (HighamBench.p03VecInfNorm (HighamBench.p03ExactResidual run i)))
      (HighamBench.p03Beta run i))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P03NormwiseIRRun n) (i : Nat),
  @LE.le.{0} Real Real.instLE
    (@HighamBench.p03VecInfNorm n
      (@HighamBench.p03ExactResidual n run
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p03Alpha n run i)
        (@HighamBench.p03VecInfNorm n (@HighamBench.p03ExactResidual n run i)))
      (@HighamBench.p03Beta n run i))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P03Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P03Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P03NormwiseIRRun`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2baf8b280d75137ba8434b04ed73d871d74979f27fa68a9b06f4742d1a3c82ab`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.p03Alpha`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `598780717b374f965680dcf8e652675ef266e1cf73269ba4e28535a33b0bbcc0`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P03NormwiseIRRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHMul.hMul run.uS (instHAdd.hAdd 1 (instHMul.hMul (instHAdd.hAdd 1 run.uS) (HighamBench.p03CorrectionRatio run i)))
```

### D003: `HighamBench.p03Beta`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1602fe63752ac0935aba028edad71a7d504fe3749b02d408c993a897eb9fca95`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P03NormwiseIRRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHAdd.hAdd
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHAdd.hAdd 1 (instHMul.hMul run.uS (HighamBench.p03CorrectionRatio run i)))
          (instHAdd.hAdd 1 run.uS))
        (HighamBench.gamma run.uR (HighamBench.p03MaxAugmentedRowNnz run.A run.b)))
      (instHAdd.hAdd (HighamBench.p03VecInfNorm run.b)
        (instHMul.hMul (HighamBench.p03MatInfNorm run.A) (HighamBench.p03VecInfNorm (run.x i)))))
    (instHMul.hMul (instHMul.hMul run.u (HighamBench.p03MatInfNorm run.A))
      (HighamBench.p03VecInfNorm (run.x (instHAdd.hAdd i 1))))
```

### D004: `HighamBench.p03ExactResidual`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `33447e806ad606c76b495e825cea5874f6b49159bede664f532ee2d02a634179`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P03NormwiseIRRun n) → (i : Nat) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i j => instHSub.hSub (run.b j) (HighamBench.p03MatVec run.A (run.x i) j)
```

### D005: `HighamBench.p03VecInfNorm`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `630b5433cd5c650d5a290840eb04c1dae4b7c98e4d43ea7baf0eeabb16c890bf`

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
fun {n} x => Pi.normedRing.norm x
```

### D006: `HighamBench.P03NormwiseIRRun.A`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `674110d92e49c1d9178618c2fa290b599162041c98df3a8a6a460c683dcb53fe`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D007: `HighamBench.P03NormwiseIRRun.b`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ba0e8bb5aaaf94734ced4a5aeac2fa874e378a7e9bfdf22520704689fe7f1ad1`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D008: `HighamBench.P03NormwiseIRRun.mk`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `85929445fc2ae3277887c947dfbff9fe6b732b1b69ac085f48f7e555e7685cce`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv : Fin n → Fin n → Real) →
      (b : Fin n → Real) →
        (x rHat dHat deltaR deltaX : Nat → Fin n → Real) →
          (uR u uS uF : Real) →
            (c1 c2 : Nat → Real) →
              Real.instLE.le 0 uR →
                Real.instLE.le uR u →
                  Real.instLE.le u uS →
                    Real.instLE.le uS uF →
                      HighamBench.GammaValid uR (HighamBench.p03MaxAugmentedRowNnz A b) →
                        (∀ (i : Nat), Real.instLE.le 0 (c1 i)) →
                          (∀ (i : Nat), Real.instLE.le 0 (c2 i)) →
                            (∀ (z : Fin n → Real) (j : Fin n),
                                Eq (HighamBench.p03MatVec Ainv (HighamBench.p03MatVec A z) j) (z j)) →
                              (∀ (i : Nat) (j : Fin n),
                                  Eq (rHat i j)
                                    (instHAdd.hAdd (instHSub.hSub (b j) (HighamBench.p03MatVec A (x i) j))
                                      (deltaR i j))) →
                                (∀ (i : Nat) (j : Fin n),
                                    Real.instLE.le (abs (deltaR i j))
                                      (instHAdd.hAdd
                                        (instHMul.hMul uS (abs (instHSub.hSub (b j) (HighamBench.p03MatVec A (x i) j))))
                                        (instHMul.hMul
                                          (instHMul.hMul (instHAdd.hAdd 1 uS)
                                            (HighamBench.gamma uR (HighamBench.p03MaxAugmentedRowNnz A b)))
                                          (instHAdd.hAdd (abs (b j))
                                            (HighamBench.p03MatVec (HighamBench.p03MatAbs A)
                                              (HighamBench.p03VecAbs (x i)) j))))) →
                                  (∀ (i : Nat),
                                      Real.instLE.le
                                        (HighamBench.p03VecInfNorm fun j =>
                                          instHSub.hSub (rHat i j) (HighamBench.p03MatVec A (dHat i) j))
                                        (instHMul.hMul uS
                                          (instHAdd.hAdd
                                            (instHMul.hMul (instHMul.hMul (c1 i) (HighamBench.p03MatInfNorm A))
                                              (HighamBench.p03VecInfNorm (dHat i)))
                                            (instHMul.hMul (c2 i) (HighamBench.p03VecInfNorm (rHat i)))))) →
                                    (∀ (i : Nat) (j : Fin n),
                                        Eq (x (instHAdd.hAdd i 1) j)
                                          (instHAdd.hAdd (instHAdd.hAdd (x i j) (dHat i j)) (deltaX i j))) →
                                      (∀ (i : Nat) (j : Fin n),
                                          Real.instLE.le (abs (deltaX i j))
                                            (instHMul.hMul u (abs (x (instHAdd.hAdd i 1) j)))) →
                                        (∀ (i : Nat),
                                            Real.instLT.lt
                                              (instHMul.hMul
                                                (instHMul.hMul (c1 i)
                                                  (instHMul.hMul (HighamBench.p03MatInfNorm Ainv)
                                                    (HighamBench.p03MatInfNorm A)))
                                                uS)
                                              1) →
                                          HighamBench.P03NormwiseIRRun n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (A Ainv : Fin n → Fin n → Real) →
      (b : Fin n → Real) →
        (x rHat dHat deltaR deltaX : Nat → Fin n → Real) →
          (uR u uS uF : Real) →
            (c1 c2 : Nat → Real) →
              (uR_nonneg :
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uR) →
                (uR_le_u : @LE.le.{0} Real Real.instLE uR u) →
                  (u_le_uS : @LE.le.{0} Real Real.instLE u uS) →
                    (uS_le_uF : @LE.le.{0} Real Real.instLE uS uF) →
                      (gamma_valid : HighamBench.GammaValid uR (@HighamBench.p03MaxAugmentedRowNnz n A b)) →
                        (c1_nonneg :
                            ∀ (i : Nat),
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (c1 i)) →
                          (c2_nonneg :
                              ∀ (i : Nat),
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (c2 i)) →
                            (inverse_action :
                                ∀ (z : Fin n → Real) (j : Fin n),
                                  @Eq.{1} Real (@HighamBench.p03MatVec n Ainv (@HighamBench.p03MatVec n A z) j) (z j)) →
                              (residual_equation :
                                  ∀ (i : Nat) (j : Fin n),
                                    @Eq.{1} Real (rHat i j)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (b j)
                                          (@HighamBench.p03MatVec n A (x i) j))
                                        (deltaR i j))) →
                                (residual_error_bound :
                                    ∀ (i : Nat) (j : Fin n),
                                      @LE.le.{0} Real Real.instLE
                                        (@abs.{0} Real Real.lattice Real.instAddGroup (deltaR i j))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) uS
                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                (b j) (@HighamBench.p03MatVec n A (x i) j))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                uS)
                                              (HighamBench.gamma uR (@HighamBench.p03MaxAugmentedRowNnz n A b)))
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@abs.{0} Real Real.lattice Real.instAddGroup (b j))
                                              (@HighamBench.p03MatVec n (@HighamBench.p03MatAbs n A)
                                                (@HighamBench.p03VecAbs n (x i)) j))))) →
                                  (correction_solver_bound :
                                      ∀ (i : Nat),
                                        @LE.le.{0} Real Real.instLE
                                          (@HighamBench.p03VecInfNorm n fun (j : Fin n) =>
                                            @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (rHat i j) (@HighamBench.p03MatVec n A (dHat i) j))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) uS
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (c1 i) (@HighamBench.p03MatInfNorm n A))
                                                (@HighamBench.p03VecInfNorm n (dHat i)))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (c2 i) (@HighamBench.p03VecInfNorm n (rHat i)))))) →
                                    (update_equation :
                                        ∀ (i : Nat) (j : Fin n),
                                          @Eq.{1} Real
                                            (x
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              j)
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (x i j) (dHat i j))
                                              (deltaX i j))) →
                                      (update_error_bound :
                                          ∀ (i : Nat) (j : Fin n),
                                            @LE.le.{0} Real Real.instLE
                                              (@abs.{0} Real Real.lattice Real.instAddGroup (deltaX i j))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                  (x
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    j)))) →
                                        (denominator_condition :
                                            ∀ (i : Nat),
                                              @LT.lt.{0} Real Real.instLT
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (c1 i)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HighamBench.p03MatInfNorm n Ainv)
                                                      (@HighamBench.p03MatInfNorm n A)))
                                                  uS)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne))) →
                                          HighamBench.P03NormwiseIRRun n
```

### D009: `HighamBench.P03NormwiseIRRun.u`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a3fb10d7c083ec41286b507fb6640a1979f308e2e7ae2d16ffc796a57e828e41`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D010: `HighamBench.P03NormwiseIRRun.uR`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a403402c0c81e80f3f287591a1f36b1b15d0c7629fc1bb62b6e9b5870a861319`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.10
```

### D011: `HighamBench.P03NormwiseIRRun.uS`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `45565cc07c86a4d1065e93701d2cf3bced7d97bc8392026d3d31723a6e05b4d7`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.12
```

### D012: `HighamBench.P03NormwiseIRRun.x`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5ab1530ff75c6469b5362d48d8e3cda5decc8e3571cf36cc09a3cdb64b3cd50b`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Nat → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D013: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D014: `HighamBench.p03CorrectionRatio`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `357f32f973132f00434ca60bec05a04d2028443c47a25bc6c803b36ae2ff302e`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P03NormwiseIRRun n) → (i : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run i =>
  instHDiv.hDiv (instHAdd.hAdd (instHMul.hMul (run.c1 i) (HighamBench.p03KappaInf run)) (run.c2 i))
    (instHSub.hSub 1 (instHMul.hMul (instHMul.hMul (run.c1 i) (HighamBench.p03KappaInf run)) run.uS))
```

### D015: `HighamBench.p03MatInfNorm`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `721c937222ae78f5baad347370736d1cac051efc05ff0861ea5f92a7592e1192`

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
fun {n} A => Matrix.linftyOpNormedRing.norm (EquivLike.toFunLike.coe Matrix.of A)
```

### D016: `HighamBench.p03MatVec`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1369ded3dc793c70d72eeba99084d1d0ffc9aac01ed5047bab8b80574697ee32`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → (i : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D017: `HighamBench.p03MaxAugmentedRowNnz`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b7acd2d4a7747b498df1950ab8aec172b4daa2f74d833c651253a350c5e01f7c`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Nat
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (b : Fin n → Real) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b => Finset.univ.sup (HighamBench.p03AugmentedRowNnz A b)
```

### D018: `HighamBench.GammaValid`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `651ef903a8d9a3c8f539284f6c70325cebe6e199aad808cb56d9123f31e258c9`

Type:

```lean
Real → Nat → Prop
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u n => Real.instLT.lt (instHMul.hMul n.cast u) 1
```

### D019: `HighamBench.P03NormwiseIRRun.c1`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fdec424dadaf8c21d703e67ec01ce8195a4367ee3184b0b0c24bf5220942bc6c`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.14
```

### D020: `HighamBench.P03NormwiseIRRun.c2`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `91503422086a5f548bc22f0db00ab56bc53599ed6b8c2488ecb55f10867c3eed`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.15
```

### D021: `HighamBench.p03AugmentedRowNnz`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `bceef9b215e54444cb0e1a8cc9f0527bba3610a2d60ecae1b030ff5f6a412ed0`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Nat
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (b : Fin n → Real) → (i : Fin n) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b i => instHAdd.hAdd (Finset.filter (fun j => Ne (A i j) 0) Finset.univ).card (ite (Ne (b i) 0) 1 0)
```

### D022: `HighamBench.p03KappaInf`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `38f1626c6d5182e2b286cca93f6f0403a411f0bde5adc77a8493592c26d0ab08`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P03NormwiseIRRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run => instHMul.hMul (HighamBench.p03MatInfNorm run.Ainv) (HighamBench.p03MatInfNorm run.A)
```

### D023: `HighamBench.p03MatAbs`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `38cb5eba6c9f4f581ac2d713277c7a673188f086e4561b6ff92c3abd957b934b`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A i j => abs (A i j)
```

### D024: `HighamBench.p03VecAbs`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cbcbc1d3ff3dbe2170b57b8eb1dc87d4298806361ceb82cf64cda83fcd35d815`

Type:

```lean
{n : Nat} → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x i => abs (x i)
```

### D025: `HighamBench.P03NormwiseIRRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `29fe754aa6b330cafa3e1984ecb16c4b23aa53303a3d08fdeafe9ce49c3fc5ad`

Type:

```lean
{n : Nat} → HighamBench.P03NormwiseIRRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P03NormwiseIRRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
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

### D027: `HMul.hMul`

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

### D028: `LE.le`

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

### D029: `Nat`

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

### D030: `OfNat.ofNat`

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

### D031: `Real`

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

### D032: `Real.instAdd`

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

### D033: `Real.instLE`

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

### D034: `Real.instMul`

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

### D035: `instAddNat`

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

### D036: `instHAdd`

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

### D037: `instHMul`

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

### D038: `instOfNatNat`

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

### D039: `Fin`

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

### D040: `Fin.fintype`

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

### D041: `HSub.hSub`

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

### D042: `Norm.norm`

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

### D043: `NormedCommRing.toNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ff5852fa6ac00f6a258a1d8fe950a0ed74f219c79c926896eb081436331a480e`

Type:

```lean
{α : Type u_5} → [self : NormedCommRing α] → NormedRing α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : NormedCommRing.{u_5} α] → NormedRing.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NormedCommRing α] => self.1
```

### D044: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D045: `One.toOfNat1`

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

### D046: `Pi.normedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Lemmas`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f9dab15f307cbf227004c74c0bb06dec60fd13239b8d79b0751df5ec0ca2a0d9`

Type:

```lean
{ι : Type u_3} → {R : ι → Type u_4} → [Fintype ι] → [(i : ι) → NormedRing (R i)] → NormedRing ((i : ι) → R i)
```

Fully explicit type:

```lean
{ι : Type u_3} →
  {R : ι → Type u_4} → [Fintype.{u_3} ι] → [(i : ι) → NormedRing.{u_4} (R i)] → NormedRing.{max u_3 u_4} ((i : ι) → R i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {R} [Fintype ι] [(i : ι) → NormedRing (R i)] =>
  let __src := Pi.seminormedRing;
  have __src_1 := Pi.normedAddCommGroup;
  { toNorm := __src.toNorm, toRing := __src.toRing, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D047: `Real.instOne`

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

### D048: `Real.instSub`

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

### D049: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D050: `instHSub`

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

### D051: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Fully explicit type:

```lean
{F : Sort u_1} →
  {α : outParam.{u_2 + 1} (Sort u_2)} →
    {β : outParam.{max u_2 (u_3 + 1)} (α → Sort u_3)} → [self : DFunLike.{u_1, u_2, u_3} F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D052: `DivInvMonoid.toDiv`

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

### D053: `Eq`

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

### D054: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

Fully explicit type:

```lean
(α : Sort u_1) → (β : Sort u_2) → Sort (max (max 1 u_1) u_2)
```

### D055: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike.{max (max 1 v) u, u, v} (Equiv.{u, v} α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D056: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Fully explicit type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike.{u_1, u_3, u_4} E α β] → FunLike.{u_1, u_3, u_4} E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D057: `Finset.sum`

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

### D058: `Finset.sup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Lattice.Fold`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `dd4c14458f3cc53851b18c831b354790927e7783eeceddbd2bc8e0e17c3e5d98`

Type:

```lean
{α : Type u_2} → {β : Type u_3} → [inst : SemilatticeSup α] → [OrderBot α] → Finset β → (β → α) → α
```

Fully explicit type:

```lean
{α : Type u_2} →
  {β : Type u_3} →
    [inst : SemilatticeSup.{u_2} α] →
      [@OrderBot.{u_2} α
            (@Preorder.toLE.{u_2} α (@PartialOrder.toPreorder.{u_2} α (@SemilatticeSup.toPartialOrder.{u_2} α inst)))] →
        (s : Finset.{u_3} β) → (f : β → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [SemilatticeSup α] [inst_1 : OrderBot α] s f =>
  Finset.fold (fun x1 x2 => SemilatticeSup.toMax.max x1 x2) inst_1.bot f s
```

### D059: `Finset.univ`

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

### D060: `HDiv.hDiv`

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

### D061: `LT.lt`

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

### D062: `Lattice.toSemilatticeSup`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Lattice`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `bb8675de9ef80341811562fa08f748f06f8f8f80063bcb662d0fc47b03a65720`

Type:

```lean
{α : Type u} → [self : Lattice α] → SemilatticeSup α
```

Fully explicit type:

```lean
{α : Type u} → [self : Lattice.{u} α] → SemilatticeSup.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Lattice α] => self.1
```

### D063: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D064: `Matrix.linftyOpNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `63404065ca9f93ab919b13e1ceb99fcf28a63378fa7429eb0ca506c0d76d728c`

Type:

```lean
{n : Type u_4} → {α : Type u_5} → [Fintype n] → [NormedRing α] → [DecidableEq n] → NormedRing (Matrix n n α)
```

Fully explicit type:

```lean
{n : Type u_4} →
  {α : Type u_5} →
    [Fintype.{u_4} n] →
      [NormedRing.{u_5} α] → [DecidableEq.{u_4 + 1} n] → NormedRing.{max u_5 u_4} (Matrix.{u_4, u_4, u_5} n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [Fintype n] [NormedRing α] [DecidableEq n] =>
  let __src := Matrix.linftyOpSemiNormedRing;
  { toNorm := __src.toNorm, toRing := __src.toRing, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D065: `Matrix.of`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2fd11c1f258b666a5be58a830ae21c93bc674ab3014a8a722530d141dddb3638`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Equiv (m → n → α) (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} →
      Equiv.{max (max (u_2 + 1) (u_3 + 1)) (v + 1), max (max (v + 1) (u_3 + 1)) (u_2 + 1)} (m → n → α)
        (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} => Equiv.refl (m → n → α)
```

### D066: `Nat.cast`

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

### D067: `Nat.instLattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Lattice`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `19fdcd181b6efb04e4d40bc23d53b115234103c437893eee6b060857ca880376`

Type:

```lean
Lattice Nat
```

Fully explicit type:

```lean
Lattice.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
LinearOrder.toLattice
```

### D068: `Nat.instOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Nat`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e994168f0ff556be514daaa1c6ea8dab3678a3db7e3ca7bb529a53ef523655a3`

Type:

```lean
OrderBot Nat
```

Fully explicit type:

```lean
@OrderBot.{0} Nat instLENat
```

Definition body (one-level semantic boundary):

```lean
{ bot := 0, bot_le := Nat.zero_le }
```

### D069: `Real.instAddCommMonoid`

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

### D070: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D071: `Real.instDivInvMonoid`

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

### D072: `Real.instLT`

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

### D073: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D074: `Real.instZero`

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

### D075: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D076: `Zero.toOfNat0`

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

### D077: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D078: `instDecidableEqFin`

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

### D079: `instHDiv`

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

### D080: `instLTNat`

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

### D081: `Finset.card`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Card`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `53f5c09b147215efcd8844f0936a32a05334a5f290114ef711ebb1615f4504e4`

Type:

```lean
{α : Type u_1} → Finset α → Nat
```

Fully explicit type:

```lean
{α : Type u_1} → (s : Finset.{u_1} α) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {α} s => s.val.card
```

### D082: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D083: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D084: `Real.decidableEq`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `58b21b2d8719c9bf9f6e23c4dbf1284069f5ce6f35c64915e45284792e8a5bcf`

Type:

```lean
(a b : Real) → Decidable (Eq a b)
```

Fully explicit type:

```lean
(a b : Real) → Decidable (@Eq.{1} Real a b)
```

Definition body (one-level semantic boundary):

```lean
fun a b => inferInstance
```

### D085: `instDecidableNot`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `37aa26a947d5738f12ec544d42841f48b475aa5a77621b11677f5a37fce0c2f9`

Type:

```lean
{p : Prop} → [dp : Decidable p] → Decidable (Not p)
```

Fully explicit type:

```lean
{p : Prop} → [dp : Decidable p] → Decidable (Not p)
```

Definition body (one-level semantic boundary):

```lean
fun {p} [dp : Decidable p] =>
  instDecidableAnd.match_1 (fun dp => Decidable (Not p)) dp (fun hp => Decidable.isFalse ⋯) fun hp =>
    Decidable.isTrue hp
```

### D086: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### `HighamBench.P03Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P03Definitions.lean`
SHA-256: `8187989501a568ea0d68608500696079d547d8b79cdd5f2ee6f74b9a7ec95973`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P03 definitions

Condition-neutral finite matrix/vector notation and the execution contract for
the Carson--Higham three-precision iterative-refinement tasks. This file
contains no evaluated-library import.
-/

namespace HighamBench

open scoped BigOperators

/-- Finite real matrix-vector multiplication used in the P03 paper model. -/
noncomputable def p03MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * x j

/-- Finite real matrix multiplication used in the P03 paper model. -/
noncomputable def p03MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  ∑ j : Fin n, A i j * B j k

/-- Componentwise absolute value of a P03 vector. -/
noncomputable def p03VecAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x i|

/-- Componentwise absolute value of a P03 matrix. -/
noncomputable def p03MatAbs {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |A i j|

/-- Vector infinity norm used in P03. -/
noncomputable def p03VecInfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/-- Induced matrix infinity norm used in P03. -/
noncomputable def p03MatInfNorm {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖(Matrix.of A : Matrix (Fin n) (Fin n) ℝ)‖

/-- Number of nonzeros in one row of the augmented matrix `[A b]`. -/
noncomputable def p03AugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => A i j ≠ 0).card +
    if b i ≠ 0 then 1 else 0

/-- Maximum number `p` of nonzeros in a row of `[A b]`. -/
noncomputable def p03MaxAugmentedRowNnz {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : ℕ :=
  Finset.univ.sup (p03AugmentedRowNnz A b)

/-- A complete real-valued execution certificate for the unscaled Algorithm
1.1 model used in P03 Theorem 4.1. The equations and inequalities are the
exact error representations (3.3), (3.6), and solver condition (2.4).
Real-valued states encode the paper's finite standard-model regime, in which
underflow and overflow are excluded. -/
structure P03NormwiseIRRun (n : ℕ) where
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  b : Fin n → ℝ
  x : ℕ → Fin n → ℝ
  rHat : ℕ → Fin n → ℝ
  dHat : ℕ → Fin n → ℝ
  deltaR : ℕ → Fin n → ℝ
  deltaX : ℕ → Fin n → ℝ
  uR : ℝ
  u : ℝ
  uS : ℝ
  uF : ℝ
  c1 : ℕ → ℝ
  c2 : ℕ → ℝ
  uR_nonneg : 0 ≤ uR
  uR_le_u : uR ≤ u
  u_le_uS : u ≤ uS
  uS_le_uF : uS ≤ uF
  gamma_valid : GammaValid uR (p03MaxAugmentedRowNnz A b)
  c1_nonneg : ∀ i, 0 ≤ c1 i
  c2_nonneg : ∀ i, 0 ≤ c2 i
  inverse_action : ∀ (z : Fin n → ℝ) (j : Fin n),
    p03MatVec Ainv (p03MatVec A z) j = z j
  residual_equation : ∀ (i : ℕ) (j : Fin n),
    rHat i j = b j - p03MatVec A (x i) j + deltaR i j
  residual_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaR i j| ≤
      uS * |b j - p03MatVec A (x i) j| +
        (1 + uS) * gamma uR (p03MaxAugmentedRowNnz A b) *
          (|b j| + p03MatVec (p03MatAbs A) (p03VecAbs (x i)) j)
  correction_solver_bound : ∀ i : ℕ,
    p03VecInfNorm (fun j => rHat i j - p03MatVec A (dHat i) j) ≤
      uS *
        (c1 i * p03MatInfNorm A * p03VecInfNorm (dHat i) +
          c2 i * p03VecInfNorm (rHat i))
  update_equation : ∀ (i : ℕ) (j : Fin n),
    x (i + 1) j = x i j + dHat i j + deltaX i j
  update_error_bound : ∀ (i : ℕ) (j : Fin n),
    |deltaX i j| ≤ u * |x (i + 1) j|
  denominator_condition : ∀ i : ℕ,
    c1 i * (p03MatInfNorm Ainv * p03MatInfNorm A) * uS < 1

/-- Exact residual of the stored iterate for the original system. -/
noncomputable def p03ExactResidual {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.b j - p03MatVec run.A (run.x i) j

/-- Residual of the computed correction equation. -/
noncomputable def p03CorrectionDefect {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : Fin n → ℝ :=
  fun j => run.rHat i j - p03MatVec run.A (run.dHat i) j

/-- `κ_∞(A) = ‖A⁻¹‖_∞ ‖A‖_∞` for a certified P03 run. -/
noncomputable def p03KappaInf {n : ℕ} (run : P03NormwiseIRRun n) : ℝ :=
  p03MatInfNorm run.Ainv * p03MatInfNorm run.A

/-- The correction-solver quotient in P03 Theorem 4.1. -/
noncomputable def p03CorrectionRatio {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (run.c1 i * p03KappaInf run + run.c2 i) /
    (1 - run.c1 i * p03KappaInf run * run.uS)

/-- The coefficient `α_i` in P03 Theorem 4.1. -/
noncomputable def p03Alpha {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  run.uS * (1 + (1 + run.uS) * p03CorrectionRatio run i)

/-- The additive term `β_i` in P03 Theorem 4.1. -/
noncomputable def p03Beta {n : ℕ}
    (run : P03NormwiseIRRun n) (i : ℕ) : ℝ :=
  (1 + run.uS * p03CorrectionRatio run i) * (1 + run.uS) *
      gamma run.uR (p03MaxAugmentedRowNnz run.A run.b) *
        (p03VecInfNorm run.b +
          p03MatInfNorm run.A * p03VecInfNorm (run.x i)) +
    run.u * p03MatInfNorm run.A * p03VecInfNorm (run.x (i + 1))

/-- The inverse-action contract for the nonnegative M-matrix inverse `M₁`
used in the proof of P03 Theorem 5.1. -/
def P03ResolventInverse {n : ℕ}
    (M P : Fin n → Fin n → ℝ) : Prop :=
  (∀ i k : Fin n, 0 ≤ M i k) ∧
    ∀ (z : Fin n → ℝ) (i : Fin n),
      p03MatVec M (fun k => z k - p03MatVec P z k) i = z i

end HighamBench
```
