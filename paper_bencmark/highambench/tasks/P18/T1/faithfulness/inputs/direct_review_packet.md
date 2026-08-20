# Declaration dossier for P18-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p18_t1_scheme_perturbation_error_split {n s : ℕ}
    (run : P18AdditiveRKOneStepRun n s) :
    p18TotalOneStepError run =
        p18Add (p18SchemeOneStepError run)
          (p18PerturbationOneStepError run) ∧
      p18VecNorm2 (p18TotalOneStepError run) ≤
        p18VecNorm2 (p18SchemeOneStepError run) +
          p18VecNorm2 (p18PerturbationOneStepError run)
```

## Elaborated target type

```lean
∀ {n s : Nat} (run : HighamBench.P18AdditiveRKOneStepRun n s),
  And
    (Eq (HighamBench.p18TotalOneStepError run)
      (HighamBench.p18Add (HighamBench.p18SchemeOneStepError run) (HighamBench.p18PerturbationOneStepError run)))
    (Real.instLE.le (HighamBench.p18VecNorm2 (HighamBench.p18TotalOneStepError run))
      (instHAdd.hAdd (HighamBench.p18VecNorm2 (HighamBench.p18SchemeOneStepError run))
        (HighamBench.p18VecNorm2 (HighamBench.p18PerturbationOneStepError run))))
```

## Fully explicit elaborated target type

```lean
∀ {n s : Nat} (run : HighamBench.P18AdditiveRKOneStepRun n s),
  And
    (@Eq.{1} (Fin n → Real) (@HighamBench.p18TotalOneStepError n s run)
      (@HighamBench.p18Add n (@HighamBench.p18SchemeOneStepError n s run)
        (@HighamBench.p18PerturbationOneStepError n s run)))
    (@LE.le.{0} Real Real.instLE (@HighamBench.p18VecNorm2 n (@HighamBench.p18TotalOneStepError n s run))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HighamBench.p18VecNorm2 n (@HighamBench.p18SchemeOneStepError n s run))
        (@HighamBench.p18VecNorm2 n (@HighamBench.p18PerturbationOneStepError n s run))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P18Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P18Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P18AdditiveRKOneStepRun`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `0515fbc1560f4447acc583f4b0976dd898fd14f8c5b45ed024f71245b0d05918`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(n s : Nat) → Type
```

### D002: `HighamBench.p18Add`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a618ade07a852d5fd95ede3f352cb8e1b2123e6bc0d9cc7b34857ff4b7502a01`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHAdd.hAdd (x i) (y i)
```

### D003: `HighamBench.p18PerturbationOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fd9006cea861d46b2a542f2cc8590d7420d7882652f112bae8ff9433a64a7309`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (run : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n s} run => HighamBench.p18Sub run.schemeNext run.perturbedNext
```

### D004: `HighamBench.p18SchemeOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `488de497112a7d188e072710bb679657b3c367a8b3c4fd6c8658c593672a73c8`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (run : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n s} run => HighamBench.p18Sub run.exactNext run.schemeNext
```

### D005: `HighamBench.p18TotalOneStepError`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `79ef88b4f9e1c1c4e28428356eb24f9b404043b1fdadf6935ce27113622084cc`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (run : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n s} run => HighamBench.p18Sub run.exactNext run.perturbedNext
```

### D006: `HighamBench.p18VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dae8ad1d4d081e7ea81ff6faab63aa8a3774e35268e6edada4a650886b35e5e6`

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
fun {n} x => (HighamBench.p18VecNorm2Sq x).sqrt
```

### D007: `HighamBench.P18AdditiveRKOneStepRun.exactNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c63efdc3ef00fd54d44c0da31b4e76871495ad4968a3f4470a1323568129f734`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (self : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n s self => self.8
```

### D008: `HighamBench.P18AdditiveRKOneStepRun.mk`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `712fe878597443a8162651d50c456a438633c55f18111a084318bdfc12ffcebf`

Type:

```lean
{n s : Nat} →
  instLTNat.lt 0 n →
    instLTNat.lt 0 s →
      (step epsilon : Real) →
        Real.instLE.le 0 step →
          Real.instLE.le 0 epsilon →
            (initial : Fin n → Real) →
              (Fin n → Real) →
                (F tau : (Fin n → Real) → Fin n → Real) →
                  (aTilde aPerturbation : Fin s → Fin s → Real) →
                    (bTilde bPerturbation : Fin s → Real) →
                      (schemeStages perturbedStages : Fin s → Fin n → Real) →
                        (schemeNext perturbedNext : Fin n → Real) →
                          (∀ (i : Fin s),
                              Eq (schemeStages i)
                                (HighamBench.p18Add initial
                                  (HighamBench.p18Scale step
                                    (HighamBench.p18StageSum (aTilde i) fun j => F (schemeStages j))))) →
                            Eq schemeNext
                                (HighamBench.p18Add initial
                                  (HighamBench.p18Scale step
                                    (HighamBench.p18StageSum bTilde fun j => F (schemeStages j)))) →
                              (∀ (i : Fin s),
                                  Eq (perturbedStages i)
                                    (HighamBench.p18Add initial
                                      (HighamBench.p18Add
                                        (HighamBench.p18Scale step
                                          (HighamBench.p18StageSum (aTilde i) fun j => F (perturbedStages j)))
                                        (HighamBench.p18Scale (instHMul.hMul epsilon step)
                                          (HighamBench.p18StageSum (aPerturbation i) fun j =>
                                            tau (perturbedStages j)))))) →
                                Eq perturbedNext
                                    (HighamBench.p18Add initial
                                      (HighamBench.p18Add
                                        (HighamBench.p18Scale step
                                          (HighamBench.p18StageSum bTilde fun j => F (perturbedStages j)))
                                        (HighamBench.p18Scale (instHMul.hMul epsilon step)
                                          (HighamBench.p18StageSum bPerturbation fun j => tau (perturbedStages j))))) →
                                  HighamBench.P18AdditiveRKOneStepRun n s
```

Fully explicit type:

```lean
{n s : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (stage_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s) →
      (step epsilon : Real) →
        (step_nonneg :
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              step) →
          (epsilon_nonneg :
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                epsilon) →
            (initial exactNext : Fin n → Real) →
              (F tau : (Fin n → Real) → Fin n → Real) →
                (aTilde aPerturbation : Fin s → Fin s → Real) →
                  (bTilde bPerturbation : Fin s → Real) →
                    (schemeStages perturbedStages : Fin s → Fin n → Real) →
                      (schemeNext perturbedNext : Fin n → Real) →
                        (scheme_stage_equation :
                            ∀ (i : Fin s),
                              @Eq.{1} (Fin n → Real) (schemeStages i)
                                (@HighamBench.p18Add n initial
                                  (@HighamBench.p18Scale n step
                                    (@HighamBench.p18StageSum n s (aTilde i) fun (j : Fin s) => F (schemeStages j))))) →
                          (scheme_output_equation :
                              @Eq.{1} (Fin n → Real) schemeNext
                                (@HighamBench.p18Add n initial
                                  (@HighamBench.p18Scale n step
                                    (@HighamBench.p18StageSum n s bTilde fun (j : Fin s) => F (schemeStages j))))) →
                            (perturbed_stage_equation :
                                ∀ (i : Fin s),
                                  @Eq.{1} (Fin n → Real) (perturbedStages i)
                                    (@HighamBench.p18Add n initial
                                      (@HighamBench.p18Add n
                                        (@HighamBench.p18Scale n step
                                          (@HighamBench.p18StageSum n s (aTilde i) fun (j : Fin s) =>
                                            F (perturbedStages j)))
                                        (@HighamBench.p18Scale n
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                                            step)
                                          (@HighamBench.p18StageSum n s (aPerturbation i) fun (j : Fin s) =>
                                            tau (perturbedStages j)))))) →
                              (perturbed_output_equation :
                                  @Eq.{1} (Fin n → Real) perturbedNext
                                    (@HighamBench.p18Add n initial
                                      (@HighamBench.p18Add n
                                        (@HighamBench.p18Scale n step
                                          (@HighamBench.p18StageSum n s bTilde fun (j : Fin s) =>
                                            F (perturbedStages j)))
                                        (@HighamBench.p18Scale n
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                                            step)
                                          (@HighamBench.p18StageSum n s bPerturbation fun (j : Fin s) =>
                                            tau (perturbedStages j)))))) →
                                HighamBench.P18AdditiveRKOneStepRun n s
```

### D009: `HighamBench.P18AdditiveRKOneStepRun.perturbedNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `81ef2f8be6ae146b1d9e9ee7fa248b19479f1c3c6bb22dc1af44a23594417850`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (self : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n s self => self.18
```

### D010: `HighamBench.P18AdditiveRKOneStepRun.schemeNext`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `111155a11bb1f05a1bf986422f567d588cf81975c0e0056605613f5eff0a99c8`

Type:

```lean
{n s : Nat} → HighamBench.P18AdditiveRKOneStepRun n s → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (self : HighamBench.P18AdditiveRKOneStepRun n s) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n s self => self.17
```

### D011: `HighamBench.p18Sub`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a048fe7cdbf9628fedf3fd15a7bf6e3c9670027bc0339a47e35e483fe49457f3`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHSub.hSub (x i) (y i)
```

### D012: `HighamBench.p18VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0e1e195ed4b6629871f131ca22275653ea718d87fb997f5d9f095659fd926caf`

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

### D013: `HighamBench.p18Scale`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `cccc50115c3e45e5f770a2125292286d90f1b477a7ebe70844057090a4f76056`

Type:

```lean
{n : Nat} → Real → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a x i => instHMul.hMul a (x i)
```

### D014: `HighamBench.p18StageSum`

- Role: `local`
- Owner module: `HighamBench.P18Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6593a99f2829c3f0f2e9484bfd258a50dfaa785b7c9d1b50c8e85777ecf70014`

Type:

```lean
{n s : Nat} → (Fin s → Real) → (Fin s → Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n s : Nat} → (weights : Fin s → Real) → (values : Fin s → Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n s} weights values k => Finset.univ.sum fun j => instHMul.hMul (weights j) (values j k)
```

### D015: `And`

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

### D016: `Eq`

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

### D017: `Fin`

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

### D018: `HAdd.hAdd`

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

### D019: `LE.le`

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

### D020: `Nat`

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

### D021: `Real`

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

### D022: `Real.instAdd`

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

### D023: `Real.instLE`

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

### D024: `instHAdd`

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

### D025: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D026: `Fin.fintype`

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

### D027: `Finset.sum`

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

### D028: `Finset.univ`

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

### D029: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D030: `HPow.hPow`

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

### D031: `HSub.hSub`

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

### D032: `LT.lt`

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

### D033: `Monoid.toNatPow`

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

### D034: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D035: `Real.instAddCommMonoid`

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

### D036: `Real.instMonoid`

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

### D037: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D038: `Real.instSub`

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

### D039: `Real.instZero`

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

### D040: `Zero.toOfNat0`

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

### D041: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D042: `instHPow`

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

### D043: `instHSub`

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

### D044: `instLTNat`

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

### D045: `instOfNatNat`

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
