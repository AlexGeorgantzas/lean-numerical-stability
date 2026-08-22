# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {b p r : Nat} (run : LocalDef001 b p r),
  have c := LocalDef019 b p r;
  have gammaP := LocalDef024 p.cast run.unitRoundoff;
  have gamma3C := LocalDef024 (instHMul.hMul 3 c) run.unitRoundoff;
  have xi := LocalDef020 p run.threshold run.recompression;
  have solveScale :=
    instHMul.hMul (instHMul.hMul (LocalDef023 run.L) (LocalDef023 run.U))
      (LocalDef028 run.xHat);
  Exists fun matrixError =>
    Exists fun rhsError =>
      Exists fun rhsRemainder =>
        And
          (Eq matrixError
            (LocalDef021 run.factorError run.lowerError run.upperError run.L run.U))
          (And (Eq rhsError (LocalDef022 run.lowerRhsError run.upperRhsError run.L run.lowerError))
            (And (LocalDef025 run.factorRemainder)
              (And (LocalDef026 rhsRemainder fun x x_1 => solveScale)
                (And
                  (Eq (LocalDef027 (instHAdd.hAdd run.A matrixError) run.xHat) (instHAdd.hAdd run.v rhsError))
                  (And
                    (Real.instLE.le (LocalDef023 matrixError)
                      (instHAdd.hAdd
                        (instHAdd.hAdd
                          (instHMul.hMul (instHAdd.hAdd (instHMul.hMul xi run.epsilon) gammaP)
                            (LocalDef023 run.A))
                          (instHMul.hMul (instHMul.hMul gamma3C (LocalDef023 run.L))
                            (LocalDef023 run.U)))
                        (run.factorRemainder run.unitRoundoff run.epsilon)))
                    (Real.instLE.le (LocalDef028 rhsError)
                      (instHAdd.hAdd (instHMul.hMul gammaP (instHAdd.hAdd (LocalDef028 run.v) solveScale))
                        (rhsRemainder run.unitRoundoff run.epsilon))))))))
```

## Fully explicit elaborated target type

```lean
∀ {b p r : Nat} (run : LocalDef001 b p r),
  have c : Real := LocalDef019 b p r;
  have gammaP : Real :=
    LocalDef024 (@Nat.cast.{0} Real Real.instNatCast p)
      (@LocalDef012 b p r run);
  have gamma3C : Real :=
    LocalDef024
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        c)
      (@LocalDef012 b p r run);
  have xi : Real :=
    LocalDef020 p (@LocalDef011 b p r run)
      (@LocalDef010 b p r run);
  have solveScale : Real :=
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@LocalDef023 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@LocalDef003 b p r run))
        (@LocalDef023 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
          (@LocalDef004 b p r run)))
      (@LocalDef028 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
        (@LocalDef016 b p r run));
  @Exists.{1} (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
    fun (matrixError : LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
    @Exists.{1} (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
      fun (rhsError : LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
      @Exists.{1} (Real → Real → Real) fun (rhsRemainder : Real → Real → Real) =>
        And
          (@Eq.{1} (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
            matrixError
            (@LocalDef021 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
              (@LocalDef006 b p r run)
              (@LocalDef008 b p r run)
              (@LocalDef013 b p r run)
              (@LocalDef003 b p r run)
              (@LocalDef004 b p r run)))
          (And
            (@Eq.{1} (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
              rhsError
              (@LocalDef022 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                (@LocalDef009 b p r run)
                (@LocalDef014 b p r run)
                (@LocalDef003 b p r run)
                (@LocalDef008 b p r run)))
            (And (LocalDef025 (@LocalDef007 b p r run))
              (And (LocalDef026 rhsRemainder fun (x x_1 : Real) => solveScale)
                (And
                  (@Eq.{1} (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                    (@LocalDef027 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                      (@HAdd.hAdd.{0, 0, 0}
                        (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@instHAdd.{0}
                          (LocalDef017 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (@Matrix.add.{0, 0, 0}
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                            (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) Real
                            Real.instAdd))
                        (@LocalDef002 b p r run) matrixError)
                      (@LocalDef016 b p r run))
                    (@HAdd.hAdd.{0, 0, 0}
                      (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                      (@instHAdd.{0}
                        (LocalDef018 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                        (@Pi.instAdd.{0, 0} (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b))
                          (fun (a : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) => Real)
                          fun (i : Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)) =>
                          Real.instAdd))
                      (@LocalDef015 b p r run) rhsError))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@LocalDef023 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        matrixError)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) xi
                                (@LocalDef005 b p r run))
                              gammaP)
                            (@LocalDef023
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                              (@LocalDef002 b p r run)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma3C
                              (@LocalDef023
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                                (@LocalDef003 b p r run)))
                            (@LocalDef023
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                              (@LocalDef004 b p r run))))
                        (@LocalDef007 b p r run
                          (@LocalDef012 b p r run)
                          (@LocalDef005 b p r run))))
                    (@LE.le.{0} Real Real.instLE
                      (@LocalDef028 (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                        rhsError)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaP
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@LocalDef028
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b)
                              (@LocalDef015 b p r run))
                            solveScale))
                        (rhsRemainder (@LocalDef012 b p r run)
                          (@LocalDef005 b p r run)))))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `48c46a478eff0fa22f0898ad08185950e64ed035455b313237ed0de36e6ce742`

Type:

```lean
Nat → Nat → Nat → Type
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4faf24f64a56296b99377806a186ba87857ca1c06ce54cd4110fde3419f5cf11`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.7
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `dd1bb5831e63b5325a0a0fd68a380122fd9bc54824c1a10da5dda9f098ce01ae`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.9
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bfb02ddb14a49b2eecf6522f2756e6d7c9fb989dbb530746e1d922cf0a5bf210`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.10
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f4eee8e255cd7780044fcfedef79478296d5d53cec840c6ebcf4ccf63d499b23`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.15
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5bb5a6057f3dcae8dd442e815d3dc648ab94e9adf79bc71c8fa8783ebac3f5f3`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.21
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `779bcc0d9f22ca5e00ef28c2bc07d007577de2cd286668e5195b06b5fcb79aef`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.22
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bc53000dbd1a561389841865a2aafc0ec24e05b4f7d124c9a1cace53c8377bf9`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.26
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `807a747072413476d6b063a853946b25d71b5f1e0f743bb7b63df18b7359736c`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef018 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.28
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e7f1b55868e45e12b0d6c040ff1ec13a5cfbf49d154d6a3977c3263be2ba9be7`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef030
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.6
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b2081b192b5bec9d5c1c2d74651461f29c272f0a650849e68edfb770160ff00f`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef031
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.5
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `bc26714304c3ad22cc758e91dddfa3e38c62a45a7633594f4e9248dad85dd665`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.14
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a1be125505c8a2a063d8f19d0adf6561276dbc5669e70aaebf46ba202fecf8da`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef017 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.27
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2ef4b51d0dfd3a4c59184e724dea824a9f3bb01761bd321e9908640f29bb77a0`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef018 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.29
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `00f246fb21beb0a4eda222b738f2836a34ea1b7bb1b45e9f25b02b46a676ffc1`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef018 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.11
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9c50fb0ae5c74f9edf68d152b71b37707e8f398a9bffb607240e598a54ceda18`

Type:

```lean
{b p r : Nat} → LocalDef001 b p r → LocalDef018 (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun b p r self => self.13
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `15e7e37c5731d7df61fbacb22e39e6f80678f5f9880fecbb579e57644d05505c`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e7760f878caa60b3dc61c72221f5221bd67e85cb18d96a0f3d138f5c6026151e`

Type:

```lean
Nat → Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r => instHAdd.hAdd (instHAdd.hAdd b.cast (instHMul.hMul (instHMul.hMul 2 r.cast) r.cast.sqrt)) p.cast
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `65929a6bf33f8b7c99b156c0f9eb0b7289d5220cbf07cd19e2c7a5f7aa28c95d`

Type:

```lean
Nat → LocalDef031 → LocalDef030 → Real
```

Definition body (one-level semantic boundary):

```lean
fun p threshold recompression =>
  LocalDef034 (fun recompression threshold => Real) recompression threshold (fun _ => 1)
    (fun _ => p.cast) (fun _ => p.cast) fun _ => instHDiv.hDiv (instHPow.hPow p.cast 2) (Real.sqrt 6)
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7fea7f458b67ea6c52b1dbb4c20be145a0a762071dd49829d699a2b06da7bfd2`

Type:

```lean
{n : Nat} →
  LocalDef017 n →
    LocalDef017 n →
      LocalDef017 n → LocalDef017 n → LocalDef017 n → LocalDef017 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} factorError lowerError upperError L U =>
  instHAdd.hAdd
    (instHAdd.hAdd (instHAdd.hAdd factorError (LocalDef035 lowerError U))
      (LocalDef035 L upperError))
    (LocalDef035 lowerError upperError)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `af0b640c8d0046428cf87fce5a7328baeb6b0ab688f048dbfbae91dcef566e77`

Type:

```lean
{n : Nat} →
  LocalDef018 n →
    LocalDef018 n → LocalDef017 n → LocalDef017 n → LocalDef018 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} rhsLower rhsUpper L lowerError =>
  instHAdd.hAdd (instHAdd.hAdd rhsLower (LocalDef027 L rhsUpper)) (LocalDef027 lowerError rhsUpper)
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837bd1b4fd433e90b49e653f1245c95156c8bd043250d89a7117737646408c28`

Type:

```lean
{n : Nat} → LocalDef017 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => LocalDef036 A
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `271296c936d7dd54bb763543aed321ddd01215dbcf43ad0f046996eedec71821`

Type:

```lean
Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun k u => instHDiv.hDiv (instHMul.hMul k u) (instHSub.hSub 1 (instHMul.hMul k u))
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `94d1db16fdbc23e161b75cfb8bf2cd9e73cf3680a0bc8abf9e03e9af4a05db77`

Type:

```lean
(Real → Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder =>
  Exists fun C =>
    Exists fun delta =>
      And (Real.instLE.le 0 C)
        (And (Real.instLT.lt 0 delta)
          (∀ (u epsilon : Real),
            Real.instLT.lt 0 u →
              Real.instLT.lt 0 epsilon →
                Real.instLT.lt u epsilon →
                  Real.instLE.le u delta →
                    Real.instLE.le epsilon delta →
                      Real.instLE.le (abs (remainder u epsilon)) (instHMul.hMul C (instHMul.hMul u epsilon))))
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4acca8fab08b6cee29aa63aadee09af3b0d679224a9c92cffe5b8d3bd5add815`

Type:

```lean
(Real → Real → Real) → (Real → Real → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun remainder scale =>
  Exists fun C =>
    Exists fun delta =>
      And (Real.instLE.le 0 C)
        (And (Real.instLT.lt 0 delta)
          (∀ (u epsilon : Real),
            Real.instLT.lt 0 u →
              Real.instLT.lt 0 epsilon →
                Real.instLT.lt u epsilon →
                  Real.instLE.le u delta →
                    Real.instLE.le epsilon delta →
                      Real.instLE.le 0 (scale u epsilon) →
                        Real.instLE.le (abs (remainder u epsilon))
                          (instHMul.hMul (instHMul.hMul C (instHPow.hPow u 2)) (scale u epsilon))))
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `46653426fb5f80e06b04a77772652321fa618edf797127f16a95ad856ba2a7a8`

Type:

```lean
{n : Nat} → LocalDef017 n → LocalDef018 n → LocalDef018 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a716c1fae04d4026c6643ec3b153abae96d0f93b8c6f72ce66bce27b4a46d6f9`

Type:

```lean
{n : Nat} → LocalDef018 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `cd9ee91f66f822e80555e7dcca6cc3a7764c6ebee10e0d3a7903a5928227aa73`

Type:

```lean
{b p r : Nat} →
  instLTNat.lt 0 b →
    instLTNat.lt 0 p →
      instLENat.le r b →
        (algorithm : LocalDef037) →
          (threshold : LocalDef031) →
            (recompression : LocalDef030) →
              (A Atilde L U : LocalDef017 (instHMul.hMul p b)) →
                (v yHat xHat : LocalDef018 (instHMul.hMul p b)) →
                  (unitRoundoff epsilon : Real) →
                    LocalDef049 (LocalDef019 b p r) unitRoundoff epsilon →
                      LocalDef053 A →
                        LocalDef050 threshold epsilon A Atilde →
                          LocalDef052 r L U →
                            LocalDef044 r algorithm threshold recompression unitRoundoff
                                epsilon Atilde L U →
                              (factorError : LocalDef017 (instHMul.hMul p b)) →
                                (factorRemainder : Real → Real → Real) →
                                  Eq (instHAdd.hAdd A factorError) (LocalDef035 L U) →
                                    Real.instLE.le (LocalDef023 factorError)
                                        (instHAdd.hAdd
                                          (instHAdd.hAdd
                                            (instHMul.hMul
                                              (instHAdd.hAdd
                                                (instHMul.hMul (LocalDef020 p threshold recompression) epsilon)
                                                (LocalDef024 p.cast unitRoundoff))
                                              (LocalDef023 A))
                                            (instHMul.hMul
                                              (instHMul.hMul
                                                (LocalDef024 (LocalDef019 b p r)
                                                  unitRoundoff)
                                                (LocalDef023 L))
                                              (LocalDef023 U)))
                                          (factorRemainder unitRoundoff epsilon)) →
                                      LocalDef025 factorRemainder →
                                        (lowerError upperError : LocalDef017 (instHMul.hMul p b)) →
                                          (lowerRhsError upperRhsError : LocalDef018 (instHMul.hMul p b)) →
                                            Nonempty
                                                (LocalDef045 r
                                                  LocalDef047 unitRoundoff L v yHat) →
                                              Nonempty
                                                  (LocalDef045 r
                                                    LocalDef048 unitRoundoff U yHat
                                                    xHat) →
                                                Eq (LocalDef027 (instHAdd.hAdd L lowerError) yHat)
                                                    (instHAdd.hAdd v lowerRhsError) →
                                                  Eq (LocalDef027 (instHAdd.hAdd U upperError) xHat)
                                                      (instHAdd.hAdd yHat upperRhsError) →
                                                    Real.instLE.le (LocalDef023 lowerError)
                                                        (instHMul.hMul
                                                          (LocalDef024
                                                            (LocalDef051 b p r) unitRoundoff)
                                                          (LocalDef023 L)) →
                                                      Real.instLE.le (LocalDef023 upperError)
                                                          (instHMul.hMul
                                                            (LocalDef024
                                                              (LocalDef051 b p r)
                                                              unitRoundoff)
                                                            (LocalDef023 U)) →
                                                        Real.instLE.le (LocalDef028 lowerRhsError)
                                                            (instHMul.hMul
                                                              (LocalDef024 p.cast unitRoundoff)
                                                              (LocalDef028 v)) →
                                                          Real.instLE.le (LocalDef028 upperRhsError)
                                                              (instHMul.hMul
                                                                (LocalDef024 p.cast unitRoundoff)
                                                                (LocalDef028 yHat)) →
                                                            LocalDef001 b p r
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `184eef312a57ab5d86ec09b3a62edb2f4fe92527de10cff181cdfc695e456116`

Type:

```lean
Type
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e2bc11e18c7915802478e0c20e7eb676fc28067e8803e4c25ccd75efeb157e13`

Type:

```lean
Type
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `9d0e87eee49660c5b3c5b7631778db5647e4d28e6668a010375f571402b39ec4`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `bec3b366c0a588b14aa37dd233d61af7e47a2ba0a0eb0217d7909a24061d7a5c`

Type:

```lean
(instHAdd.hAdd 5 1).AtLeastTwo
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a1d7660b5a3e94f47fb136e11de89d815a1f6f99ba2238e3edc3a8d64723e165`

Type:

```lean
(motive : LocalDef030 → LocalDef031 → Sort u_1) →
  (recompression : LocalDef030) →
    (threshold : LocalDef031) →
      (Unit → motive LocalDef040 LocalDef043) →
        (Unit → motive LocalDef040 LocalDef042) →
          (Unit → motive LocalDef039 LocalDef043) →
            (Unit → motive LocalDef039 LocalDef042) →
              motive recompression threshold
```

Definition body (one-level semantic boundary):

```lean
fun motive recompression threshold h_1 h_2 h_3 h_4 =>
  LocalDef038 recompression
    (LocalDef041 threshold (h_1 Unit.unit) (h_2 Unit.unit))
    (LocalDef041 threshold (h_3 Unit.unit) (h_4 Unit.unit))
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `82a32c03123a1b58cce8a2734d2ddfed6b499db78b5c4e68d56caf8636e3bb0e`

Type:

```lean
{n : Nat} → LocalDef017 n → LocalDef017 n → LocalDef017 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f8df59150997c9c35d296b01efb6efe480f420d12b4d3873085fbf5fff732e33`

Type:

```lean
{m n : Nat} → LocalDef046 m n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `55236782b6eb2958981cd7ade1aafafec01e8f1dcb72f732214d156bee39ecec`

Type:

```lean
Type
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b81703bd43cb9741e32fc7ad503c8f369ffe55be40e8e7d6bc2374cf7a742b72`

Type:

```lean
{motive : LocalDef030 → Sort u} →
  (t : LocalDef030) →
    motive LocalDef040 → motive LocalDef039 → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t without «with» => LocalDef056 without «with» t
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `22d601e2e4bd74edece2b74479af68b0a4ddefed62faa92727c3d2b097562dab`

Type:

```lean
LocalDef030
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e33ab8fec1f818f03ada0115fe3b390d0d6c11ef7ccaf47e4f7bac6edc637082`

Type:

```lean
LocalDef030
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8eb410f5081e0717f83f45dda75ce2ed416bdd3f9c33ce8d8bd2d08aef99f7d8`

Type:

```lean
{motive : LocalDef031 → Sort u} →
  (t : LocalDef031) →
    motive LocalDef043 → motive LocalDef042 → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t «local» global => LocalDef057 «local» global t
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `5ae988e456ef025679682e499a244a52188744a737558e58b1d9d60f70b688b5`

Type:

```lean
LocalDef031
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b02c95e620ddc4f9263cabc12ce7e8d4dfbbb8dfced4a022d73b7aebfb67ad25`

Type:

```lean
LocalDef031
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `79ca4edb3a2cddd1dc183ac8302cb42b4f1566cadd37f80fdd2236f76b78fa78`

Type:

```lean
{b p : Nat} →
  Nat →
    LocalDef037 →
      LocalDef031 →
        LocalDef030 →
          Real →
            Real →
              LocalDef017 (instHMul.hMul p b) →
                LocalDef017 (instHMul.hMul p b) → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b p} r algorithm threshold recompression u epsilon A L U =>
  LocalDef062 (fun algorithm => Prop) algorithm
    (fun _ => Nonempty (LocalDef060 r threshold recompression u epsilon A L U)) fun _ =>
    Nonempty (LocalDef059 r threshold recompression u epsilon A L U)
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `c38a1d2cebf2f0beab40745ae55677fa2621e5c50a870375d8d7a55e0a316718`

Type:

```lean
{p b : Nat} →
  Nat →
    LocalDef061 →
      Real →
        LocalDef017 (instHMul.hMul p b) →
          LocalDef018 (instHMul.hMul p b) → LocalDef018 (instHMul.hMul p b) → Type
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8feb40d08c5292d10bb340b09678c4d176088c4c97bb1880d9f95a2c76fde9a2`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m n => Matrix (Fin m) (Fin n) Real
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `ed7c8315fcb03c4458bf042d8e255dbdd43a81b2256e12ed8cedcaa4b4901e2b`

Type:

```lean
LocalDef061
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e6d13e0fa0da3a432d462199fc5932439303d796406010f67483ae2716235cb0`

Type:

```lean
LocalDef061
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `163653545cc46da55ac53d48b395986d09e643293aa7fb4c106e6c742adbc4e3`

Type:

```lean
Real → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun c u epsilon =>
  And (Real.instLT.lt 0 u)
    (And (Real.instLT.lt 0 epsilon)
      (And (Real.instLT.lt u epsilon) (Real.instLT.lt (instHMul.hMul (instHMul.hMul 3 c) u) 1)))
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0bf4757bbc049d923d6621a1e589b4df23c1ba532f0802bb047cb4a19e019c19`

Type:

```lean
{p b : Nat} →
  LocalDef031 →
    Real → LocalDef017 (instHMul.hMul p b) → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold epsilon A Atilde =>
  And (∀ (i : Fin p), Eq (LocalDef067 Atilde i i) (LocalDef067 A i i))
    (∀ (i j : Fin p),
      Ne i j →
        Exists fun k =>
          And (LocalDef064 threshold epsilon A i j k (LocalDef067 Atilde i j))
            (∀ (ell : Nat) (candidate : LocalDef017 b),
              LocalDef064 threshold epsilon A i j ell candidate → instLENat.le k ell))
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `43766147f49acd15be088fd137e9b18b67b31e32af7ca125bd5b4ee721e2bbe6`

Type:

```lean
Nat → Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun b p r => instHAdd.hAdd (instHAdd.hAdd b.cast (instHMul.hMul r.cast r.cast.sqrt)) p.cast
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `caba8603744ec7aec3bfe43bb632fc5757c0af57502cc4f36e059c39b9313ef4`

Type:

```lean
{p b : Nat} → Nat → LocalDef017 (instHMul.hMul p b) → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r L U =>
  And (LocalDef066 r L)
    (And (LocalDef066 r U)
      (∀ (s : Nat), LocalDef066 s L → LocalDef066 s U → instLENat.le r s))
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `725bc01ee86ff95bcecf211671daa8a6a5dec9a47a1a481248902e115feeece2`

Type:

```lean
{n : Nat} → LocalDef017 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A =>
  Exists fun Ainv =>
    And (Eq (LocalDef035 Ainv A) (LocalDef065 n))
      (Eq (LocalDef035 A Ainv) (LocalDef065 n))
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `93a612d37f6c47859778cd40fd5fde9d5f37cd69a2f8fcff4bdda0f474f19c51`

Type:

```lean
LocalDef037
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `39d148233d14cc9057e6abeed9c5dfc41bf64932051a49ece31079eb79d2c097`

Type:

```lean
LocalDef037
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `b3bd839df8a5575f92a8d277048ec72db51ad4d9c566c3a66067e793be53a850`

Type:

```lean
{motive : LocalDef030 → Sort u} →
  motive LocalDef040 →
    motive LocalDef039 → (t : LocalDef030) → motive t
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `09d8cf322bde803da325f034925cbbbdb74b5bd9f34fa7d51d83a97f077fdac6`

Type:

```lean
{motive : LocalDef031 → Sort u} →
  motive LocalDef043 →
    motive LocalDef042 → (t : LocalDef031) → motive t
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `bff97541f040ad35a64f6ce14aa85d177fcabaa558f9758b37e4ab1292604a70`

Type:

```lean
{p b r : Nat} →
  {direction : LocalDef061} →
    {u : Real} →
      {T : LocalDef017 (instHMul.hMul p b)} →
        {rhs x : LocalDef018 (instHMul.hMul p b)} →
          (LocalDef072 (fun direction => Prop) direction
              (fun _ => LocalDef074 T) fun _ => LocalDef075 T) →
            (∀ (i : Fin p), LocalDef053 (LocalDef067 T i i)) →
              (productValue : Fin p → Fin p → LocalDef018 b) →
                (productError : Fin p → Fin p → LocalDef017 b) →
                  (rhsRelativeError : Fin p → LocalDef018 b) →
                    (productRelativeError : Fin p → Fin p → LocalDef018 b) →
                      (diagonalError : Fin p → LocalDef017 b) →
                        (∀ (i j : Fin p),
                            LocalDef081 direction i j →
                              Eq (productValue i j)
                                (LocalDef027
                                  (instHAdd.hAdd (LocalDef067 T i j) (productError i j))
                                  (LocalDef084 x j))) →
                          (∀ (i j : Fin p),
                              LocalDef081 direction i j →
                                Real.instLE.le (LocalDef023 (productError i j))
                                  (instHMul.hMul (LocalDef024 (LocalDef076 b r) u)
                                    (LocalDef023 (LocalDef067 T i j)))) →
                            (∀ (i : Fin p) (row : Fin b),
                                Real.instLE.le (abs (rhsRelativeError i row)) (LocalDef024 p.cast u)) →
                              (∀ (i j : Fin p) (row : Fin b),
                                  LocalDef081 direction i j →
                                    Real.instLE.le (abs (productRelativeError i j row))
                                      (LocalDef024 p.cast u)) →
                                (∀ (i : Fin p),
                                    Real.instLE.le (LocalDef023 (diagonalError i))
                                      (instHMul.hMul (LocalDef024 b.cast u)
                                        (LocalDef023 (LocalDef067 T i i)))) →
                                  (∀ (i : Fin p),
                                      Eq
                                        (LocalDef027
                                          (instHAdd.hAdd (LocalDef067 T i i) (diagonalError i))
                                          (LocalDef084 x i))
                                        (instHSub.hSub
                                          (LocalDef083 (LocalDef084 rhs i)
                                            (instHAdd.hAdd (LocalDef078 b) (rhsRelativeError i)))
                                          ((LocalDef082 direction i).sum fun j =>
                                            LocalDef083 (productValue i j)
                                              (instHAdd.hAdd (LocalDef078 b)
                                                (productRelativeError i j))))) →
                                    LocalDef045 r direction u T rhs x
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `5b7298c0394e3cd6f32f441cc34400e000f95ed1f77f2fc5f891d06dd839dbfa`

Type:

```lean
{p b : Nat} →
  Nat →
    LocalDef031 →
      LocalDef030 →
        Real →
          Real →
            LocalDef017 (instHMul.hMul p b) →
              LocalDef017 (instHMul.hMul p b) → LocalDef017 (instHMul.hMul p b) → Type
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `5aac7c45973a6b3b3d7d96251486d4c0f15d78aaea9cad06ee8ff209a59a03bd`

Type:

```lean
{p b : Nat} →
  Nat →
    LocalDef031 →
      LocalDef030 →
        Real →
          Real →
            LocalDef017 (instHMul.hMul p b) →
              LocalDef017 (instHMul.hMul p b) → LocalDef017 (instHMul.hMul p b) → Type
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `2739599cb5c208da8ba46dbb051853914b460ecd048eb3ce127ee1b183a6a5f3`

Type:

```lean
Type
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `f170b62e1780181c35a46a156b1718c31e11fc5ad1de610936d81dc52775a2ff`

Type:

```lean
(motive : LocalDef037 → Sort u_1) →
  (x : LocalDef037) →
    (Unit → motive LocalDef055) →
      (Unit → motive LocalDef054) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => LocalDef068 x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `213bd1e73174b7595c41e7b42aa9993d17dae1408a69ea3f0097deeae64f2916`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2ae3164d58c89c16825b3800d5cbffb555544425da7350adab053e7f6a8e4e19`

Type:

```lean
{p b : Nat} →
  LocalDef031 →
    Real → LocalDef017 (instHMul.hMul p b) → Fin p → Fin p → Nat → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold epsilon A i j k candidate =>
  Exists fun X =>
    Exists fun Y =>
      And (LocalDef080 X)
        (And (Eq candidate (LocalDef079 i j X Y))
          (Real.instLE.le (LocalDef023 (instHSub.hSub candidate (LocalDef067 A i j)))
            (instHMul.hMul epsilon
              (LocalDef071 (fun threshold => Real) threshold
                (fun _ => LocalDef023 (LocalDef067 A i j)) fun _ =>
                LocalDef023 A))))
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b666a790818338446ad29c7622b631b68fff0b34eabf08253467b02fd032fa63`

Type:

```lean
(n : Nat) → LocalDef017 n
```

Definition body (one-level semantic boundary):

```lean
fun n i j => ite (Eq i j) 1 0
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `23b2fd5405f6ba223eaef2d1cd61e62edd91a663b0bd801522dff0a705cea7db`

Type:

```lean
{p b : Nat} → Nat → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r A =>
  Exists fun X =>
    Exists fun Y =>
      ∀ (i j : Fin p), Ne i j → Eq (LocalDef067 A i j) (LocalDef077 (X i j) (Y i j))
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b6f6652f790cad96f7c671f939858824c8903bdc549b35ca6417e1dee14a7aaa`

Type:

```lean
{p b : Nat} → LocalDef017 (instHMul.hMul p b) → Fin p → Fin p → LocalDef017 b
```

Definition body (one-level semantic boundary):

```lean
fun {p b} A i j row col => A (LocalDef073 i row) (LocalDef073 j col)
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `30b5d6ce1343e00bc8154d85f4f1a4dcdd43c9c3d0e5e49eb85ea6cdf99eed21`

Type:

```lean
{motive : LocalDef037 → Sort u} →
  (t : LocalDef037) →
    motive LocalDef055 → motive LocalDef054 → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t ufc ucf => LocalDef085 ufc ucf t
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `6b5dfdcd453d3974f9d52bc7f02fe7870a0ebceb2af139612205c84e897482a7`

Type:

```lean
{p b r : Nat} →
  {threshold : LocalDef031} →
    {recompression : LocalDef030} →
      {u epsilon : Real} →
        {A L U : LocalDef017 (instHMul.hMul p b)} →
          (recompressionError : Fin p → Fin p → Fin p → LocalDef017 b) →
            LocalDef094 recompression threshold epsilon A recompressionError →
              (updatedColumn updatedRow compressedColumn compressedRow : Fin p → Fin p → LocalDef017 b) →
                LocalDef074 L →
                  LocalDef075 U →
                    (∀ (k i : Fin p),
                        instLEFin.le k i →
                          LocalDef090 r u A L U recompressionError k i k (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            LocalDef090 r u A L U recompressionError k k i (updatedRow k i)) →
                        (∀ (k : Fin p), Eq (updatedColumn k k) (updatedRow k k)) →
                          ((k i : Fin p) →
                              instLTFin.lt k i →
                                LocalDef086 epsilon
                                  (LocalDef088 threshold A i k) (updatedColumn k i)
                                  (compressedColumn k i)) →
                            ((k i : Fin p) →
                                instLTFin.lt k i →
                                  LocalDef086 epsilon
                                    (LocalDef088 threshold A k i) (updatedRow k i)
                                    (compressedRow k i)) →
                              (∀ (k : Fin p),
                                  LocalDef091 u (updatedColumn k k)
                                    (LocalDef067 L k k) (LocalDef067 U k k)) →
                                (∀ (k i : Fin p),
                                    instLTFin.lt k i →
                                      LocalDef093 u (compressedColumn k i)
                                        (LocalDef067 L i k) (LocalDef067 U k k)) →
                                  (∀ (k i : Fin p),
                                      instLTFin.lt k i →
                                        LocalDef092 u (compressedRow k i)
                                          (LocalDef067 L k k) (LocalDef067 U k i)) →
                                    LocalDef059 r threshold recompression u epsilon A L U
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `b17af843d0388ba5782f551a1bd7dde642747b94755d8f88b3a5861368e2604d`

Type:

```lean
{p b r : Nat} →
  {threshold : LocalDef031} →
    {recompression : LocalDef030} →
      {u epsilon : Real} →
        {A L U : LocalDef017 (instHMul.hMul p b)} →
          (recompressionError : Fin p → Fin p → Fin p → LocalDef017 b) →
            LocalDef094 recompression threshold epsilon A recompressionError →
              (updatedColumn updatedRow rawLower rawUpper : Fin p → Fin p → LocalDef017 b) →
                LocalDef074 L →
                  LocalDef075 U →
                    (∀ (k i : Fin p),
                        instLEFin.le k i →
                          LocalDef090 r u A L U recompressionError k i k (updatedColumn k i)) →
                      (∀ (k i : Fin p),
                          instLEFin.le k i →
                            LocalDef090 r u A L U recompressionError k k i (updatedRow k i)) →
                        (∀ (k : Fin p), Eq (updatedColumn k k) (updatedRow k k)) →
                          (∀ (k : Fin p),
                              LocalDef091 u (updatedColumn k k) (LocalDef067 L k k)
                                (LocalDef067 U k k)) →
                            (∀ (k i : Fin p),
                                instLTFin.lt k i →
                                  LocalDef093 u (updatedColumn k i) (rawLower i k)
                                    (LocalDef067 U k k)) →
                              (∀ (k i : Fin p),
                                  instLTFin.lt k i →
                                    LocalDef092 u (updatedRow k i)
                                      (LocalDef067 L k k) (rawUpper k i)) →
                                (∀ (k : Fin p),
                                    Real.instLT.lt 0 (LocalDef023 (LocalDef067 U k k))) →
                                  (∀ (k : Fin p),
                                      Real.instLT.lt 0 (LocalDef023 (LocalDef067 L k k))) →
                                    ((k i : Fin p) →
                                        instLTFin.lt k i →
                                          LocalDef086 epsilon
                                            (instHDiv.hDiv (LocalDef088 threshold A i k)
                                              (LocalDef023 (LocalDef067 U k k)))
                                            (rawLower i k) (LocalDef067 L i k)) →
                                      ((k i : Fin p) →
                                          instLTFin.lt k i →
                                            LocalDef086 epsilon
                                              (instHDiv.hDiv (LocalDef088 threshold A k i)
                                                (LocalDef023 (LocalDef067 L k k)))
                                              (rawUpper k i) (LocalDef067 U k i)) →
                                        LocalDef060 r threshold recompression u epsilon A L
                                          U
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a3fc79126a46d76de79c7b2dd592c4fa306fa0a77acfcfb7079a8a221fed499e`

Type:

```lean
(motive : LocalDef031 → Sort u_1) →
  (x : LocalDef031) →
    (Unit → motive LocalDef043) → (Unit → motive LocalDef042) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => LocalDef041 x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7c7d96d802478fd0bf6d0acaa82fe608e40f41316be07d45c944532713344ed5`

Type:

```lean
(motive : LocalDef061 → Sort u_1) →
  (x : LocalDef061) →
    (Unit → motive LocalDef047) →
      (Unit → motive LocalDef048) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => LocalDef087 x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `9e33142dfaa09274a463e2d14509613ff1e15a8f300a5da95769f5c50eb19602`

Type:

```lean
{p b : Nat} → Fin p → Fin b → Fin (instHMul.hMul p b)
```

Definition body (one-level semantic boundary):

```lean
fun {p b} i row => ⟨instHAdd.hAdd (instHMul.hMul i.val b) row.val, ⋯⟩
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `99f5c8c5e48af6d2cd2fe5d29d204dd444168ee995c9045c1f7a0a9f365b9771`

Type:

```lean
{p b : Nat} → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} L => ∀ (i j : Fin p), instLTFin.lt i j → Eq (LocalDef067 L i j) 0
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `23004871ada397d4f70a364b015f381aa517c6fff957fcb31e835bd648dc4259`

Type:

```lean
{p b : Nat} → LocalDef017 (instHMul.hMul p b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} U => ∀ (i j : Fin p), instLTFin.lt j i → Eq (LocalDef067 U i j) 0
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `c2fe5f62aae01995df6fd00f4964b121fe67637620e558fead3ee0984d93d978`

Type:

```lean
Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r => instHAdd.hAdd b.cast (instHMul.hMul r.cast r.cast.sqrt)
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1842193034dc631c3f6c3edebfa469daf6e8b41c15a0037f9331a904ad932e6f`

Type:

```lean
{b r : Nat} → LocalDef046 b r → LocalDef046 b r → LocalDef017 b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X Y => LocalDef095 X (LocalDef096 Y)
```

### D078: `LocalDef078`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `a2203fd1a41fe8de353c91f3b392b65b3cfa4e77158ccb30e3d89a34e69d7f2d`

Type:

```lean
(n : Nat) → LocalDef018 n
```

Definition body (one-level semantic boundary):

```lean
fun n x => 1
```

### D079: `LocalDef079`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ff9394e1a4396a66ba3b3a76d24697c53bbc8fd227a368f05d7863cba41863d5`

Type:

```lean
{p b k : Nat} → Fin p → Fin p → LocalDef046 b k → LocalDef046 b k → LocalDef017 b
```

Definition body (one-level semantic boundary):

```lean
fun {p b k} i j X Y => ite (instLTFin.lt j i) (LocalDef077 X Y) (LocalDef077 Y X)
```

### D080: `LocalDef080`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `deb9d644f031d8e71a57f0238d55fc37a145cb41cbb82b90abe8a87780c03815`

Type:

```lean
{b r : Nat} → LocalDef046 b r → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X => ∀ (j k : Fin r), Eq (Finset.univ.sum fun i => instHMul.hMul (X i j) (X i k)) (ite (Eq j k) 1 0)
```

### D081: `LocalDef081`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `180e72ab7e2b83815485864c04f73550b3146d55b0ba0dc5aa53e5d5207e1fed`

Type:

```lean
LocalDef061 → {p : Nat} → Fin p → Fin p → Prop
```

Definition body (one-level semantic boundary):

```lean
fun direction {p} i j =>
  LocalDef072 (fun direction => Prop) direction
    (fun _ => instLTFin.lt j i) fun _ => instLTFin.lt i j
```

### D082: `LocalDef082`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ff629d092bf564cb4f6878df7bea0122acebac8902cfe13e7d5a277656188c82`

Type:

```lean
LocalDef061 → {p : Nat} → Fin p → Finset (Fin p)
```

Definition body (one-level semantic boundary):

```lean
fun direction {p} i => Finset.filter (LocalDef081 direction i) Finset.univ
```

### D083: `LocalDef083`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `250df853e8b2977888389f94c979b348c242386ad7e0d0083df6609f3c9f25a6`

Type:

```lean
{n : Nat} → LocalDef018 n → LocalDef018 n → LocalDef018 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y i => instHMul.hMul (x i) (y i)
```

### D084: `LocalDef084`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `2212ed50a2f881fa449f39357d3d2124523f7d4309cb3ab0be3d4562f59f558c`

Type:

```lean
{p b : Nat} → LocalDef018 (instHMul.hMul p b) → Fin p → LocalDef018 b
```

Definition body (one-level semantic boundary):

```lean
fun {p b} x i row => x (LocalDef073 i row)
```

### D085: `LocalDef085`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `6`
- Semantic SHA-256: `94a9924a5133c1ce47df1dd7e810851a7a8a8d7066f2219e3c3912e374eb2511`

Type:

```lean
{motive : LocalDef037 → Sort u} →
  motive LocalDef055 →
    motive LocalDef054 → (t : LocalDef037) → motive t
```

### D086: `LocalDef086`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `b39765279d0e57ef423fc04ef4d68b38c574ecdd4718bb8c3ab7b3b12847a03e`

Type:

```lean
{b : Nat} → Real → Real → LocalDef017 b → LocalDef017 b → Type
```

### D087: `LocalDef087`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `2d73782930849562771ac303e47a3463fda2be38408f4f13e7e4caa7c754e04a`

Type:

```lean
{motive : LocalDef061 → Sort u} →
  (t : LocalDef061) →
    motive LocalDef047 →
      motive LocalDef048 → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t lower upper => LocalDef098 lower upper t
```

### D088: `LocalDef088`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `c05e8a18a9508d719f410fe9a4a323436748ea1d9b36c9a8a2461043fc4e82d8`

Type:

```lean
{p b : Nat} → LocalDef031 → LocalDef017 (instHMul.hMul p b) → Fin p → Fin p → Real
```

Definition body (one-level semantic boundary):

```lean
fun {p b} threshold A i k =>
  LocalDef071 (fun threshold => Real) threshold
    (fun _ => LocalDef023 (LocalDef067 A i k)) fun _ => LocalDef023 A
```

### D089: `LocalDef089`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `6`
- Semantic SHA-256: `50fbbd3fed5168541821a0be60abb75d0dedeeb6b80a1cefb693b952f00050fa`

Type:

```lean
∀ {p b : Nat} (i : Fin p) (row : Fin b),
  Nat.instPreorder.lt (instHAdd.hAdd (instHMul.hMul i.val b) row.val) (instHMul.hMul p b)
```

### D090: `LocalDef090`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `41cbac7cf652f6be4ebc733ab7b5211fe050f0bd81c8614698bd5f2e4aa6fcaa`

Type:

```lean
{p b : Nat} →
  Nat →
    Real →
      LocalDef017 (instHMul.hMul p b) →
        LocalDef017 (instHMul.hMul p b) →
          LocalDef017 (instHMul.hMul p b) →
            (Fin p → Fin p → Fin p → LocalDef017 b) → Fin p → Fin p → Fin p → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} r u A L U recompressionError k row col rounded =>
  Exists fun product =>
    Exists fun productError =>
      Exists fun inputRelativeError =>
        Exists fun productRelativeError =>
          And
            (∀ (j : Fin p),
              SetLike.instMembership.mem (LocalDef100 k) j →
                Eq (product j)
                  (instHAdd.hAdd
                    (instHAdd.hAdd
                      (LocalDef035 (LocalDef067 L row j) (LocalDef067 U j col))
                      (recompressionError row col j))
                    (productError j)))
            (And
              (∀ (j : Fin p),
                SetLike.instMembership.mem (LocalDef100 k) j →
                  Real.instLE.le (LocalDef023 (productError j))
                    (instHMul.hMul
                      (instHMul.hMul (LocalDef024 (LocalDef019 b p r) u)
                        (LocalDef023 (LocalDef067 L row j)))
                      (LocalDef023 (LocalDef067 U j col))))
              (And
                (∀ (row col : Fin b),
                  Real.instLE.le (abs (inputRelativeError row col)) (LocalDef024 p.cast u))
                (And
                  (∀ (j : Fin p),
                    SetLike.instMembership.mem (LocalDef100 k) j →
                      ∀ (row col : Fin b),
                        Real.instLE.le (abs (productRelativeError j row col)) (LocalDef024 p.cast u))
                  (Eq rounded
                    (instHSub.hSub
                      (LocalDef101 (LocalDef067 A row col)
                        (instHAdd.hAdd (LocalDef102 b) inputRelativeError))
                      ((LocalDef100 k).sum fun j =>
                        LocalDef101 (product j)
                          (instHAdd.hAdd (LocalDef102 b) (productRelativeError j))))))))
```

### D091: `LocalDef091`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9489312d3d4916286e8e6f13421df89d3e022f8c7cfbc0882a39ab7f2e750b09`

Type:

```lean
{b : Nat} → Real → LocalDef017 b → LocalDef017 b → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u input L U =>
  Exists fun error =>
    And (Eq (LocalDef035 L U) (instHAdd.hAdd input error))
      (Real.instLE.le (LocalDef023 error)
        (instHMul.hMul (instHMul.hMul (LocalDef024 b.cast u) (LocalDef023 L))
          (LocalDef023 U)))
```

### D092: `LocalDef092`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `88ccbda15dcc294ce674c2734d11cc472df25c806160d70e475ec3cc225b68a7`

Type:

```lean
{b : Nat} → Real → LocalDef017 b → LocalDef017 b → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u rhs T X =>
  Exists fun residual =>
    And (Eq (LocalDef035 T X) (instHAdd.hAdd rhs residual))
      (Real.instLE.le (LocalDef023 residual)
        (instHMul.hMul (instHMul.hMul (LocalDef024 b.cast u) (LocalDef023 T))
          (LocalDef023 X)))
```

### D093: `LocalDef093`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `e9f91e2c8bc64fe6ff15ea34032bafe34e2cdf81a248997169fd66c0cf56a2a0`

Type:

```lean
{b : Nat} → Real → LocalDef017 b → LocalDef017 b → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} u rhs X T =>
  Exists fun residual =>
    And (Eq (LocalDef035 X T) (instHAdd.hAdd rhs residual))
      (Real.instLE.le (LocalDef023 residual)
        (instHMul.hMul (instHMul.hMul (LocalDef024 b.cast u) (LocalDef023 T))
          (LocalDef023 X)))
```

### D094: `LocalDef094`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `49760032c70e8094ed8f959a410b29722b18fb40433c9d8066afab8bdb11ac13`

Type:

```lean
{p b : Nat} →
  LocalDef030 →
    LocalDef031 →
      Real → LocalDef017 (instHMul.hMul p b) → (Fin p → Fin p → Fin p → LocalDef017 b) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {p b} choice threshold epsilon A error =>
  LocalDef099 (fun choice => Prop) choice
    (fun _ => ∀ (i k j : Fin p), Eq (error i k j) 0) fun _ =>
    ∀ (row col j : Fin p),
      instLTFin.lt j row →
        instLTFin.lt j col →
          Real.instLE.le (LocalDef023 (error row col j))
            (instHMul.hMul epsilon (LocalDef088 threshold A row col))
```

### D095: `LocalDef095`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `f6707f2e526a146358f007d2349847963679a3556d53c05f30fd242f90c18238`

Type:

```lean
{m n p : Nat} → LocalDef046 m n → LocalDef046 n p → LocalDef046 m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D096: `LocalDef096`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `5d09057ba3a21630e320ba9e9e5153de687ba08c185951b20149ba794d3de258`

Type:

```lean
{m n : Nat} → LocalDef046 m n → LocalDef046 n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A j i => A i j
```

### D097: `LocalDef097`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `a2a4a99e8005463015186023badadb98756eadd332be0e3c7040c61243909ff9`

Type:

```lean
{b : Nat} →
  {epsilon beta : Real} →
    {exact compressed : LocalDef017 b} →
      (rank : Nat) →
        LocalDef103 epsilon beta exact rank compressed →
          (∀ (ell : Nat) (candidate : LocalDef017 b),
              LocalDef103 epsilon beta exact ell candidate → instLENat.le rank ell) →
            (error : LocalDef017 b) →
              Eq compressed (instHAdd.hAdd exact error) →
                Real.instLE.le (LocalDef023 error) (instHMul.hMul epsilon beta) →
                  LocalDef086 epsilon beta exact compressed
```

### D098: `LocalDef098`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `7`
- Semantic SHA-256: `516c254977beabe762211da28071bc73eaf1954ee249231f915228fe589bf21c`

Type:

```lean
{motive : LocalDef061 → Sort u} →
  motive LocalDef047 →
    motive LocalDef048 → (t : LocalDef061) → motive t
```

### D099: `LocalDef099`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `027a317f61f4983bed8f78d418a5a7d35c981ffb5d7c065bbec4e81a11d90c64`

Type:

```lean
(motive : LocalDef030 → Sort u_1) →
  (x : LocalDef030) →
    (Unit → motive LocalDef040) →
      (Unit → motive LocalDef039) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => LocalDef038 x (h_1 Unit.unit) (h_2 Unit.unit)
```

### D100: `LocalDef100`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `5e57755c58a51d81b8ab942a17d06c83af5b98a5f1b248418b1ddfb1a001d914`

Type:

```lean
{p : Nat} → Fin p → Finset (Fin p)
```

Definition body (one-level semantic boundary):

```lean
fun {p} k => Finset.filter (fun j => instLTFin.lt j k) Finset.univ
```

### D101: `LocalDef101`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `8452f0ebcbbeaec37575a22c258d1f411709419662e73d4f68cb0b26721fd425`

Type:

```lean
{n : Nat} → LocalDef017 n → LocalDef017 n → LocalDef017 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => instHMul.hMul (A i j) (B i j)
```

### D102: `LocalDef102`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `a4de0098b36b1e3e1c1be5de8ec1382c5f509ef5b6ed18c3dd9a3177da897caa`

Type:

```lean
(n : Nat) → LocalDef017 n
```

Definition body (one-level semantic boundary):

```lean
fun n x x_1 => 1
```

### D103: `LocalDef103`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `be719c16f25cabc1d9e8f295d0e5cbde11d6d20b71aa9ebf9fffebd0b84ac62b`

Type:

```lean
{b : Nat} → Real → Real → LocalDef017 b → Nat → LocalDef017 b → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b} epsilon beta exact k candidate =>
  Exists fun X =>
    Exists fun Y =>
      And (LocalDef080 X)
        (And (Eq candidate (LocalDef077 X Y))
          (Real.instLE.le (LocalDef023 (instHSub.hSub candidate exact)) (instHMul.hMul epsilon beta)))
```

### D104: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D105: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D106: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D107: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D108: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D109: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D110: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D111: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D112: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D113: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D114: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D115: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D116: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D117: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D118: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D119: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`

Type:

```lean
Add Real
```

Definition body (one-level semantic boundary):

```lean
{ add := Real.add✝ }
```

### D120: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D121: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D122: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D123: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`

Type:

```lean
{α : Type u_1} → [Add α] → HAdd α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
```

### D124: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D125: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `15abc50804fa78aecc5a807f82f13a6b67bcdff9061558426471fc4b606841aa`

Type:

```lean
Mul Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul }
```

### D126: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D127: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D128: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D129: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D130: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D131: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D132: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D133: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D134: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D135: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D136: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D137: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D138: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D139: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D140: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D141: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`

Type:

```lean
DivInvMonoid Real
```

Definition body (one-level semantic boundary):

```lean
{ toMonoid := Real.instMonoid, toInv := Real.instInv, div := DivInvMonoid.div',
  div_eq_mul_inv := Real.instDivInvMonoid._proof_1, zpow := zpowRec, zpow_zero' := Real.instDivInvMonoid._proof_2,
  zpow_succ' := Real.instDivInvMonoid._proof_3, zpow_neg' := Real.instDivInvMonoid._proof_4 }
```

### D142: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D143: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D144: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D145: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

Type:

```lean
Sub Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D146: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D147: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D148: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D149: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D150: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D151: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`

Type:

```lean
{α : Type u_1} → [Lattice α] → [AddGroup α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D152: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D153: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D154: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D155: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D156: `Nonempty`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `37c79de378d44cb9dc334502b161bb140da0544579086aded2cf83ff99c462c7`

Type:

```lean
Sort u → Prop
```

### D157: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D158: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D159: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D160: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D161: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D162: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f9a0c1f5b41c8d9a8658798c73b295495f6dfbf0bd7d081817aec4f598bbfc46`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub α] → Sub (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Sub α] => Pi.instSub
```

### D163: `Pi.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Pi.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `9b57724ac626ed82a5e3b9060068391fe112af839994c2304c9990493e8e9fbc`

Type:

```lean
{I : Type u} → {f : I → Type v₁} → [(i : I) → AddCommMonoid (f i)] → AddCommMonoid ((i : I) → f i)
```

Definition body (one-level semantic boundary):

```lean
fun {I} {f} [(i : I) → AddCommMonoid (f i)] =>
  let __src := Pi.addMonoid;
  have __src_1 := Pi.addCommSemigroup;
  { toAddMonoid := __src, add_comm := ⋯ }
```

### D164: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`

Type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub (G i)] → Sub ((i : ι) → G i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {G} [(i : ι) → Sub (G i)] => { sub := fun f g i => instHSub.hSub (f i) (g i) }
```

### D165: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D166: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D167: `Classical.propDecidable`

- Role: `external-frontier`
- Owner module: `Init.Classical`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `823c02cb7dcdb8ce30edfb12a2496dda0849f0773c65f9e91e289fab27c36c46`

Type:

```lean
(a : Prop) → Decidable a
```

Definition body (one-level semantic boundary):

```lean
fun a => Classical.choice ⋯
```

### D168: `Fin.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `24fa4b4b6252c6619c7be20c8f88b00ad65adc22900c2f8cef15ab1ce2247816`

Type:

```lean
{n : Nat} → (a b : Fin n) → Decidable (instLTFin.lt a b)
```

Definition body (one-level semantic boundary):

```lean
fun {n} a b => a.val.decLt b.val
```

### D169: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D170: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D171: `Finset`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Defs`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `56a880af39b5f8e2e55560abe97637994d5830a3a7ed0adaa46c44b8c3eaf831`

Type:

```lean
Type u_4 → Type u_4
```

### D172: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `cc2bad5c5cc6aa2b196abe33b9083d127ab69155f1189766c3500bb83412c7df`

Type:

```lean
{α : Type u_1} → (p : α → Prop) → [DecidablePred p] → Finset α → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p [DecidablePred p] s => { val := Multiset.filter p s.val, nodup := ⋯ }
```

### D173: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D174: `instLEFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ebac56428fb1bdf0060f322d2454b52c141188f43ac10a1e1c3b3437e05db596`

Type:

```lean
{n : Nat} → LE (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { le := fun a b => instLENat.le a.val b.val }
```

### D175: `instLTFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `8cd15fdbb565335569354b3a92dd84648b7f425b56b502181ab2df382268eb87`

Type:

```lean
{n : Nat} → LT (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { lt := fun a b => instLTNat.lt a.val b.val }
```

### D176: `Finset.instSetLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `f43bd57c8a5e05334ba371d3e354fb5f1cd42a3177ae342e6448d872bd6428b6`

Type:

```lean
{α : Type u_1} → SetLike (Finset α) α
```

Definition body (one-level semantic boundary):

```lean
fun {α} => { coe := fun s => setOf fun a => Multiset.instMembership.mem s.val a, coe_injective' := ⋯ }
```

### D177: `Matrix.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `6b893d81bc298230772e16cd0c8ddf7d2638ac0d6127094b06a1290d88f8c3ae`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [AddCommMonoid α] → AddCommMonoid (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [AddCommMonoid α] => Pi.addCommMonoid
```

### D178: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `941ea3346e809f919727c21bfcdeea342714a6b83f1cf871d648aa2cb14d6e9e`

Type:

```lean
{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} γ [self : Membership α γ] => self.1
```

### D179: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D180: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `8fcf5a8f5a8899408a8cdc310bc44f6f7b84a21905a114103fbc65083f779a43`

Type:

```lean
{α : Type u_2} → [self : Preorder α] → LT α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Preorder α] => self.2
```

### D181: `SetLike.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.SetLike.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `47a75450bbb51c4e8fdd9e8881cc3fa741dfb5f1f186d952055686e285c081e4`

Type:

```lean
{A : Type u_1} → {B : Type u_2} → [i : SetLike A B] → Membership B A
```

Definition body (one-level semantic boundary):

```lean
fun {A} {B} [i : SetLike A B] => { mem := fun p x => Set.instMembership.mem (i.coe p) x }
```
