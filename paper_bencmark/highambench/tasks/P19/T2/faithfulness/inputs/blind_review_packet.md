# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (execution : LocalDef012 l),
  Exists fun k =>
    And (Eq k execution.run.keyDimension)
      (And (instLTNat.lt 0 k)
        (And (instLENat.le k n)
          (And
            (Filter.Eventually
              (fun t =>
                And (Real.instLE.le (instHDiv.hDiv 1 (execution.run.vHatSpectrum t).sigmaMin) (4 / 3))
                  (Real.instLE.le (execution.run.vHatSpectrum t).sigmaMax (4 / 3)))
              l)
            (∀ (MR MRinv : LocalDef003 n) (hMR : LocalDef018 MR MRinv),
              have analysis := execution.forwardAnalysis MR MRinv hMR;
              LocalDef016 l (LocalDef020 execution.run)
                (fun t => LocalDef017 execution.run.xExact (execution.run.xHat t)) fun t =>
                instHMul.hMul
                  (instHMul.hMul (LocalDef019 execution.run.polynomialFactor n k)
                    (LocalDef023 execution.run MR MRinv analysis.quantities t))
                  (LocalDef015 (LocalDef022 execution.run MRinv)
                    (LocalDef021 execution.run MR))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (execution : @LocalDef012.{u_1} n ι l),
  @Exists.{1} Nat fun (k : Nat) =>
    And
      (@Eq.{1} Nat k
        (@LocalDef004.{u_1} n ι l
          (@LocalDef014.{u_1} n ι l execution)))
      (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        (And (@LE.le.{0} Nat instLENat k n)
          (And
            (@Filter.Eventually.{u_1} ι
              (fun (t : ι) =>
                And
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@LocalDef011 n
                        (@LocalDef004.{u_1} n ι l
                          (@LocalDef014.{u_1} n ι l execution))
                        (@LocalDef006.{u_1} n ι l
                          (@LocalDef014.{u_1} n ι l execution) t)
                        (@LocalDef007.{u_1} n ι l
                          (@LocalDef014.{u_1} n ι l execution) t)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@LE.le.{0} Real Real.instLE
                    (@LocalDef010 n
                      (@LocalDef004.{u_1} n ι l
                        (@LocalDef014.{u_1} n ι l execution))
                      (@LocalDef006.{u_1} n ι l
                        (@LocalDef014.{u_1} n ι l execution) t)
                      (@LocalDef007.{u_1} n ι l
                        (@LocalDef014.{u_1} n ι l execution) t))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
              l)
            (∀ (MR MRinv : LocalDef003 n) (hMR : @LocalDef018 n MR MRinv),
              have analysis :
                @LocalDef001.{u_1} n ι l
                  (@LocalDef014.{u_1} n ι l execution) MR MRinv :=
                @LocalDef013.{u_1} n ι l execution MR MRinv hMR;
              @LocalDef016.{u_1} ι l
                (@LocalDef020.{u_1} n ι l
                  (@LocalDef014.{u_1} n ι l execution))
                (fun (t : ι) =>
                  @LocalDef017 n
                    (@LocalDef008.{u_1} n ι l
                      (@LocalDef014.{u_1} n ι l execution))
                    (@LocalDef009.{u_1} n ι l
                      (@LocalDef014.{u_1} n ι l execution) t))
                fun (t : ι) =>
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (LocalDef019
                      (@LocalDef005.{u_1} n ι l
                        (@LocalDef014.{u_1} n ι l execution))
                      n k)
                    (@LocalDef023.{u_1} n ι l (@LocalDef014.{u_1} n ι l execution) MR
                      MRinv
                      (@LocalDef002.{u_1} n ι l
                        (@LocalDef014.{u_1} n ι l execution) MR MRinv analysis)
                      t))
                  (@LocalDef015 n
                    (@LocalDef022.{u_1} n ι l
                      (@LocalDef014.{u_1} n ι l execution) MRinv)
                    (@LocalDef021.{u_1} n ι l
                      (@LocalDef014.{u_1} n ι l execution) MR))))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9ac83a09bfd7bab55e17ae5c7fc00b601ce16d2b27a44f15a85ddee2cb21891`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → LocalDef025 l → LocalDef003 n → LocalDef003 n → Type u_1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0b438ee8658c81f0e84c7639a3f4e9c6775ef1bef01c5a58c2a3dc11dac2c356`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : LocalDef025 l} →
        {MR MRinv : LocalDef003 n} →
          LocalDef001 run MR MRinv → LocalDef039 run MR MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n ι l run MR MRinv self => self.1
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `da34af64745188df680411658bb275d858795f5d4483f121fbd1b2751be7bd09`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `767f69e4769c4c0becd2befca856b405e9162005c29c09510ea257270525ec38`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.13
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `553771567bab00d42d3938d46e9b207922460f90b77e05070799f49270fe1140`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef034
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.16
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4ac504c95889845aa9c51165baec4964b1578a4c41ec218261e98f1d6e05954b`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : LocalDef025 l) → ι → LocalDef038 n self.keyDimension
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.31
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `14279e80ea4d996a83bca8b47cd3e87afc7ca5416e052d656cb43d2fe52058e0`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (self : LocalDef025 l) → (t : ι) → LocalDef040 (self.vHat t)
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.52
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cc197682e9da3daeb8ee25b764ecc2be7634b595dbf390f0b556c107ac5399c0`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.7
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2324897d125aa383706a0f450a66a8a3717e5ab91749b471f1b1311eeb85e105`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.47
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `39b1024085d127c92aa430d39d98d3d00a99a5d1c44ea3bcaff897aa19328ba4`

Type:

```lean
{m k : Nat} → {A : LocalDef038 m k} → LocalDef040 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.2
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1013716a93aaa4244e940de911b2c7afefa568b957b54095b8426864b032c52c`

Type:

```lean
{m k : Nat} → {A : LocalDef038 m k} → LocalDef040 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.1
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `5b717643c51c82887357e2b74e5fa20e19cb0901d113af9598f0354a6996fd66`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e1b834f84752ac6d0222710bc13db30a366a5efd6161ae03c36f2945c568a341`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (self : LocalDef012 l) →
        (MR MRinv : LocalDef003 n) →
          LocalDef018 MR MRinv → LocalDef001 self.run MR MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a13cc3e797365b0c4a89dfb8193b07af59cf5be5cc83ee580f94bd18113eb0ee`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef012 l → LocalDef025 l
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.1
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0caab4531a1846f654c1dd00b274cf19ace9e44cbf1773a4d95f56800e9ffd1`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef045 Ainv) (LocalDef045 A)
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `762c7d3a1b43802433562110427d7f354a4212f105bf0df6b4094874cda3499e`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (LocalDef049 l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `de704d15118aaa066da7b9d608fb5f38683c608a436633eec639f8da74709601`

Type:

```lean
{n : Nat} → LocalDef042 n → LocalDef042 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (LocalDef051 (instHSub.hSub xHat x)) (LocalDef051 x)
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `77b8f45040142dc9a1f4c41dcad3fdb3c16d0ebc240adbaa5dac1c0ffabb00df`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef003 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv =>
  And (∀ (x : LocalDef042 n), Eq (LocalDef047 Ainv (LocalDef047 A x)) x)
    (∀ (x : LocalDef042 n), Eq (LocalDef047 A (LocalDef047 Ainv x)) x)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e32297e66203da021d9ce43ebf603a182f9ddfad04cfab209bfb4f1246022f1d`

Type:

```lean
LocalDef034 → Nat → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun c n k =>
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      instHMul.hMul (instHMul.hMul (c.coefficient i j) (instHPow.hPow n.cast i.val)) (instHPow.hPow k.cast j.val)
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fad5b1a69feb7a1d2c4461019923c00ea4539e608602c407f6db7cbeb1f645a2`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHAdd.hAdd (instHAdd.hAdd (instHAdd.hAdd (run.epsilonC t) (run.epsilonB t)) (run.ug t)) (run.epsilonX t)
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9477aec818a5cb51663615169812c4e799cb323f77050999d8483829388a05be`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR => LocalDef050 MR (LocalDef050 run.Ainv run.ML)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4865bff1cf8cab324d5e100bf3645aa19c2a7d74b2d0f8fe3be2945b09440241`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MRinv => LocalDef050 run.MLinv (LocalDef050 run.A MRinv)
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe707534cb683a4ab207547ffb88e334426fe75e025851328be68292e8485852`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : LocalDef025 l) →
        (MR MRinv : LocalDef003 n) → LocalDef039 run MR MRinv → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  LocalDef048 (LocalDef043 run MR MRinv q t) (LocalDef044 run MR MRinv q t)
    (LocalDef046 run MR MRinv) (run.epsilonC t) (run.epsilonB t) (run.ug t) (run.epsilonX t)
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `f65902c46b4d8ef84c868f62ccb61d08728a331e93f2c6a1cbcc883f46c9603e`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : LocalDef025 l} →
        {MR MRinv : LocalDef003 n} →
          (quantities : LocalDef039 run MR MRinv) →
            (computationPropagation : ι → LocalDef038 n run.keyDimension → LocalDef042 n) →
              (rhsPropagation leastSquaresBPropagation : ι → LocalDef042 n → LocalDef042 n) →
                (leastSquaresCPropagation :
                    ι → LocalDef038 n run.keyDimension → LocalDef042 n) →
                  (solutionPropagation : ι → LocalDef042 n → LocalDef042 n) →
                    (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                        ι → LocalDef042 n) →
                      (∀ (t : ι), Eq (computationContribution t) (computationPropagation t (run.deltaC t))) →
                        (∀ (t : ι), Eq (rhsContribution t) (rhsPropagation t (run.deltaB t))) →
                          (∀ (t : ι),
                              Eq (gmresContribution t)
                                (instHAdd.hAdd (leastSquaresBPropagation t (run.leastSquaresDeltaB t))
                                  (leastSquaresCPropagation t (run.leastSquaresDeltaC t)))) →
                            (∀ (t : ι), Eq (solutionContribution t) (solutionPropagation t (run.deltaX t))) →
                              (∀ (t : ι), Eq (computationPropagation t 0) 0) →
                                (∀ (t : ι), Eq (rhsPropagation t 0) 0) →
                                  (∀ (t : ι), Eq (leastSquaresBPropagation t 0) 0) →
                                    (∀ (t : ι), Eq (leastSquaresCPropagation t 0) 0) →
                                      (∀ (t : ι), Eq (solutionPropagation t 0) 0) →
                                        (∀ (t : ι),
                                            Eq (instHSub.hSub (run.xHat t) run.xExact)
                                              (instHAdd.hAdd
                                                (instHAdd.hAdd
                                                  (instHAdd.hAdd
                                                    (instHAdd.hAdd (computationContribution t) (rhsContribution t))
                                                    (gmresContribution t))
                                                  (solutionContribution t))
                                                (remainder t))) →
                                          (∀ (t : ι),
                                              Real.instLE.le
                                                (instHDiv.hDiv (LocalDef051 (computationContribution t))
                                                  (LocalDef051 run.xExact))
                                                (instHMul.hMul
                                                  (instHMul.hMul
                                                    (LocalDef019 run.polynomialFactor n
                                                      run.keyDimension)
                                                    (LocalDef015
                                                      (LocalDef022 run MRinv)
                                                      (LocalDef021 run MR)))
                                                  (instHMul.hMul (LocalDef043 run MR MRinv quantities t)
                                                    (run.epsilonC t)))) →
                                            (∀ (t : ι),
                                                Real.instLE.le
                                                  (instHDiv.hDiv (LocalDef051 (rhsContribution t))
                                                    (LocalDef051 run.xExact))
                                                  (instHMul.hMul
                                                    (instHMul.hMul
                                                      (LocalDef019 run.polynomialFactor n
                                                        run.keyDimension)
                                                      (LocalDef015
                                                        (LocalDef022 run MRinv)
                                                        (LocalDef021 run MR)))
                                                    (instHMul.hMul (LocalDef044 run MR MRinv quantities t)
                                                      (run.epsilonB t)))) →
                                              (∀ (t : ι),
                                                  Real.instLE.le
                                                    (instHDiv.hDiv (LocalDef051 (gmresContribution t))
                                                      (LocalDef051 run.xExact))
                                                    (instHMul.hMul
                                                      (instHMul.hMul
                                                        (LocalDef019 run.polynomialFactor n
                                                          run.keyDimension)
                                                        (LocalDef015
                                                          (LocalDef022 run MRinv)
                                                          (LocalDef021 run MR)))
                                                      (instHMul.hMul (LocalDef044 run MR MRinv quantities t)
                                                        (run.ug t)))) →
                                                (∀ (t : ι),
                                                    Real.instLE.le
                                                      (instHDiv.hDiv (LocalDef051 (solutionContribution t))
                                                        (LocalDef051 run.xExact))
                                                      (instHMul.hMul
                                                        (instHMul.hMul
                                                          (LocalDef019 run.polynomialFactor n
                                                            run.keyDimension)
                                                          (LocalDef015
                                                            (LocalDef022 run MRinv)
                                                            (LocalDef021 run MR)))
                                                        (instHMul.hMul (LocalDef046 run MR MRinv)
                                                          (run.epsilonX t)))) →
                                                  (LocalDef049 l (LocalDef020 run)
                                                      fun t =>
                                                      instHDiv.hDiv (LocalDef051 (remainder t))
                                                        (LocalDef051 run.xExact)) →
                                                    LocalDef001 run MR MRinv
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6c5961570fb514c1634dc4e0e0a4185d234ac058cd3dfb106326004fc13fdbda`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0ce3a906eed62528020a8c781eb29417572547dfafaeed377c4b63b4562b14c2`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `71cdba8088718feb6bf0c74041ed1089da00356008a16b896dfe855d1e95a6a7`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.3
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b481783919dde74d3043e6900772f3a93ea4e0ed28802a1668d3238d6fa50ecd`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.4
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f770cefa03e5dfb30cbeaa365932555ca4822ad26ee0dee8f64159af97cb8696`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef003 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.5
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `432a7da4065c28bef283f93899aa0e147a4eb1d543ceeee6de6da6304d8df53c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.18
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `bcc2a28e246363fff15906f5bf38b406f655185faac9565c2d08ec471ceab3ce`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.17
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a79118e51524a23c26ab3bf88605cc5ad6b9dbc9e6867e9eca95f0f3a4250ba5`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.20
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d1fafdb6c4a35d493154f8a360635ed5256777015c8239006ace146575fc2161`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.19
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a277c56923b73b8cbd2ff65bc6ad14878794606b603837ef0396952b58e944d9`

Type:

```lean
Type
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9621c065f238974bb2a7f1cd1fe45a52c03304d6ef88994300d1147e3391dbdc`

Type:

```lean
(self : LocalDef034) →
  Fin (instHAdd.hAdd self.degreeN 1) → Fin (instHAdd.hAdd self.degreeK 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a01c1f807284de44bbe07bbd3a2d026399a18a1fbba970fb07b404a97a078f97`

Type:

```lean
LocalDef034 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `747b227a49e80a41dfe67147163421d6a73f878c21d1a01b7b51e6c425ff7a6f`

Type:

```lean
LocalDef034 → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `439dd553c0545a1da7e92aa2fe36a24aa581a6f27bc01f3f2b81504fea271a29`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ecfe7f38d457064664c1e9d39d7e4ce312574c629a9618863967a345704ba3d4`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → LocalDef025 l → LocalDef003 n → LocalDef003 n → Type u_1
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → LocalDef038 m k → Type
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `9ad26490b78040e4a2cce78f162e37d95460fd67371e05744ce5b9388396fd19`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : LocalDef025 l) →
        ((MR MRinv : LocalDef003 n) →
            LocalDef018 MR MRinv → LocalDef001 run MR MRinv) →
          LocalDef012 l
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f1f6f4466f0d4de5052934629682ac38b1dc670a54dad0a303f7ed04448984d9`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a56cbd7beb408e81cc0a8e5a16bd3803326cbca2db7a8b5f7df6483ee236b456`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : LocalDef025 l) →
        (MR MRinv : LocalDef003 n) → LocalDef039 run MR MRinv → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  instHMul.hMul (instHDiv.hDiv (LocalDef015 MR MRinv) (q.mrzSpectrum t).sigmaMin)
    (instHDiv.hDiv (LocalDef045 (LocalDef064 run t))
      (LocalDef045 (LocalDef022 run MRinv)))
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ccf45d1b3776c1251f48b362abde5d03cc4fc98635c4acddcfa679d206528bed`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : LocalDef025 l) →
        (MR MRinv : LocalDef003 n) → LocalDef039 run MR MRinv → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv q t =>
  instHMul.hMul
    (Real.instMax.max 1
      (instHDiv.hDiv
        (instHDiv.hDiv (LocalDef045 (LocalDef064 run t))
          (LocalDef045 (LocalDef022 run MRinv)))
        (q.mrzSpectrum t).sigmaMin))
    (LocalDef015 MR MRinv)
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1d77e739886fafe42f3444123b92bfd0ee9c522738b34d29764b9a10cb431f73`

Type:

```lean
{m k : Nat} → LocalDef038 m k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a4138ec36bd4cba05513fd06dbc017aea3f59e262d7bde78e234fcd23b2326b0`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → LocalDef025 l → LocalDef003 n → LocalDef003 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run MR MRinv =>
  instHDiv.hDiv 1
    (LocalDef015 (LocalDef022 run MRinv) (LocalDef021 run MR))
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1ae9d14b7b4a526e86a7616a8ca6e9f01f9c771fcb8636b83a7aee0f1c7547c1`

Type:

```lean
{n : Nat} → LocalDef003 n → LocalDef042 n → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4d1f50569f1e938522ad9eb1ae93404d40243c6ec09407ff5120e6b1032a551c`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun alpha beta lambda epsilonC epsilonB ug epsilonX =>
  instHAdd.hAdd
    (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul alpha epsilonC) (instHMul.hMul beta epsilonB)) (instHMul.hMul beta ug))
    (instHMul.hMul lambda epsilonX)
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `be18d1baa6a2642eef71fd1188d02fbf532849ff793b47048d71b3ff31a20335`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2b8444b51bdd6b2f43ba4d5ab8376e63a1788f241ad49a66ee55d945464e1769`

Type:

```lean
{n k : Nat} → LocalDef003 n → LocalDef038 n k → LocalDef038 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6b6e1bd375429f5aeb20a6f7108df37b3e72d1ec77d5e9de9ed7b15b6a12565e`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (LocalDef065 x).sqrt
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ea70ac01cbc08de52a454d21e6f55d67e23415834c4fb2a7940ceb5c80c625ea`

Type:

```lean
{n : Nat} → {ι : Type u_1} → LocalDef066 n ι → (k : Nat) → ι → LocalDef038 n k
```

Definition body (one-level semantic boundary):

```lean
fun n ι self => self.1
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `feda3a60d7050f57efdd50df71f0c36c7444163064341d357a47344c0d29e661`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → LocalDef066 n ι
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.12
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d22832f89b0e15884606c8362a4d72a1625e89283cd8ce30c1f839cba9a7a703`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.28
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `429a7a1f66277b258a86c83b66387d1fc1c862f79b8dd9fc6dd9d157051262f5`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : LocalDef025 l) → ι → LocalDef038 n self.keyDimension
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.24
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a6637cee9f79cabbed0a9d377c77096d77165a541c22205e8316c5ed64a4a9c5`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.48
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e74dc228173db84ea616b718ea11d8b43e0f7fbd545bbaab8e4a92662285f8ac`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → LocalDef025 l → ι → LocalDef042 n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.38
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9a0e064298849ae0d2110809ff753ce1bcbf99b53936f5efd4d91874308b9ed9`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (self : LocalDef025 l) → ι → LocalDef038 n self.keyDimension
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.39
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `8b3be08a29236a310e5547e060c838db69a40536fc680c23a42640826bd2af54`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      instLTNat.lt 0 n →
        (A Ainv ML MLinv : LocalDef003 n) →
          (b xExact : LocalDef042 n) →
            LocalDef018 A Ainv →
              LocalDef018 ML MLinv →
                Ne b 0 →
                  Eq (LocalDef047 A xExact) b →
                    (basisFamily : LocalDef066 n ι) →
                      (keyDimension : Nat) →
                        instLTNat.lt 0 keyDimension →
                          instLENat.le keyDimension n →
                            (polynomialFactor : LocalDef034) →
                              (epsilonC epsilonB ug epsilonX : ι → Real) →
                                (∀ (t : ι),
                                    And (Real.instLE.le 0 (epsilonC t))
                                      (And (Real.instLE.le 0 (epsilonB t))
                                        (And (Real.instLE.le 0 (ug t)) (Real.instLE.le 0 (epsilonX t))))) →
                                  And (Filter.Tendsto epsilonC l (nhds 0))
                                      (And (Filter.Tendsto epsilonB l (nhds 0))
                                        (And (Filter.Tendsto ug l (nhds 0)) (Filter.Tendsto epsilonX l (nhds 0)))) →
                                    (computedC deltaC : ι → LocalDef038 n keyDimension) →
                                      (∀ (t : ι),
                                          Eq (computedC t)
                                            (instHAdd.hAdd
                                              (LocalDef050 MLinv
                                                (LocalDef050 A (basisFamily.basis keyDimension t)))
                                              (deltaC t))) →
                                        (∀ (t : ι),
                                            Real.instLE.le (LocalDef045 (deltaC t))
                                              (instHMul.hMul (epsilonC t)
                                                (LocalDef045
                                                  (LocalDef050 MLinv
                                                    (LocalDef050 A
                                                      (basisFamily.basis keyDimension t)))))) →
                                          (computedB deltaB : ι → LocalDef042 n) →
                                            (∀ (t : ι),
                                                Eq (computedB t)
                                                  (instHAdd.hAdd (LocalDef047 MLinv b) (deltaB t))) →
                                              (∀ (t : ι),
                                                  Real.instLE.le (LocalDef051 (deltaB t))
                                                    (instHMul.hMul (epsilonB t)
                                                      (LocalDef051 (LocalDef047 MLinv b)))) →
                                                (vHat : ι → LocalDef038 n keyDimension) →
                                                  (vHatNext :
                                                      ι → LocalDef038 n (instHAdd.hAdd keyDimension 1)) →
                                                    (beta : ι → Real) →
                                                      (hessenberg :
                                                          ι →
                                                            LocalDef038 (instHAdd.hAdd keyDimension 1)
                                                              keyDimension) →
                                                        (∀ (t : ι), LocalDef070 (hessenberg t)) →
                                                          (∀ (t : ι),
                                                              Eq (LocalDef067 (computedB t) (computedC t))
                                                                (LocalDef073 (vHatNext t)
                                                                  (LocalDef067
                                                                    (LocalDef075 (beta t))
                                                                    (hessenberg t)))) →
                                                            (∀ (t : ι) (i : Fin n) (j : Fin keyDimension),
                                                                Eq (vHat t i j) (vHatNext t i j.castSucc)) →
                                                              (leastSquaresDeltaB : ι → LocalDef042 n) →
                                                                (leastSquaresDeltaC :
                                                                    ι → LocalDef038 n keyDimension) →
                                                                  (yHat : ι → LocalDef042 keyDimension) →
                                                                    (∀ (t : ι),
                                                                        LocalDef069
                                                                          (instHAdd.hAdd (computedC t)
                                                                            (leastSquaresDeltaC t))
                                                                          (instHAdd.hAdd (computedB t)
                                                                            (leastSquaresDeltaB t))
                                                                          (yHat t)) →
                                                                      (∀ (t : ι)
                                                                          (j : Fin (instHAdd.hAdd keyDimension 1)),
                                                                          Real.instLE.le
                                                                            (LocalDef051
                                                                              (LocalDef068
                                                                                (LocalDef067
                                                                                  (leastSquaresDeltaB t)
                                                                                  (leastSquaresDeltaC t))
                                                                                j))
                                                                            (instHMul.hMul
                                                                              (instHMul.hMul
                                                                                (LocalDef019
                                                                                  polynomialFactor n keyDimension)
                                                                                (ug t))
                                                                              (LocalDef051
                                                                                (LocalDef068
                                                                                  (LocalDef067 (computedB t)
                                                                                    (computedC t))
                                                                                  j)))) →
                                                                        (computedCSpectrum :
                                                                            (t : ι) →
                                                                              LocalDef040
                                                                                (computedC t)) →
                                                                          (LocalDef071 l fun t =>
                                                                              instHMul.hMul (ug t)
                                                                                (LocalDef072
                                                                                  (computedC t)
                                                                                  (computedCSpectrum t).sigmaMin)) →
                                                                            (exactCSpectrum :
                                                                                (t : ι) →
                                                                                  LocalDef040
                                                                                    (LocalDef050 MLinv
                                                                                      (LocalDef050 A
                                                                                        (basisFamily.basis keyDimension
                                                                                          t)))) →
                                                                              (LocalDef071 l
                                                                                  fun t =>
                                                                                  instHMul.hMul
                                                                                    (instHAdd.hAdd
                                                                                      (instHAdd.hAdd (epsilonC t)
                                                                                        (epsilonB t))
                                                                                      (ug t))
                                                                                    (LocalDef072
                                                                                      (LocalDef050
                                                                                        MLinv
                                                                                        (LocalDef050 A
                                                                                          (basisFamily.basis
                                                                                            keyDimension t)))
                                                                                      (exactCSpectrum t).sigmaMin)) →
                                                                                (xHat deltaX :
                                                                                    ι → LocalDef042 n) →
                                                                                  (∀ (t : ι),
                                                                                      Eq (xHat t)
                                                                                        (instHAdd.hAdd
                                                                                          (LocalDef074
                                                                                            (basisFamily.basis
                                                                                              keyDimension t)
                                                                                            (yHat t))
                                                                                          (deltaX t))) →
                                                                                    (∀ (t : ι),
                                                                                        Real.instLE.le
                                                                                          (LocalDef051
                                                                                            (deltaX t))
                                                                                          (instHMul.hMul (epsilonX t)
                                                                                            (LocalDef051
                                                                                              (LocalDef074
                                                                                                (basisFamily.basis
                                                                                                  keyDimension t)
                                                                                                (yHat t))))) →
                                                                                      LocalDef071 l
                                                                                          epsilonX →
                                                                                        (vHatSpectrum :
                                                                                            (t : ι) →
                                                                                              LocalDef040
                                                                                                (vHat t)) →
                                                                                          (mgsOrthogonalityDefect :
                                                                                              ι → Real) →
                                                                                            (∀ (t : ι),
                                                                                                Real.instLE.le 0
                                                                                                  (mgsOrthogonalityDefect
                                                                                                    t)) →
                                                                                              Filter.Eventually
                                                                                                  (fun t =>
                                                                                                    Real.instLE.le
                                                                                                      (mgsOrthogonalityDefect
                                                                                                        t)
                                                                                                      (7 / 16))
                                                                                                  l →
                                                                                                (∀ (t : ι),
                                                                                                    Real.instLE.le
                                                                                                      (instHSub.hSub 1
                                                                                                        (mgsOrthogonalityDefect
                                                                                                          t))
                                                                                                      (instHPow.hPow
                                                                                                        (vHatSpectrum
                                                                                                            t).sigmaMin
                                                                                                        2)) →
                                                                                                  (∀ (t : ι),
                                                                                                      Real.instLE.le
                                                                                                        (instHPow.hPow
                                                                                                          (vHatSpectrum
                                                                                                              t).sigmaMax
                                                                                                          2)
                                                                                                        (instHAdd.hAdd 1
                                                                                                          (mgsOrthogonalityDefect
                                                                                                            t))) →
                                                                                                    LocalDef025
                                                                                                      l
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `d58684bdda1ea68b662f7a64d90373af65ef0a9d2ae7c566f7f577b882df1bbb`

Type:

```lean
(degreeN degreeK : Nat) →
  (coefficient : Fin (instHAdd.hAdd degreeN 1) → Fin (instHAdd.hAdd degreeK 1) → Real) →
    (∀ (i : Fin (instHAdd.hAdd degreeN 1)) (j : Fin (instHAdd.hAdd degreeK 1)), Real.instLE.le 0 (coefficient i j)) →
      LocalDef034
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `0c3f47600c05b183f7722f41b79ef5c4b7faff9a6900372e65146ed02e54da98`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : LocalDef025 l} →
        {MR MRinv : LocalDef003 n} →
          (mrzSpectrum :
              (t : ι) →
                LocalDef040
                  (LocalDef050 MR (run.basisFamily.basis run.keyDimension t))) →
            (∀ (t : ι), Real.instLT.lt 0 (mrzSpectrum t).sigmaMin) →
              LocalDef039 run MR MRinv
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fa4d18c7380daa3f66d2f771770298f12d6c9d2b454bd697a6fdf28177e01cfe`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : LocalDef025 l} →
        {MR MRinv : LocalDef003 n} →
          LocalDef039 run MR MRinv →
            (t : ι) →
              LocalDef040
                (LocalDef050 MR (run.basisFamily.basis run.keyDimension t))
```

Definition body (one-level semantic boundary):

```lean
fun n ι l run MR MRinv self => self.1
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `785b5c97bf75f07f40320aa93a7623aeb13039753f9b0be30629411ab231dca4`

Type:

```lean
{m k : Nat} →
  {A : LocalDef038 m k} →
    (sigmaMin sigmaMax : Real) →
      Real.instLE.le 0 sigmaMin →
        Real.instLE.le 0 sigmaMax →
          (∀ (x : LocalDef042 k),
              Real.instLE.le (instHMul.hMul sigmaMin (LocalDef051 x))
                (LocalDef051 (LocalDef074 A x))) →
            (∀ (x : LocalDef042 k),
                Real.instLE.le (LocalDef051 (LocalDef074 A x))
                  (instHMul.hMul sigmaMax (LocalDef051 x))) →
              (instLTNat.lt 0 k →
                  Exists fun x =>
                    And (Eq (LocalDef051 x) 1)
                      (Eq (LocalDef051 (LocalDef074 A x)) sigmaMin)) →
                (instLTNat.lt 0 k →
                    Exists fun x =>
                      And (Eq (LocalDef051 x) 1)
                        (Eq (LocalDef051 (LocalDef074 A x)) sigmaMax)) →
                  LocalDef040 A
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d53169450812b017abdf4df9c66e1a9b6df67cc41fa03b150e209b66934af9ab`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → (run : LocalDef025 l) → ι → LocalDef038 n run.keyDimension
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  LocalDef050 run.MLinv (LocalDef050 run.A (run.basisFamily.basis run.keyDimension t))
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e29dbb51f77b0df1c2e4cbb308e8a6e36e232c2b0ce38cd883c0b946cd01ea97`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Finset.univ.sum fun i => instHPow.hPow (x i) 2
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `7964a4dd38133453ceffb7b7c9c982dc1c8ac2e6beb707f90bc36f96a00f0897`

Type:

```lean
Nat → Type u_1 → Type u_1
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `2fe0e06752730d60394b59adb4b76c6f22ea6681023a70406cbdcfc4ba900101`

Type:

```lean
{n k : Nat} → LocalDef042 n → LocalDef038 n k → LocalDef038 n (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b C i i_1 => Fin.cases (b i) (fun j => C i j) i_1
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d1c96c67d25102fa9368afc8215a13cc0626a5b92b4ea3b4e4f9c82429d0c977`

Type:

```lean
{m k : Nat} → LocalDef038 m k → Fin k → LocalDef042 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A j i => A i j
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `3007f611ab5087af1f0566bf60dfd75fc71f78dad5e293cff7cd63de4c42ed91`

Type:

```lean
{m k : Nat} → LocalDef038 m k → LocalDef042 m → LocalDef042 k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : LocalDef042 k),
    Real.instLE.le (LocalDef051 (instHSub.hSub b (LocalDef074 A y)))
      (LocalDef051 (instHSub.hSub b (LocalDef074 A z)))
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `40e9dda219091e0a8274024ac3a6a6ec9b0f2c87f705a5d5c83ed03835619d3e`

Type:

```lean
{k : Nat} → LocalDef038 (instHAdd.hAdd k 1) k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {k} H => ∀ (i : Fin (instHAdd.hAdd k 1)) (j : Fin k), instLTNat.lt (instHAdd.hAdd j.val 1) i.val → Eq (H i j) 0
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `94328ed94fae4c0bd138ee6906d87a85bd518264114896318c738e9c53ae1bf3`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l theta =>
  And (Filter.Tendsto theta l (nhds 0))
    (Filter.Eventually (fun t => And (Real.instLE.le 0 (theta t)) (Real.instLT.lt (theta t) 1)) l)
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `4be40f532556d3e77ff183d73f58ca53c39906eff20cfa2a95d74371577bb95c`

Type:

```lean
{m k : Nat} → LocalDef038 m k → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigmaMin => instHDiv.hDiv (LocalDef045 A) sigmaMin
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ea659dd0af1e90317a62571898bde6fc8ded022ac6934bf0f96c8e9243b11c08`

Type:

```lean
{m k q : Nat} → LocalDef038 m k → LocalDef038 k q → LocalDef038 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5e9563ecebb7f14ef3dfee0df9571dc5b992f9e32c9c0c19c6b34001b872d8e1`

Type:

```lean
{m k : Nat} → LocalDef038 m k → LocalDef042 k → LocalDef042 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7eeb372ed49009a9fbaa619f7d7edd369b54e614c91e79ae1a32ede22433dc11`

Type:

```lean
{k : Nat} → Real → LocalDef042 (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {k} beta i => ite (Eq i.val 0) beta 0
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `26222588e9ab394aa206f7d4ca98e516b1b333815c6d509644d3f2240ed3816f`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (basis : (k : Nat) → ι → LocalDef038 n k) →
      (∀ (k : Nat), instLENat.le k n → ∀ (t : ι), LocalDef077 (basis k t)) →
        (∀ (k : Nat) (t : ι) (i : Fin n) (j : Fin k),
            instLTNat.lt k n → Eq (basis k t i j) (basis (instHAdd.hAdd k 1) t i j.castSucc)) →
          LocalDef066 n ι
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `84de5f440851ab2c3f7c3f00b48f7e6daa85ef2eb14e213077a5d2a91ee34c06`

Type:

```lean
{m k : Nat} → LocalDef038 m k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Function.Injective (LocalDef074 A)
```

### D078: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D079: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D080: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D081: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D082: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

### D083: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D084: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

### D085: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D086: `HMul.hMul`

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

### D087: `LE.le`

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

### D088: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D089: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D090: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D091: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D092: `OfNat.ofNat`

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

### D093: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D094: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D095: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D096: `Real.instLE`

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

### D097: `Real.instMul`

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

### D098: `Real.instNatCast`

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

### D099: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D100: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D101: `instHMul`

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

### D102: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D103: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D104: `instOfNatAtLeastTwo`

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

### D105: `instOfNatNat`

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

### D106: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D107: `Fin.fintype`

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

### D108: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D109: `Finset.sum`

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

### D110: `Finset.univ`

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

### D111: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D112: `HPow.hPow`

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

### D113: `HSub.hSub`

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

### D114: `Matrix`

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

### D115: `Monoid.toNatPow`

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

### D116: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D117: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`

Type:

```lean
{ι : Type u_1} → {G : ι → Type u_4} → [(i : ι) → Sub (G i)] → Sub ((i : ι) → G i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {G} [(i : ι) → Sub (G i)] => { sub := fun f g i => instHSub.hSub (f i) (g i) }
```

### D118: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`

Type:

```lean
Add Real
```

Definition body (one-level semantic boundary):

```lean
{ add := Real.add✝ }
```

### D119: `Real.instAddCommMonoid`

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

### D120: `Real.instAddGroup`

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

### D121: `Real.instMonoid`

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

### D122: `Real.instSub`

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

### D123: `Real.lattice`

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

### D124: `abs`

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

### D125: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D126: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`

Type:

```lean
{α : Type u_1} → [Add α] → HAdd α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
```

### D127: `instHPow`

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

### D128: `instHSub`

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

### D129: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D130: `Matrix.frobeniusNormedAddCommGroup`

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

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Fintype m] [Fintype n] [NormedAddCommGroup α] => PiLp.normedAddCommGroupToPi 2 fun a => n → α
```

### D131: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D132: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6fa198061d1b8595a7b8b0ed74bd9e48f2c7a18aa01bf39d9c30be49c1d4741c`

Type:

```lean
{α : Type u} → [self : Max α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Max α] => self.1
```

### D133: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D134: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D135: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D136: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```

### D137: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `313f6558836157f8e8b4ea7be18fb6953bf9aefc4dcb68940ef5c4889e18a763`

Type:

```lean
Max Real
```

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```

### D138: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D139: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```

### D140: `Real.normedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9ff0d896c635e2a38531d689d24ee70cfffa41565354ce15f6ff59b51650bd93`

Type:

```lean
NormedAddCommGroup Real
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Real.norm, toAddCommGroup := Real.instAddCommGroup, toMetricSpace := Real.metricSpace, dist_eq := ⋯ }
```

### D141: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D142: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D143: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D144: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D145: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D146: `Ne`

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

### D147: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D148: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D149: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `9c0d1d56a04dd3ae3fce36b5fb3c2f4fe632c2bdaed84b5667c1a60a03491a3e`

Type:

```lean
PseudoMetricSpace Real
```

Definition body (one-level semantic boundary):

```lean
{ dist := fun x y => abs (instHSub.hSub x y), dist_self := Real.pseudoMetricSpace._proof_1, dist_comm := ⋯,
  dist_triangle := ⋯, edist_dist := Real.pseudoMetricSpace._proof_2, uniformity_dist := Real.pseudoMetricSpace._proof_3,
  cobounded_sets := Real.pseudoMetricSpace._proof_4 }
```

### D150: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D151: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```

### D152: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `38edd2256cd8f4f33f2c43ce7c36a1e1c7aded652580ec57a0adaf0ec346b64d`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive 0 → ((i : Fin n) → motive i.succ) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} zero succ i => Fin.induction zero (fun i x => succ i) i
```

### D153: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

Type:

```lean
DecidableEq Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D154: `ite`

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

### D155: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```
