# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} (semantics : LocalDef004) (family : LocalDef011 n semantics),
  LocalDef005 family →
    ∀ (appendix : LocalDef007 family),
      Exists fun k =>
        And (LocalDef020 (family.iteration k))
          (LocalDef001 (family.iteration k) →
            ∀ (MR MRinv : LocalDef006 n) (hMR : LocalDef019 MR MRinv),
              have q := appendix.rightQuantities k MR MRinv hMR;
              LocalDef017 semantics
                (LocalDef018 family.system.xExact (family.iteration k).xHat)
                (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor (LocalDef023 MR MRinv q))
                  (LocalDef016 (LocalDef022 family.system MRinv)
                    (LocalDef021 family.system MR))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (semantics : LocalDef004) (family : LocalDef011 n semantics)
  (mgs : @LocalDef005 n semantics family)
  (appendix : @LocalDef007 n semantics family),
  @Exists.{1} (LocalDef010 n) fun (k : LocalDef010 n) =>
    And
      (@LocalDef020 n (@LocalDef014 n semantics family) semantics
        (@LocalDef012 n semantics family) k
        (@LocalDef013 n semantics family k))
      (@LocalDef001 n (@LocalDef014 n semantics family) semantics
          (@LocalDef012 n semantics family) k
          (@LocalDef013 n semantics family k) →
        ∀ (MR MRinv : LocalDef006 n) (hMR : @LocalDef019 n MR MRinv),
          have q : @LocalDef009 n semantics family k MR MRinv :=
            @LocalDef008 n semantics family appendix k MR MRinv hMR;
          LocalDef017 semantics
            (@LocalDef018 n
              (@LocalDef015 n (@LocalDef014 n semantics family))
              (@LocalDef003 n (@LocalDef014 n semantics family)
                semantics (@LocalDef012 n semantics family) k
                (@LocalDef013 n semantics family k)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@LocalDef002 n
                  (@LocalDef014 n semantics family) semantics
                  (@LocalDef012 n semantics family) k
                  (@LocalDef013 n semantics family k))
                (@LocalDef023 n semantics family k MR MRinv q))
              (@LocalDef016 n
                (@LocalDef022 n (@LocalDef014 n semantics family)
                  MRinv)
                (@LocalDef021 n (@LocalDef014 n semantics family) MR))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f3da5a71d70cb6862c8500b208a4f5a9a8679a38a6b7d68318ea1e5a3fa54eb0`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Prop
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bd61c8f1e579e2bc426d5a08c59735f265c1098959fb615dd750676b8f5f9f9`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.1
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0f616cd1d9ce48e6eb27c83d2c4a4c2df84dd67d173d645b05f7301f1c36da83`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.25
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a20664f9def445da45faf4e94b9d57628f2c92d716d878ab43853aebfc279a4f`

Type:

```lean
Type
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b67e2d9f04acecbc78207a030a90d981c008234f8a4032f60100150823aba8a3`

Type:

```lean
{n : Nat} → {semantics : LocalDef004} → LocalDef011 n semantics → Prop
```

### D006: `LocalDef006`

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

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f878ea97002c4b2194fa2f73c12e0f0c4b72630967712bbf65fa43c50ff031fa`

Type:

```lean
{n : Nat} → {semantics : LocalDef004} → LocalDef011 n semantics → Type
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `79c3a6536a92b7a762cd0d7c31fc8459e7439753c676c7c63292a9e9c21108b1`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      LocalDef007 family →
        (k : LocalDef010 n) →
          (MR MRinv : LocalDef006 n) →
            LocalDef019 MR MRinv → LocalDef009 family k MR MRinv
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.1
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cdb178e57a28c2c5ee320fc7a43c465f7e981c77a239d21d1559d69277e7a564`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    LocalDef011 n semantics →
      LocalDef010 n → LocalDef006 n → LocalDef006 n → Type
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ba4d761a25f81cfb346c892740752ac617f111a2ec0eef599d417bd7f7d3e658`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Subtype fun k => And (instLTNat.lt 0 k) (instLENat.le k n)
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cc83d8798f9a47a79576057c89bdc261929f89427a25b80ab5445df3cd5f82a3`

Type:

```lean
Nat → LocalDef004 → Type
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `48b8971fe31959b7c84e4fa154d6726a70bcbe3b6bc2717c09056064d86842e0`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    (self : LocalDef011 n semantics) → LocalDef039 self.system
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `19b31c6eb7cb832d22efb7b1839ce0bc1843824506aa8009381c2a4b584f2da2`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    (self : LocalDef011 n semantics) →
      (k : LocalDef010 n) →
        LocalDef025 self.system semantics self.basisFamily k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f9b5cc522a99882317f849e0f893e587ce7572ee9af8b6bcf8da993caceb2a83`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    LocalDef011 n semantics → LocalDef041 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c060fd2e6cb0459f8835569f03cacb0ab0a92b86296d51c2585bb7100236edd6`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0caab4531a1846f654c1dd00b274cf19ace9e44cbf1773a4d95f56800e9ffd1`

Type:

```lean
{n : Nat} → LocalDef006 n → LocalDef006 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef047 Ainv) (LocalDef047 A)
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `35e87ffbddb5973e07dcc90dac89a3894e57974b204159105b2394786a93ec95`

Type:

```lean
LocalDef004 → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `de704d15118aaa066da7b9d608fb5f38683c608a436633eec639f8da74709601`

Type:

```lean
{n : Nat} → LocalDef046 n → LocalDef046 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (LocalDef056 (instHSub.hSub xHat x)) (LocalDef056 x)
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `77b8f45040142dc9a1f4c41dcad3fdb3c16d0ebc240adbaa5dac1c0ffabb00df`

Type:

```lean
{n : Nat} → LocalDef006 n → LocalDef006 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv =>
  And (∀ (x : LocalDef046 n), Eq (LocalDef050 Ainv (LocalDef050 A x)) x)
    (∀ (x : LocalDef046 n), Eq (LocalDef050 A (LocalDef050 Ainv x)) x)
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837ad167b07baa790538584ded0302c4a219440403d2a43dfcb0dfd365ded950`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  And (Real.instLE.le (instHDiv.hDiv 1 iteration.vHatSpectrum.sigmaMin) (4 / 3))
    (Real.instLE.le iteration.vHatSpectrum.sigmaMax (4 / 3))
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4cb66673cf665323a02c7eb0c2c6dc429e9bd04200a6e3229334df0c1b9d3f4b`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MR => LocalDef052 MR (LocalDef052 system.Ainv system.ML)
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c25f2199e58a4a4de5edf313b6a5d571be22105c7937a8116262d0e4917f09a1`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MRinv => LocalDef052 system.MLinv (LocalDef052 system.A MRinv)
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f2bb3e83a46a0dfed93d2a90100870ec073df2ef99f0582cc00b88a6ba6e4ca8`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        (MR MRinv : LocalDef006 n) → LocalDef009 family k MR MRinv → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  have run := family.iteration k;
  LocalDef051 (LocalDef053 MR MRinv q) (LocalDef054 MR MRinv q)
    (LocalDef055 family.system MR MRinv) run.epsilonC run.epsilonB run.ug run.epsilonX
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `255e05d9169cf68160ec75d831b67a6c01b7321d65c3244a232270c4e9a6a0f2`

Type:

```lean
∀ {n : Nat} {system : LocalDef041 n} {semantics : LocalDef004}
  {basisFamily : LocalDef039 system} {k : LocalDef010 n}
  {iteration : LocalDef025 system semantics basisFamily k},
  And (Real.instLE.le 0 iteration.epsilonC)
      (And (Real.instLE.le 0 iteration.epsilonB)
        (And (Real.instLE.le 0 iteration.ug) (Real.instLE.le 0 iteration.epsilonX))) →
    Real.instLE.le (LocalDef047 iteration.deltaC)
        (instHMul.hMul iteration.epsilonC
          (LocalDef047 (LocalDef084 system (basisFamily.basis k.val)))) →
      Real.instLE.le (LocalDef056 iteration.deltaB)
          (instHMul.hMul iteration.epsilonB (LocalDef056 (LocalDef083 system))) →
        LocalDef079 (instHAdd.hAdd iteration.computedC iteration.leastSquaresDeltaC)
            (instHAdd.hAdd iteration.computedB iteration.leastSquaresDeltaB) iteration.yHat →
          (∀ (j : Fin (instHAdd.hAdd k.val 1)),
              Real.instLE.le
                (LocalDef056
                  (LocalDef078
                    (LocalDef077 iteration.leastSquaresDeltaB iteration.leastSquaresDeltaC) j))
                (instHMul.hMul (instHMul.hMul iteration.dimensionFactor iteration.ug)
                  (LocalDef056
                    (LocalDef078 (LocalDef077 iteration.computedB iteration.computedC) j)))) →
            semantics.small
                (instHMul.hMul iteration.ug
                  (LocalDef081 iteration.computedC iteration.computedCSpectrum.sigmaMin)) →
              semantics.small
                  (instHMul.hMul (instHAdd.hAdd (instHAdd.hAdd iteration.epsilonC iteration.epsilonB) iteration.ug)
                    (LocalDef081 (LocalDef084 system (basisFamily.basis k.val))
                      iteration.exactCSpectrum.sigmaMin)) →
                Real.instLE.le (LocalDef056 iteration.deltaX)
                    (instHMul.hMul iteration.epsilonX
                      (LocalDef056 (LocalDef082 (basisFamily.basis k.val) iteration.yHat))) →
                  semantics.small iteration.epsilonX → LocalDef001 iteration
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f4879bef746a587dacfe91ab1a424bce7078d52c23f5781d3d8d85d64b2e912e`

Type:

```lean
{n : Nat} →
  (system : LocalDef041 n) →
    LocalDef004 →
      LocalDef039 system → LocalDef010 n → Type
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f8030bfc92643eceb346f953d6858c99670b9bac33003239e0d7a3301ae7fe23`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.4
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fbab99a9750c59d1a1e583743df520e7d44c5cc91bb8f953dd579b781c71de46`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.3
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `f7561b0267689d981281ecd75c09df38fe7833e3c39fc79174e4f25762311905`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.6
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4719f7a83a03368282078d24f181cee29a7a4a469c3c34d7ae10554be584afb9`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.5
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e8833827bd3a748534cb2317f9f1b570eb9df72748910ae72b2f34cd8d63c4a3`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef069 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.13
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6c6a21a70e9a127eec34be18a02b5156e7c6fd3553d869f8a57f86ef151cbc57`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          (self : LocalDef025 system semantics basisFamily k) →
            LocalDef070 self.vHat
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.28
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a249dfd13648ccda052f87210f4319154f5c284c54962efd48e215532eae0d6b`

Type:

```lean
(Real → Prop) → (secondOrder : Real → Prop) → secondOrder 0 → LocalDef004
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ddf671e3d58393ee511310b987314be908539f15467ae3cf73e66807e455755c`

Type:

```lean
LocalDef004 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1497d719068f8d8895ba60bd603e9d3c8c9016560b59759954bd461a979d201f`

Type:

```lean
∀ {n : Nat} {semantics : LocalDef004} {family : LocalDef011 n semantics},
  LocalDef020 (family.iteration ⟨1, ⋯⟩) →
    (∀ (k : Nat) (hkpos : instLTNat.lt 0 k) (hklt : instLTNat.lt k n),
        let current := ⟨k, ⋯⟩;
        let next := ⟨instHAdd.hAdd k 1, ⋯⟩;
        Not (LocalDef020 (family.iteration next)) →
          LocalDef080 (family.iteration current)) →
      LocalDef005 family
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `39b1024085d127c92aa430d39d98d3d00a99a5d1c44ea3bcaff897aa19328ba4`

Type:

```lean
{m k : Nat} → {A : LocalDef069 m k} → LocalDef070 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.2
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1013716a93aaa4244e940de911b2c7afefa568b957b54095b8426864b032c52c`

Type:

```lean
{m k : Nat} → {A : LocalDef069 m k} → LocalDef070 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.1
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0b99057edf7eba18d77a5822550ccb3122e66f1ce382e968b86ae4de5c4dcaf6`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      (rightQuantities :
          (k : LocalDef010 n) →
            (MR MRinv : LocalDef006 n) →
              LocalDef019 MR MRinv → LocalDef009 family k MR MRinv) →
        ((k : LocalDef010 n) →
            LocalDef020 (family.iteration k) →
              Or (Eq k.val n) (LocalDef080 (family.iteration k)) →
                LocalDef001 (family.iteration k) →
                  (MR MRinv : LocalDef006 n) →
                    (hMR : LocalDef019 MR MRinv) →
                      LocalDef071 family k MR MRinv (rightQuantities k MR MRinv hMR)) →
          LocalDef007 family
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `54b2fb2699fdda10cec4cd98026ef5d71f8ac18d3e70b55e827d0943bb0eb135`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        {MR MRinv : LocalDef006 n} →
          (mrzSpectrum :
              LocalDef070 (LocalDef052 MR (family.basisFamily.basis k.val))) →
            Real.instLT.lt 0 mrzSpectrum.sigmaMin →
              Real.instLT.lt 0
                  (LocalDef047
                    (LocalDef084 family.system (family.basisFamily.basis k.val))) →
                Real.instLT.lt 0 (LocalDef047 (LocalDef022 family.system MRinv)) →
                  Real.instLT.lt 0 (LocalDef016 MR MRinv) →
                    Real.instLT.lt 0
                        (LocalDef016 (LocalDef022 family.system MRinv)
                          (LocalDef021 family.system MR)) →
                      LocalDef009 family k MR MRinv
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cd7346b530ce5e5d6ba1c2e5416ee7c43d715dd345875961bcce92cbe5f41e14`

Type:

```lean
{n : Nat} → LocalDef041 n → Type
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f076c552518a53410edcb7f11b49475fb90d812b0212bc30431c42bf011d836`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    (system : LocalDef041 n) →
      (basisFamily : LocalDef039 system) →
        ((k : LocalDef010 n) →
            LocalDef025 system semantics basisFamily k) →
          LocalDef011 n semantics
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1fc353b1b432c0c1ef430f4cf2ff9afcfbed92f49cf465d778ddda0a635dd4d`

Type:

```lean
Nat → Type
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4bfdf1aea21b236835dd2c7582c4c22271b794da188a0ba1ccc5a694afff4be4`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5af7fc516b339d9009da5411f78f824a75063e508c6084b47f8ef7e44f62db8e`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `49bf2034c91342a98820db7017c34f0a2e9d1c3aaff5c66811d036bd3b1a1dcf`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ef0cd4e713f0114adf6c09b9205814f09e9a4779fd1ba97cdfa6d00458ff172c`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D046: `LocalDef046`

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

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1d77e739886fafe42f3444123b92bfd0ee9c522738b34d29764b9a10cb431f73`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e36ed6bfde9948e287453e8e216377bb07ab71b2d92789cf0f62d8ac7d27adbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `a53f13b94d3dbfd1b78203ce451bfa60bbd01b058daa3f65ff6c7d30ec55b8bd`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1ae9d14b7b4a526e86a7616a8ca6e9f01f9c771fcb8636b83a7aee0f1c7547c1`

Type:

```lean
{n : Nat} → LocalDef006 n → LocalDef046 n → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D051: `LocalDef051`

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

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2b8444b51bdd6b2f43ba4d5ab8376e63a1788f241ad49a66ee55d945464e1769`

Type:

```lean
{n k : Nat} → LocalDef006 n → LocalDef069 n k → LocalDef069 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `94ad6765fd2d1d76a7cf6f5e694fe696559cc294ae4aa2092584da7318d86f0e`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        (MR MRinv : LocalDef006 n) → LocalDef009 family k MR MRinv → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  instHMul.hMul (instHDiv.hDiv (LocalDef016 MR MRinv) q.mrzSpectrum.sigmaMin)
    (instHDiv.hDiv
      (LocalDef047 (LocalDef084 family.system (family.basisFamily.basis k.val)))
      (LocalDef047 (LocalDef022 family.system MRinv)))
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc6616164dde51b36dde0851bbe04442ce448feaf37560cbf0eb1c080b14ab56`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        (MR MRinv : LocalDef006 n) → LocalDef009 family k MR MRinv → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {semantics} {family} {k} MR MRinv q =>
  instHMul.hMul
    (Real.instMax.max 1
      (instHDiv.hDiv
        (instHDiv.hDiv
          (LocalDef047 (LocalDef084 family.system (family.basisFamily.basis k.val)))
          (LocalDef047 (LocalDef022 family.system MRinv)))
        q.mrzSpectrum.sigmaMin))
    (LocalDef016 MR MRinv)
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ef76c331af6971ea383a0e720b65e84633e2cc7d764624ac05082af69c1970f0`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef006 n → LocalDef006 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} system MR MRinv =>
  instHDiv.hDiv 1
    (LocalDef016 (LocalDef022 system MRinv)
      (LocalDef021 system MR))
```

### D056: `LocalDef056`

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
fun {n} x => (LocalDef085 x).sqrt
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0a36228ab177e3d96350f260b42b0b39cdbb2e3af19df1b61a4bdbe4767eb7c1`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.10
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `50a6535dd8ce1360428870bf95756a470737cd826b008cdbfad61b0808d02dee`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef069 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.7
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7824e63acaf19271f33d66772ca09d12cc7c9a38fa97405a605ee999bc4894e9`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          (self : LocalDef025 system semantics basisFamily k) →
            LocalDef070 self.computedC
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.23
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `737380e55e6f4d002c09906b6bcf025c9bda8e34cbadd9e15e1eacd15618ad5b`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.11
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `8b975d7f99cb27792acfddfe57d6c62419fd06a5e22f149738ab976b8c92053c`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef069 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.8
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c769c6055e58ce13a82154d73aaa12e36f093be38b8a1ef2590884646050568e`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.26
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `68907e28bc6082835e07880ef0723e3331dc590838e9ae56902d97687d8e0975`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k →
            LocalDef070 (LocalDef084 system (basisFamily.basis k.val))
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.24
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `09771da30686fc5e2cf381c4665caae33df2500d4d8fef9e37d1cf8a4130281b`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.20
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1474e23e024f85a3713cc0794a6573e2e4071d9d614f92fe14145947ab293054`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef069 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.21
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7878f8fc84c9629c27889bbc10be4df2f10323a0af9ee7131d71f631b0264ce2`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          (dimensionFactor : Real) →
            Real.instLE.le 1 dimensionFactor →
              Real →
                Real →
                  Real →
                    Real →
                      (computedC deltaC : LocalDef069 n k.val) →
                        Eq computedC
                            (instHAdd.hAdd (LocalDef084 system (basisFamily.basis k.val)) deltaC) →
                          (computedB deltaB : LocalDef046 n) →
                            Eq computedB (instHAdd.hAdd (LocalDef083 system) deltaB) →
                              (vHat : LocalDef069 n k.val) →
                                (vHatNext : LocalDef069 n (instHAdd.hAdd k.val 1)) →
                                  (beta : Real) →
                                    (hessenberg : LocalDef069 (instHAdd.hAdd k.val 1) k.val) →
                                      LocalDef090 hessenberg →
                                        Eq (LocalDef077 computedB computedC)
                                            (LocalDef092 vHatNext
                                              (LocalDef077 (LocalDef093 beta)
                                                hessenberg)) →
                                          (∀ (i : Fin n) (j : Fin k.val), Eq (vHat i j) (vHatNext i j.castSucc)) →
                                            LocalDef046 n →
                                              LocalDef069 n k.val →
                                                (yHat : LocalDef046 k.val) →
                                                  LocalDef070 computedC →
                                                    LocalDef070
                                                        (LocalDef084 system (basisFamily.basis k.val)) →
                                                      (xHat deltaX : LocalDef046 n) →
                                                        Eq xHat
                                                            (instHAdd.hAdd
                                                              (LocalDef082 (basisFamily.basis k.val) yHat)
                                                              deltaX) →
                                                          LocalDef070 vHat →
                                                            LocalDef025 system semantics
                                                              basisFamily k
```

### D067: `LocalDef067`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `17f32ecc0179dc60da4f31e7911e5c48e15e77ecc3d4689d7406db80def04525`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → LocalDef046 k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.22
```

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1bc30297c5d6628f7a45cd5221fd0209542b9615afa5f93728f12b0e31dc32b5`

Type:

```lean
LocalDef004 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `439dd553c0545a1da7e92aa2fe36a24aa581a6f27bc01f3f2b81504fea271a29`

Type:

```lean
Nat → Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun m k => Matrix (Fin m) (Fin k) Real
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Type
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `65eed1fd067dfb3e5a580791ed563e989356533e3bad89d99fd5a0ade6de3581`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    (family : LocalDef011 n semantics) →
      (k : LocalDef010 n) →
        (MR MRinv : LocalDef006 n) → LocalDef009 family k MR MRinv → Type
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4eb7527f6531dcb13870aa8043a1b097765583fdd88a79a19aa96217957c326c`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        {MR MRinv : LocalDef006 n} →
          LocalDef009 family k MR MRinv →
            LocalDef070 (LocalDef052 MR (family.basisFamily.basis k.val))
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family k MR MRinv self => self.1
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e068250f38486d591a2adfb1d7f2c918bc70608277fca9f7321223a7e5e37cbb`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    LocalDef039 system → (k : Nat) → LocalDef069 n k
```

Definition body (one-level semantic boundary):

```lean
fun n system self => self.1
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `436dbb701a39337ce5332902d90e6973e9b3a19d7776ff8eb60c5b47e5d23e93`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    (basis : (k : Nat) → LocalDef069 n k) →
      (∀ (k : Nat), instLTNat.lt 0 k → instLENat.le k n → LocalDef089 (basis k)) →
        (∀ (k : Nat),
            instLTNat.lt k n → ∀ (i : Fin n) (j : Fin k), Eq (basis k i j) (basis (instHAdd.hAdd k 1) i j.castSucc)) →
          LocalDef039 system
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7bcc8692a7674f34e3a15ff70ef2f751cd9c1fac7daae1fce18d92dbba9eb545`

Type:

```lean
∀ {n : Nat} (self : LocalDef041 n), instLTNat.lt 0 n
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b6ce3331a8ec6712c83ccceaf2dca3a6a89ee6e003288845219a21bd32c3a9a7`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv ML MLinv : LocalDef006 n) →
      (b xExact : LocalDef046 n) →
        LocalDef019 A Ainv →
          LocalDef019 ML MLinv →
            Ne b 0 → Eq (LocalDef050 A xExact) b → LocalDef041 n
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2fe0e06752730d60394b59adb4b76c6f22ea6681023a70406cbdcfc4ba900101`

Type:

```lean
{n k : Nat} → LocalDef046 n → LocalDef069 n k → LocalDef069 n (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b C i i_1 => Fin.cases (b i) (fun j => C i j) i_1
```

### D078: `LocalDef078`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d1c96c67d25102fa9368afc8215a13cc0626a5b92b4ea3b4e4f9c82429d0c977`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Fin k → LocalDef046 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A j i => A i j
```

### D079: `LocalDef079`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3007f611ab5087af1f0566bf60dfd75fc71f78dad5e293cff7cd63de4c42ed91`

Type:

```lean
{m k : Nat} → LocalDef069 m k → LocalDef046 m → LocalDef046 k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : LocalDef046 k),
    Real.instLE.le (LocalDef056 (instHSub.hSub b (LocalDef082 A y)))
      (LocalDef056 (instHSub.hSub b (LocalDef082 A z)))
```

### D080: `LocalDef080`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `bebe1d1e8d8d001aa18eb0792f2f6a1ee4a0fc6ffe41d08bf7c18d43bb054680`

Type:

```lean
{n : Nat} →
  {system : LocalDef041 n} →
    {semantics : LocalDef004} →
      {basisFamily : LocalDef039 system} →
        {k : LocalDef010 n} →
          LocalDef025 system semantics basisFamily k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  ∀ (phi : Real),
    Real.instLT.lt 0 phi →
      LocalDef091
        (LocalDef077 (fun i => instHMul.hMul (LocalDef083 system i) phi)
          (LocalDef084 system (basisFamily.basis k.val)))
        (instHMul.hMul (instHMul.hMul iteration.dimensionFactor (instHAdd.hAdd iteration.ug iteration.epsilonC))
          (LocalDef047
            (LocalDef077 (fun i => instHMul.hMul (LocalDef083 system i) phi)
              (LocalDef084 system (basisFamily.basis k.val)))))
```

### D081: `LocalDef081`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4be40f532556d3e77ff183d73f58ca53c39906eff20cfa2a95d74371577bb95c`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A sigmaMin => instHDiv.hDiv (LocalDef047 A) sigmaMin
```

### D082: `LocalDef082`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5e9563ecebb7f14ef3dfee0df9571dc5b992f9e32c9c0c19c6b34001b872d8e1`

Type:

```lean
{m k : Nat} → LocalDef069 m k → LocalDef046 k → LocalDef046 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D083: `LocalDef083`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4319e900a6bd10e9333ccb65413a9942cdbde8a752183b6e91ddff40f73fa205`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => LocalDef050 system.MLinv system.b
```

### D084: `LocalDef084`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `76bb6b06369be7ce2a16c093984eddc2dcc6362f2a005d765bda96800c51fcdd`

Type:

```lean
{n k : Nat} → LocalDef041 n → LocalDef069 n k → LocalDef069 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} system Z => LocalDef052 system.MLinv (LocalDef052 system.A Z)
```

### D085: `LocalDef085`

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

### D086: `LocalDef086`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `785b5c97bf75f07f40320aa93a7623aeb13039753f9b0be30629411ab231dca4`

Type:

```lean
{m k : Nat} →
  {A : LocalDef069 m k} →
    (sigmaMin sigmaMax : Real) →
      Real.instLE.le 0 sigmaMin →
        Real.instLE.le 0 sigmaMax →
          (∀ (x : LocalDef046 k),
              Real.instLE.le (instHMul.hMul sigmaMin (LocalDef056 x))
                (LocalDef056 (LocalDef082 A x))) →
            (∀ (x : LocalDef046 k),
                Real.instLE.le (LocalDef056 (LocalDef082 A x))
                  (instHMul.hMul sigmaMax (LocalDef056 x))) →
              (instLTNat.lt 0 k →
                  Exists fun x =>
                    And (Eq (LocalDef056 x) 1)
                      (Eq (LocalDef056 (LocalDef082 A x)) sigmaMin)) →
                (instLTNat.lt 0 k →
                    Exists fun x =>
                      And (Eq (LocalDef056 x) 1)
                        (Eq (LocalDef056 (LocalDef082 A x)) sigmaMax)) →
                  LocalDef070 A
```

### D087: `LocalDef087`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `622a39b4a5db3cb07f08c52b8caccba0945c736ad923945fcec0d054401588b8`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef004} →
    {family : LocalDef011 n semantics} →
      {k : LocalDef010 n} →
        {MR MRinv : LocalDef006 n} →
          {q : LocalDef009 family k MR MRinv} →
            (computationContribution rhsContribution gmresContribution solutionContribution remainder :
                LocalDef046 n) →
              Eq (instHSub.hSub (family.iteration k).xHat family.system.xExact)
                  (instHAdd.hAdd
                    (instHAdd.hAdd
                      (instHAdd.hAdd (instHAdd.hAdd computationContribution rhsContribution) gmresContribution)
                      solutionContribution)
                    remainder) →
                semantics.secondOrder
                    (instHDiv.hDiv (LocalDef056 remainder) (LocalDef056 family.system.xExact)) →
                  Real.instLE.le
                      (instHDiv.hDiv (LocalDef056 computationContribution)
                        (LocalDef056 family.system.xExact))
                      (instHMul.hMul
                        (instHMul.hMul (family.iteration k).dimensionFactor
                          (LocalDef016 (LocalDef022 family.system MRinv)
                            (LocalDef021 family.system MR)))
                        (instHMul.hMul (LocalDef053 MR MRinv q)
                          (LocalDef094 (LocalDef047 (family.iteration k).deltaC)
                            (LocalDef047
                              (LocalDef084 family.system (family.basisFamily.basis k.val)))))) →
                    Real.instLE.le
                        (instHDiv.hDiv (LocalDef056 rhsContribution)
                          (LocalDef056 family.system.xExact))
                        (instHMul.hMul
                          (instHMul.hMul (family.iteration k).dimensionFactor
                            (LocalDef016 (LocalDef022 family.system MRinv)
                              (LocalDef021 family.system MR)))
                          (instHMul.hMul (LocalDef054 MR MRinv q)
                            (LocalDef094 (LocalDef056 (family.iteration k).deltaB)
                              (LocalDef056 (LocalDef083 family.system))))) →
                      Real.instLE.le
                          (instHDiv.hDiv (LocalDef056 gmresContribution)
                            (LocalDef056 family.system.xExact))
                          (instHMul.hMul
                            (instHMul.hMul (family.iteration k).dimensionFactor
                              (LocalDef016 (LocalDef022 family.system MRinv)
                                (LocalDef021 family.system MR)))
                            (instHMul.hMul (LocalDef054 MR MRinv q) (family.iteration k).ug)) →
                        Real.instLE.le
                            (instHDiv.hDiv (LocalDef056 solutionContribution)
                              (LocalDef056 family.system.xExact))
                            (instHMul.hMul
                              (LocalDef016 (LocalDef022 family.system MRinv)
                                (LocalDef021 family.system MR))
                              (instHMul.hMul (LocalDef055 family.system MR MRinv)
                                (LocalDef094
                                  (LocalDef056 (family.iteration k).deltaX)
                                  (LocalDef056
                                    (LocalDef082 (family.basisFamily.basis k.val)
                                      (family.iteration k).yHat))))) →
                          LocalDef071 family k MR MRinv q
```

### D088: `LocalDef088`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `f2a130fd36774a5574504267aaab72b46108b1c686d97df059b452f44cf66199`

Type:

```lean
{n : Nat} → LocalDef041 n → LocalDef046 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D089: `LocalDef089`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `84de5f440851ab2c3f7c3f00b48f7e6daa85ef2eb14e213077a5d2a91ee34c06`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Function.Injective (LocalDef082 A)
```

### D090: `LocalDef090`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `40e9dda219091e0a8274024ac3a6a6ec9b0f2c87f705a5d5c83ed03835619d3e`

Type:

```lean
{k : Nat} → LocalDef069 (instHAdd.hAdd k 1) k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {k} H => ∀ (i : Fin (instHAdd.hAdd k 1)) (j : Fin k), instLTNat.lt (instHAdd.hAdd j.val 1) i.val → Eq (H i j) 0
```

### D091: `LocalDef091`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `16466bbe231c4c118f1c0663cc1bb4687beb871eeebede56fe75c840088e6a50`

Type:

```lean
{m k : Nat} → LocalDef069 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A threshold =>
  Exists fun x =>
    And (Eq (LocalDef056 x) 1)
      (Real.instLT.lt (LocalDef056 (LocalDef082 A x)) threshold)
```

### D092: `LocalDef092`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ea659dd0af1e90317a62571898bde6fc8ded022ac6934bf0f96c8e9243b11c08`

Type:

```lean
{m k q : Nat} → LocalDef069 m k → LocalDef069 k q → LocalDef069 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D093: `LocalDef093`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7eeb372ed49009a9fbaa619f7d7edd369b54e614c91e79ae1a32ede22433dc11`

Type:

```lean
{k : Nat} → Real → LocalDef046 (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {k} beta i => ite (Eq i.val 0) beta 0
```

### D094: `LocalDef094`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e90ca3fde1791e8677db326faa8ac6b95895f175f7ab0b517236d9c16c6a1872`

Type:

```lean
Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun actual reference => ite (Eq reference 0) 0 (instHDiv.hDiv actual reference)
```

### D095: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

### D096: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D097: `HMul.hMul`

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

### D098: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D099: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D100: `Real.instMul`

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

### D102: `DivInvMonoid.toDiv`

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

### D103: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D104: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D105: `HAdd.hAdd`

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

### D106: `HDiv.hDiv`

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

### D107: `HSub.hSub`

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

### D108: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D109: `LT.lt`

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

### D110: `Matrix`

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

### D111: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D112: `One.toOfNat1`

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

### D113: `Pi.instSub`

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

### D114: `Real.instAdd`

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

### D115: `Real.instAddGroup`

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

### D116: `Real.instDivInvMonoid`

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

### D117: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D118: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D119: `Real.instOne`

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

### D120: `Real.instSub`

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

### D121: `Real.lattice`

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

### D122: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

### D123: `Subtype.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `69c61ab82498e5563eaf5f0313ea7f2164c284c3dc742024a30332372a46663d`

Type:

```lean
{α : Sort u} → {p : α → Prop} → Subtype p → α
```

Definition body (one-level semantic boundary):

```lean
fun α p self => self.1
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

### D125: `instHAdd`

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

### D126: `instHDiv`

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

### D127: `instHSub`

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

### D128: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D129: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D130: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `37355febc51d6fa8ff12fc8e7b429771db340390d46411d7608c566bdffd358d`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D131: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D132: `And.intro`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `232593c5c388d46173a03223cb6b55ff2a132de1d4dfae47c09b5ba49b1e4f83`

Type:

```lean
∀ {a b : Prop}, a → b → And a b
```

### D133: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D134: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D135: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D136: `Iff.mpr`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `abcae2cc4e99f1dc596c9080dca30ec894770912ebfc2b6ad2910b661baa68ed`

Type:

```lean
∀ {a b : Prop}, Iff a b → b → a
```

### D137: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D138: `Matrix.frobeniusNormedAddCommGroup`

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

### D139: `Max.max`

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

### D140: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

### D141: `Nat.le_of_lt`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `ff212a95500662f3fc7ee2c8e4193476d63a9914c09b07b917a87fc24a0c94ad`

Type:

```lean
∀ {n m : Nat}, instLTNat.lt n m → instLENat.le n m
```

### D142: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

### D143: `Nat.succ_le_iff`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `d5b55de88f550a3dcb1879518a5688ec9a4d8ca18878d7d0d8df30740c0ae92b`

Type:

```lean
∀ {m n : Nat}, Iff (instLENat.le m.succ n) (instLTNat.lt m n)
```

### D144: `Nat.succ_pos`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `0e7e3546875c3c758b7e9f771f5146afbe4374a7356e205021f87835237aeaa7`

Type:

```lean
∀ (n : Nat), instLTNat.lt 0 n.succ
```

### D145: `Nat.zero_lt_one`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7af00b6e71ddbd58776e8dc3a2c9845b1099ebd1b1c29b6b3d4e09c80c3bc1a7`

Type:

```lean
instLTNat.lt 0 1
```

### D146: `Norm.norm`

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

### D147: `NormedAddCommGroup.toNorm`

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

### D148: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D149: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

### D150: `Pi.instAdd`

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

### D151: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D152: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`

Type:

```lean
LT Real
```

Definition body (one-level semantic boundary):

```lean
{ lt := Real.lt✝ }
```

### D153: `Real.instMax`

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

### D154: `Real.instZero`

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

### D155: `Real.normedAddCommGroup`

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

### D156: `Real.sqrt`

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

### D157: `Subtype.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `488ac61b6d3c07fb9a2f54a03a39e6001a4c7cedfd07515f0f9865e7fef9ef51`

Type:

```lean
{α : Sort u} → {p : α → Prop} → (val : α) → p val → Subtype p
```

### D158: `Zero.toOfNat0`

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

### D159: `instAddNat`

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

### D160: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D161: `Fin.castSucc`

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

### D162: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D163: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D164: `Ne`

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

### D165: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `eb5c70d9b813d7099537e8db11f59a65a3f5ad951da7314a1aa554471a122049`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Zero (M i)] → Zero ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Zero (M i)] => { zero := fun x => 0 }
```

### D166: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D167: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D168: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D169: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d947e6344cfd1327deca4c84f2eba89bf752b6e852fc0c680177dfaae4418776`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ ⦃a₁ a₂ : α⦄, Eq (f a₁) (f a₂) → Eq a₁ a₂
```

### D170: `instDecidableEqNat`

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

### D171: `ite`

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

### D172: `Real.decidableEq`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `58b21b2d8719c9bf9f6e23c4dbf1284069f5ce6f35c64915e45284792e8a5bcf`

Type:

```lean
(a b : Real) → Decidable (Eq a b)
```

Definition body (one-level semantic boundary):

```lean
fun a b => inferInstance
```
