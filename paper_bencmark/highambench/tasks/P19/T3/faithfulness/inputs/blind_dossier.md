# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} (semantics : LocalDef003) (choice : LocalDef025),
  And
    (∀ (right : LocalDef020 n semantics),
      LocalDef004 right.family →
        ∀ (appendix : LocalDef018 choice right),
          (∀ (k : LocalDef026 n),
              LocalDef034 (right.family.iteration k) →
                Or (Eq k.val n) (LocalDef035 (right.family.iteration k)) →
                  LocalDef019 choice (right.iteration k)) →
            Exists fun k =>
              And (LocalDef034 (right.family.iteration k))
                (LocalDef032 semantics
                  (LocalDef033 right.family.system.xExact (right.family.iteration k).xHat)
                  (instHMul.hMul (right.family.iteration k).dimensionFactor
                    (LocalDef037 choice right.preconditioner
                      (right.iteration k).core.ug (right.iteration k).core.um (right.iteration k).core.ua
                      (right.iteration k).core.etaR (right.iteration k).core.rhoAR))))
    (And
      (∀ (flexible : LocalDef013 n semantics),
        LocalDef004 flexible.family →
          ∀ (appendix : LocalDef011 choice flexible),
            (∀ (k : LocalDef026 n),
                LocalDef034 (flexible.family.iteration k) →
                  Or (Eq k.val n) (LocalDef035 (flexible.family.iteration k)) →
                    LocalDef012 choice (flexible.iteration k)) →
              Exists fun k =>
                And (LocalDef034 (flexible.family.iteration k))
                  (LocalDef032 semantics
                    (LocalDef033 flexible.family.system.xExact (flexible.family.iteration k).xHat)
                    (instHMul.hMul (flexible.family.iteration k).dimensionFactor
                      (LocalDef036 choice flexible.preconditioner
                        (flexible.iteration k).core.ug (flexible.iteration k).core.ua
                        (flexible.iteration k).core.rhoAR))))
      (∀ (family : LocalDef027 n semantics)
        (preconditioner : LocalDef010 family) (ug um ua etaR rhoAR : Real),
        Eq (LocalDef037 choice preconditioner ug um ua etaR rhoAR)
          (instHAdd.hAdd (LocalDef036 choice preconditioner ug ua rhoAR)
            (instHMul.hMul (instHMul.hMul um etaR)
              (LocalDef038 choice preconditioner)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (semantics : LocalDef003) (choice : LocalDef025),
  And
    (∀ (right : LocalDef020 n semantics)
      (mgs : @LocalDef004 n semantics (@LocalDef021 n semantics right))
      (appendix : @LocalDef018 choice n semantics right)
      (applicability :
        ∀ (k : LocalDef026 n),
          @LocalDef034 n
              (@LocalDef030 n semantics
                (@LocalDef021 n semantics right))
              semantics
              (@LocalDef028 n semantics
                (@LocalDef021 n semantics right))
              k
              (@LocalDef029 n semantics
                (@LocalDef021 n semantics right) k) →
            Or
                (@Eq.{1} Nat
                  (@Subtype.val.{1} Nat
                    (fun (k : Nat) =>
                      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (@LE.le.{0} Nat instLENat k n))
                    k)
                  n)
                (@LocalDef035 n
                  (@LocalDef030 n semantics
                    (@LocalDef021 n semantics right))
                  semantics
                  (@LocalDef028 n semantics
                    (@LocalDef021 n semantics right))
                  k
                  (@LocalDef029 n semantics
                    (@LocalDef021 n semantics right) k)) →
              @LocalDef019 choice n semantics
                (@LocalDef021 n semantics right)
                (@LocalDef023 n semantics right) k
                (@LocalDef022 n semantics right k)),
      @Exists.{1} (LocalDef026 n) fun (k : LocalDef026 n) =>
        And
          (@LocalDef034 n
            (@LocalDef030 n semantics
              (@LocalDef021 n semantics right))
            semantics
            (@LocalDef028 n semantics
              (@LocalDef021 n semantics right))
            k
            (@LocalDef029 n semantics
              (@LocalDef021 n semantics right) k))
          (LocalDef032 semantics
            (@LocalDef033 n
              (@LocalDef031 n
                (@LocalDef030 n semantics
                  (@LocalDef021 n semantics right)))
              (@LocalDef002 n
                (@LocalDef030 n semantics
                  (@LocalDef021 n semantics right))
                semantics
                (@LocalDef028 n semantics
                  (@LocalDef021 n semantics right))
                k
                (@LocalDef029 n semantics
                  (@LocalDef021 n semantics right) k)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@LocalDef001 n
                (@LocalDef030 n semantics
                  (@LocalDef021 n semantics right))
                semantics
                (@LocalDef028 n semantics
                  (@LocalDef021 n semantics right))
                k
                (@LocalDef029 n semantics
                  (@LocalDef021 n semantics right) k))
              (@LocalDef037 choice n semantics
                (@LocalDef021 n semantics right)
                (@LocalDef023 n semantics right)
                (@LocalDef008 n semantics
                  (@LocalDef021 n semantics right)
                  (@LocalDef023 n semantics right) k
                  (@LocalDef024 n semantics
                    (@LocalDef021 n semantics right)
                    (@LocalDef023 n semantics right) k
                    (@LocalDef022 n semantics right k)))
                (@LocalDef009 n semantics
                  (@LocalDef021 n semantics right)
                  (@LocalDef023 n semantics right) k
                  (@LocalDef024 n semantics
                    (@LocalDef021 n semantics right)
                    (@LocalDef023 n semantics right) k
                    (@LocalDef022 n semantics right k)))
                (@LocalDef007 n semantics
                  (@LocalDef021 n semantics right)
                  (@LocalDef023 n semantics right) k
                  (@LocalDef024 n semantics
                    (@LocalDef021 n semantics right)
                    (@LocalDef023 n semantics right) k
                    (@LocalDef022 n semantics right k)))
                (@LocalDef005 n semantics
                  (@LocalDef021 n semantics right)
                  (@LocalDef023 n semantics right) k
                  (@LocalDef024 n semantics
                    (@LocalDef021 n semantics right)
                    (@LocalDef023 n semantics right) k
                    (@LocalDef022 n semantics right k)))
                (@LocalDef006 n semantics
                  (@LocalDef021 n semantics right)
                  (@LocalDef023 n semantics right) k
                  (@LocalDef024 n semantics
                    (@LocalDef021 n semantics right)
                    (@LocalDef023 n semantics right) k
                    (@LocalDef022 n semantics right k)))))))
    (And
      (∀ (flexible : LocalDef013 n semantics)
        (mgs :
          @LocalDef004 n semantics
            (@LocalDef014 n semantics flexible))
        (appendix : @LocalDef011 choice n semantics flexible)
        (applicability :
          ∀ (k : LocalDef026 n),
            @LocalDef034 n
                (@LocalDef030 n semantics
                  (@LocalDef014 n semantics flexible))
                semantics
                (@LocalDef028 n semantics
                  (@LocalDef014 n semantics flexible))
                k
                (@LocalDef029 n semantics
                  (@LocalDef014 n semantics flexible) k) →
              Or
                  (@Eq.{1} Nat
                    (@Subtype.val.{1} Nat
                      (fun (k : Nat) =>
                        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                          (@LE.le.{0} Nat instLENat k n))
                      k)
                    n)
                  (@LocalDef035 n
                    (@LocalDef030 n semantics
                      (@LocalDef014 n semantics flexible))
                    semantics
                    (@LocalDef028 n semantics
                      (@LocalDef014 n semantics flexible))
                    k
                    (@LocalDef029 n semantics
                      (@LocalDef014 n semantics flexible) k)) →
                @LocalDef012 choice n semantics
                  (@LocalDef014 n semantics flexible)
                  (@LocalDef016 n semantics flexible) k
                  (@LocalDef015 n semantics flexible k)),
        @Exists.{1} (LocalDef026 n) fun (k : LocalDef026 n) =>
          And
            (@LocalDef034 n
              (@LocalDef030 n semantics
                (@LocalDef014 n semantics flexible))
              semantics
              (@LocalDef028 n semantics
                (@LocalDef014 n semantics flexible))
              k
              (@LocalDef029 n semantics
                (@LocalDef014 n semantics flexible) k))
            (LocalDef032 semantics
              (@LocalDef033 n
                (@LocalDef031 n
                  (@LocalDef030 n semantics
                    (@LocalDef014 n semantics flexible)))
                (@LocalDef002 n
                  (@LocalDef030 n semantics
                    (@LocalDef014 n semantics flexible))
                  semantics
                  (@LocalDef028 n semantics
                    (@LocalDef014 n semantics flexible))
                  k
                  (@LocalDef029 n semantics
                    (@LocalDef014 n semantics flexible) k)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@LocalDef001 n
                  (@LocalDef030 n semantics
                    (@LocalDef014 n semantics flexible))
                  semantics
                  (@LocalDef028 n semantics
                    (@LocalDef014 n semantics flexible))
                  k
                  (@LocalDef029 n semantics
                    (@LocalDef014 n semantics flexible) k))
                (@LocalDef036 choice n semantics
                  (@LocalDef014 n semantics flexible)
                  (@LocalDef016 n semantics flexible)
                  (@LocalDef008 n semantics
                    (@LocalDef014 n semantics flexible)
                    (@LocalDef016 n semantics flexible) k
                    (@LocalDef017 n semantics
                      (@LocalDef014 n semantics flexible)
                      (@LocalDef016 n semantics flexible) k
                      (@LocalDef015 n semantics flexible k)))
                  (@LocalDef007 n semantics
                    (@LocalDef014 n semantics flexible)
                    (@LocalDef016 n semantics flexible) k
                    (@LocalDef017 n semantics
                      (@LocalDef014 n semantics flexible)
                      (@LocalDef016 n semantics flexible) k
                      (@LocalDef015 n semantics flexible k)))
                  (@LocalDef006 n semantics
                    (@LocalDef014 n semantics flexible)
                    (@LocalDef016 n semantics flexible) k
                    (@LocalDef017 n semantics
                      (@LocalDef014 n semantics flexible)
                      (@LocalDef016 n semantics flexible) k
                      (@LocalDef015 n semantics flexible k)))))))
      (∀ (family : LocalDef027 n semantics)
        (preconditioner : @LocalDef010 n semantics family)
        (ug um ua etaR rhoAR : Real),
        @Eq.{1} Real
          (@LocalDef037 choice n semantics family preconditioner ug um ua etaR rhoAR)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@LocalDef036 choice n semantics family preconditioner ug ua rhoAR)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) um etaR)
              (@LocalDef038 choice n semantics family preconditioner)))))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8bd61c8f1e579e2bc426d5a08c59735f265c1098959fb615dd750676b8f5f9f9`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0f616cd1d9ce48e6eb27c83d2c4a4c2df84dd67d173d645b05f7301f1c36da83`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.25
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a20664f9def445da45faf4e94b9d57628f2c92d716d878ab43853aebfc279a4f`

Type:

```lean
Type
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b67e2d9f04acecbc78207a030a90d981c008234f8a4032f60100150823aba8a3`

Type:

```lean
{n : Nat} → {semantics : LocalDef003} → LocalDef027 n semantics → Prop
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `47cbf6557fe561ebcc11b2ad8138d2cad06a5472576e89df0c25ebac8ef3acc7`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.4
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5ef09099046905e7f89b56c7b82e67aca33f15eb3fe26814f1739d54a9095a6`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.5
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8d5598ea0fc18200212c77bf981efeff17b3c27faf56e2668f59f9fcc446beab`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.3
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `63e66824835046c6ada5feeb04d97ba1e14722f9603c523b70680071e0edeb7b`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `723d957713fb9b948ab2c8ab35a5d6e925676ed148fd8cc9a7bfbfabb30ad663`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f17c181eddba4babc040bf456a51f7a5f69f8e1086de922560b0f8450c333523`

Type:

```lean
{n : Nat} → {semantics : LocalDef003} → LocalDef027 n semantics → Type
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `d9cc418ff1028a4124ed7c3068c4aa6943c9cbb09b11534ae2656dc3721714e3`

Type:

```lean
LocalDef025 →
  {n : Nat} → {semantics : LocalDef003} → LocalDef013 n semantics → Type
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b088b3ad9a5dbc3d18d0ab445e99c4e27fe5796c6cf391a0d6f01541af0c619d`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        {preconditioner : LocalDef010 family} →
          {k : LocalDef026 n} →
            LocalDef056 family preconditioner k → Prop
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a98b45ef16ccad8799958db5b7f25acbf531bee95224288ef8b372f46f37f6b8`

Type:

```lean
Nat → LocalDef003 → Type
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `58cb6cc8f5fdc4bf773f32d161a5300e3e79d8c8d9f7039dface49bedee1e298`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    LocalDef013 n semantics → LocalDef027 n semantics
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
- Semantic SHA-256: `aa4985b27b46324f206f6c068dc073d9b9df2d0659d3cf9326b6b1b946852298`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef013 n semantics) →
      (k : LocalDef026 n) →
        LocalDef056 self.family self.preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `09d13f46802f29fe551c017f3df082e43ff5d3166886b9ce1a1dc24707738b20`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef013 n semantics) → LocalDef010 self.family
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `27a3180ca404d5342b624333ca0fcf379eee0d103cc4cda4fac240799e5fed44`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef056 family preconditioner k →
            LocalDef049 family preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `997f3e55531817475668d6b087dfce3587837fe6c2063db0295a6a1a536431c6`

Type:

```lean
LocalDef025 →
  {n : Nat} → {semantics : LocalDef003} → LocalDef020 n semantics → Type
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `c287fe1077604f3edf20e9207d23bd329281edb3a562cd23bfc003bb77580185`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        {preconditioner : LocalDef010 family} →
          {k : LocalDef026 n} → LocalDef060 family preconditioner k → Prop
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4167e6ef452a48ed9662303d633bbe76cdd69fd4e7ea64d4ff0ed76b13fcd642`

Type:

```lean
Nat → LocalDef003 → Type
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `30215e7975cb776aa7dd95938d4d39ea6fae480850b13dd0944ff9c48e059077`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    LocalDef020 n semantics → LocalDef027 n semantics
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ad047aa332a5e9a4cbb1389d7474e47a1a833569fdbf8fdb45cb42527a879890`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef020 n semantics) →
      (k : LocalDef026 n) → LocalDef060 self.family self.preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1bb04c0d8562112a011019f7c4302812716ad78cad5e42bc728ba28284934dfc`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef020 n semantics) → LocalDef010 self.family
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `21b32a833e5358eeb0920cd6801fb2d7358b31600462f005ceed16178ecc0939`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef060 family preconditioner k →
            LocalDef049 family preconditioner k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.1
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4a5fc3461154e3dc86d003a2aa51f5e386d2e947f4ca5ff258b33546a4650226`

Type:

```lean
Type
```

### D026: `LocalDef026`

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

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cc83d8798f9a47a79576057c89bdc261929f89427a25b80ab5445df3cd5f82a3`

Type:

```lean
Nat → LocalDef003 → Type
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `48b8971fe31959b7c84e4fa154d6726a70bcbe3b6bc2717c09056064d86842e0`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef027 n semantics) → LocalDef063 self.system
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.2
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `19b31c6eb7cb832d22efb7b1839ce0bc1843824506aa8009381c2a4b584f2da2`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (self : LocalDef027 n semantics) →
      (k : LocalDef026 n) →
        LocalDef039 self.system semantics self.basisFamily k
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.3
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f9b5cc522a99882317f849e0f893e587ce7572ee9af8b6bcf8da993caceb2a83`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    LocalDef027 n semantics → LocalDef066 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics self => self.1
```

### D031: `LocalDef031`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c060fd2e6cb0459f8835569f03cacb0ab0a92b86296d51c2585bb7100236edd6`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.7
```

### D032: `LocalDef032`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `35e87ffbddb5973e07dcc90dac89a3894e57974b204159105b2394786a93ec95`

Type:

```lean
LocalDef003 → Real → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D033: `LocalDef033`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `de704d15118aaa066da7b9d608fb5f38683c608a436633eec639f8da74709601`

Type:

```lean
{n : Nat} → LocalDef067 n → LocalDef067 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x xHat => instHDiv.hDiv (LocalDef078 (instHSub.hSub xHat x)) (LocalDef078 x)
```

### D034: `LocalDef034`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837ad167b07baa790538584ded0302c4a219440403d2a43dfcb0dfd365ded950`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  And (Real.instLE.le (instHDiv.hDiv 1 iteration.vHatSpectrum.sigmaMin) (4 / 3))
    (Real.instLE.le iteration.vHatSpectrum.sigmaMax (4 / 3))
```

### D035: `LocalDef035`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bebe1d1e8d8d001aa18eb0792f2f6a1ee4a0fc6ffe41d08bf7c18d43bb054680`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} {system} {semantics} {basisFamily} {k} iteration =>
  ∀ (phi : Real),
    Real.instLT.lt 0 phi →
      LocalDef072
        (LocalDef068 (fun i => instHMul.hMul (LocalDef073 system i) phi)
          (LocalDef074 system (basisFamily.basis k.val)))
        (instHMul.hMul (instHMul.hMul iteration.dimensionFactor (instHAdd.hAdd iteration.ug iteration.epsilonC))
          (LocalDef069
            (LocalDef068 (fun i => instHMul.hMul (LocalDef073 system i) phi)
              (LocalDef074 system (basisFamily.basis k.val)))))
```

### D036: `LocalDef036`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a2ce6acd788e00e7620e8063f4d3f8deb6c7382205d0c02ff36ebba5c4a3664d`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        LocalDef010 family → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug ua rhoAR =>
  instHAdd.hAdd
    (instHMul.hMul (instHMul.hMul ug (LocalDef076 choice preconditioner))
      (LocalDef038 choice preconditioner))
    (instHMul.hMul (instHMul.hMul ua (LocalDef077 choice family)) rhoAR)
```

### D037: `LocalDef037`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7b79ed05e7373af69a09c6ba9c4c34080bc6f953bbced1c2c89e8a1c29948b43`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        LocalDef010 family → Real → Real → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug um ua etaR rhoAR =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHMul.hMul (instHMul.hMul ug (LocalDef076 choice preconditioner))
        (LocalDef038 choice preconditioner))
      (instHMul.hMul (instHMul.hMul um etaR) (LocalDef038 choice preconditioner)))
    (instHMul.hMul (instHMul.hMul ua (LocalDef077 choice family)) rhoAR)
```

### D038: `LocalDef038`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e4133ea733ea352df5df33d675a4002acd0a62046b66db4dd5d146ea095bff82`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        LocalDef010 family → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner =>
  LocalDef075 choice preconditioner.MR preconditioner.MRinv
```

### D039: `LocalDef039`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f4879bef746a587dacfe91ab1a424bce7078d52c23f5781d3d8d85d64b2e912e`

Type:

```lean
{n : Nat} →
  (system : LocalDef066 n) →
    LocalDef003 →
      LocalDef063 system → LocalDef026 n → Type
```

### D040: `LocalDef040`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `fbab99a9750c59d1a1e583743df520e7d44c5cc91bb8f953dd579b781c71de46`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.3
```

### D041: `LocalDef041`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4719f7a83a03368282078d24f181cee29a7a4a469c3c34d7ae10554be584afb9`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.5
```

### D042: `LocalDef042`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e8833827bd3a748534cb2317f9f1b570eb9df72748910ae72b2f34cd8d63c4a3`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.13
```

### D043: `LocalDef043`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6c6a21a70e9a127eec34be18a02b5156e7c6fd3553d869f8a57f86ef151cbc57`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          (self : LocalDef039 system semantics basisFamily k) →
            LocalDef082 self.vHat
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.28
```

### D044: `LocalDef044`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `a249dfd13648ccda052f87210f4319154f5c284c54962efd48e215532eae0d6b`

Type:

```lean
(Real → Prop) → (secondOrder : Real → Prop) → secondOrder 0 → LocalDef003
```

### D045: `LocalDef045`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ddf671e3d58393ee511310b987314be908539f15467ae3cf73e66807e455755c`

Type:

```lean
LocalDef003 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D046: `LocalDef046`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `1497d719068f8d8895ba60bd603e9d3c8c9016560b59759954bd461a979d201f`

Type:

```lean
∀ {n : Nat} {semantics : LocalDef003} {family : LocalDef027 n semantics},
  LocalDef034 (family.iteration ⟨1, ⋯⟩) →
    (∀ (k : Nat) (hkpos : instLTNat.lt 0 k) (hklt : instLTNat.lt k n),
        let current := ⟨k, ⋯⟩;
        let next := ⟨instHAdd.hAdd k 1, ⋯⟩;
        Not (LocalDef034 (family.iteration next)) →
          LocalDef035 (family.iteration current)) →
      LocalDef004 family
```

### D047: `LocalDef047`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `39b1024085d127c92aa430d39d98d3d00a99a5d1c44ea3bcaff897aa19328ba4`

Type:

```lean
{m k : Nat} → {A : LocalDef081 m k} → LocalDef082 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.2
```

### D048: `LocalDef048`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1013716a93aaa4244e940de911b2c7afefa568b957b54095b8426864b032c52c`

Type:

```lean
{m k : Nat} → {A : LocalDef081 m k} → LocalDef082 A → Real
```

Definition body (one-level semantic boundary):

```lean
fun m k A self => self.1
```

### D049: `LocalDef049`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1af16d2cd1d267ddac77353673fc4d8b8e1d6d44a927b0c54e52a3f25a9c5f1`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (family : LocalDef027 n semantics) →
      LocalDef010 family → LocalDef026 n → Type
```

### D050: `LocalDef050`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `93922fa909bf0d374e24676a867543c8811c86c0647c04e53a44442909d17950`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      LocalDef010 family → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.1
```

### D051: `LocalDef051`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4989d7a9188a57ee86d1f70d2de3270ae514c0a21799f0fc3cb6c57548d67c73`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      LocalDef010 family → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family self => self.2
```

### D052: `LocalDef052`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `156e5be50a10502da40c3187d2166d6868740df4f6a4dde4a445176ea8a7b5a1`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      (MR MRinv : LocalDef080 n) →
        LocalDef104 MR MRinv →
          LocalDef104 (LocalDef108 family.system.A MRinv)
              (LocalDef108 MR family.system.Ainv) →
            Ne MR 1 →
              Eq family.system.ML 1 → Eq family.system.MLinv 1 → LocalDef010 family
```

### D053: `LocalDef053`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `78269f43236e9dfe8c665521211d36c0148823ae47c106abd084a025189da87d`

Type:

```lean
{choice : LocalDef025} →
  {n : Nat} →
    {semantics : LocalDef003} →
      {flexible : LocalDef013 n semantics} →
        ((k : LocalDef026 n) →
            LocalDef034 (flexible.family.iteration k) →
              Or (Eq k.val n) (LocalDef035 (flexible.family.iteration k)) →
                LocalDef012 choice (flexible.iteration k) →
                  LocalDef087 choice flexible k) →
          LocalDef011 choice flexible
```

### D054: `LocalDef054`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2c2a9c4116f616e9d400a20195748eade3a0b8e531efcec0e3b901bca268e8c6`

Type:

```lean
∀ {choice : LocalDef025} {n : Nat} {semantics : LocalDef003}
  {family : LocalDef027 n semantics}
  {preconditioner : LocalDef010 family} {k : LocalDef026 n}
  {iteration : LocalDef056 family preconditioner k},
  LocalDef086 choice iteration.core →
    (∀ (i : Fin n) (j : Fin k.val),
        Real.instLE.le (abs (iteration.solutionBasisDelta i j))
          (instHMul.hMul iteration.core.gmresMagnitude (abs (iteration.core.zHat i j)))) →
      LocalDef012 choice iteration
```

### D055: `LocalDef055`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `edebaabe72d1631e765a279660b7c46f44de870075a08afaaed29d85ea490984`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (family : LocalDef027 n semantics) →
      (preconditioner : LocalDef010 family) →
        ((k : LocalDef026 n) → LocalDef056 family preconditioner k) →
          LocalDef013 n semantics
```

### D056: `LocalDef056`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `5e9c08de7d5f874e9c5f183fe777a1f9219c2210175a15117429ee2d2418966c`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (family : LocalDef027 n semantics) →
      LocalDef010 family → LocalDef026 n → Type
```

### D057: `LocalDef057`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `70b481668da33b5b6c0b6b1bb6200622496befc495c21c3c599f63d0852686e6`

Type:

```lean
{choice : LocalDef025} →
  {n : Nat} →
    {semantics : LocalDef003} →
      {right : LocalDef020 n semantics} →
        ((k : LocalDef026 n) →
            LocalDef034 (right.family.iteration k) →
              Or (Eq k.val n) (LocalDef035 (right.family.iteration k)) →
                LocalDef019 choice (right.iteration k) →
                  LocalDef090 choice right k) →
          LocalDef018 choice right
```

### D058: `LocalDef058`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c9329a86c1c2a0eec88310cb2ab7da37a17c3876e126d149860d1532d3f2d858`

Type:

```lean
∀ {choice : LocalDef025} {n : Nat} {semantics : LocalDef003}
  {family : LocalDef027 n semantics}
  {preconditioner : LocalDef010 family} {k : LocalDef026 n}
  {iteration : LocalDef060 family preconditioner k},
  LocalDef086 choice iteration.core →
    Real.instLE.le 0 iteration.reapplicationMagnitude →
      (∀ (i : Fin n) (j : Fin k.val),
          Real.instLE.le (abs (iteration.solutionBasisDelta i j))
            (instHMul.hMul iteration.core.gmresMagnitude (abs ((family.iteration k).vHat i j)))) →
        Real.instLE.le (LocalDef069 iteration.solutionPreconditionerDelta)
            (instHMul.hMul iteration.reapplicationMagnitude (LocalDef069 preconditioner.MRinv)) →
          Real.instLE.le iteration.reapplicationMagnitude
              (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor iteration.core.um)
                iteration.core.etaR) →
            LocalDef019 choice iteration
```

### D059: `LocalDef059`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c49aa22ae2bc07d17255c2d9e29a3c4853a867118237d96c97008368111c1f1d`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (family : LocalDef027 n semantics) →
      (preconditioner : LocalDef010 family) →
        ((k : LocalDef026 n) → LocalDef060 family preconditioner k) →
          LocalDef020 n semantics
```

### D060: `LocalDef060`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cabcb7d011f004389d989447b54059f8b7aad443bf361a37b16d687d792ee6cc`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (family : LocalDef027 n semantics) →
      LocalDef010 family → LocalDef026 n → Type
```

### D061: `LocalDef061`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `427f84a86f30b1da6b07db6978118ff047b4de573aafbf63a8e16c908402fb45`

Type:

```lean
LocalDef025
```

### D062: `LocalDef062`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `6133bccfe81dd1501b725b08532f2d706adc78d227bbaac480b149b6dafc9b4f`

Type:

```lean
LocalDef025
```

### D063: `LocalDef063`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `cd7346b530ce5e5d6ba1c2e5416ee7c43d715dd345875961bcce92cbe5f41e14`

Type:

```lean
{n : Nat} → LocalDef066 n → Type
```

### D064: `LocalDef064`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e068250f38486d591a2adfb1d7f2c918bc70608277fca9f7321223a7e5e37cbb`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    LocalDef063 system → (k : Nat) → LocalDef081 n k
```

Definition body (one-level semantic boundary):

```lean
fun n system self => self.1
```

### D065: `LocalDef065`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f076c552518a53410edcb7f11b49475fb90d812b0212bc30431c42bf011d836`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    (system : LocalDef066 n) →
      (basisFamily : LocalDef063 system) →
        ((k : LocalDef026 n) →
            LocalDef039 system semantics basisFamily k) →
          LocalDef027 n semantics
```

### D066: `LocalDef066`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e1fc353b1b432c0c1ef430f4cf2ff9afcfbed92f49cf465d778ddda0a635dd4d`

Type:

```lean
Nat → Type
```

### D067: `LocalDef067`

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

### D068: `LocalDef068`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2fe0e06752730d60394b59adb4b76c6f22ea6681023a70406cbdcfc4ba900101`

Type:

```lean
{n k : Nat} → LocalDef067 n → LocalDef081 n k → LocalDef081 n (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n k} b C i i_1 => Fin.cases (b i) (fun j => C i j) i_1
```

### D069: `LocalDef069`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1d77e739886fafe42f3444123b92bfd0ee9c522738b34d29764b9a10cb431f73`

Type:

```lean
{m k : Nat} → LocalDef081 m k → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Matrix.frobeniusNormedAddCommGroup.norm A
```

### D070: `LocalDef070`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `e36ed6bfde9948e287453e8e216377bb07ab71b2d92789cf0f62d8ac7d27adbb`

Type:

```lean
(instHAdd.hAdd 3 1).AtLeastTwo
```

### D071: `LocalDef071`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `a53f13b94d3dbfd1b78203ce451bfa60bbd01b058daa3f65ff6c7d30ec55b8bd`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

### D072: `LocalDef072`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `16466bbe231c4c118f1c0663cc1bb4687beb871eeebede56fe75c840088e6a50`

Type:

```lean
{m k : Nat} → LocalDef081 m k → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A threshold =>
  Exists fun x =>
    And (Eq (LocalDef078 x) 1)
      (Real.instLT.lt (LocalDef078 (LocalDef107 A x)) threshold)
```

### D073: `LocalDef073`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `4319e900a6bd10e9333ccb65413a9942cdbde8a752183b6e91ddff40f73fa205`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} system => LocalDef106 system.MLinv system.b
```

### D074: `LocalDef074`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `76bb6b06369be7ce2a16c093984eddc2dcc6362f2a005d765bda96800c51fcdd`

Type:

```lean
{n k : Nat} → LocalDef066 n → LocalDef081 n k → LocalDef081 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} system Z => LocalDef108 system.MLinv (LocalDef108 system.A Z)
```

### D075: `LocalDef075`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f1aafe62869eae454e5361ad332ad016bf64c6573c41182e21518b95d95352af`

Type:

```lean
LocalDef025 → {n : Nat} → LocalDef080 n → LocalDef080 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} A Ainv =>
  LocalDef109 (fun choice => Real) choice (fun _ => LocalDef103 A Ainv)
    fun _ => LocalDef105 A Ainv
```

### D076: `LocalDef076`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1215f2f65acb45382e680f1efbcd34e8a8481f75d9eae7f9f998ad5589059c91`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        LocalDef010 family → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner =>
  LocalDef075 choice (LocalDef108 family.system.A preconditioner.MRinv)
    (LocalDef108 preconditioner.MR family.system.Ainv)
```

### D077: `LocalDef077`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cdca3d40b1b6f6103929fa7a20cbb1b71a1a14af7a9c42f839dc4da0219d9b5e`

Type:

```lean
LocalDef025 →
  {n : Nat} → {semantics : LocalDef003} → LocalDef027 n semantics → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} family => LocalDef075 choice family.system.A family.system.Ainv
```

### D078: `LocalDef078`

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
fun {n} x => (LocalDef110 x).sqrt
```

### D079: `LocalDef079`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7878f8fc84c9629c27889bbc10be4df2f10323a0af9ee7131d71f631b0264ce2`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          (dimensionFactor : Real) →
            Real.instLE.le 1 dimensionFactor →
              Real →
                Real →
                  Real →
                    Real →
                      (computedC deltaC : LocalDef081 n k.val) →
                        Eq computedC
                            (instHAdd.hAdd (LocalDef074 system (basisFamily.basis k.val)) deltaC) →
                          (computedB deltaB : LocalDef067 n) →
                            Eq computedB (instHAdd.hAdd (LocalDef073 system) deltaB) →
                              (vHat : LocalDef081 n k.val) →
                                (vHatNext : LocalDef081 n (instHAdd.hAdd k.val 1)) →
                                  (beta : Real) →
                                    (hessenberg : LocalDef081 (instHAdd.hAdd k.val 1) k.val) →
                                      LocalDef123 hessenberg →
                                        Eq (LocalDef068 computedB computedC)
                                            (LocalDef125 vHatNext
                                              (LocalDef068 (LocalDef126 beta)
                                                hessenberg)) →
                                          (∀ (i : Fin n) (j : Fin k.val), Eq (vHat i j) (vHatNext i j.castSucc)) →
                                            LocalDef067 n →
                                              LocalDef081 n k.val →
                                                (yHat : LocalDef067 k.val) →
                                                  LocalDef082 computedC →
                                                    LocalDef082
                                                        (LocalDef074 system (basisFamily.basis k.val)) →
                                                      (xHat deltaX : LocalDef067 n) →
                                                        Eq xHat
                                                            (instHAdd.hAdd
                                                              (LocalDef107 (basisFamily.basis k.val) yHat)
                                                              deltaX) →
                                                          LocalDef082 vHat →
                                                            LocalDef039 system semantics
                                                              basisFamily k
```

### D080: `LocalDef080`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `da34af64745188df680411658bb275d858795f5d4483f121fbd1b2751be7bd09`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D081: `LocalDef081`

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

### D082: `LocalDef082`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85567c4b733cfc54d0f17c00f8808d0788e69e1dc928b327259677770bdad8dd`

Type:

```lean
{m k : Nat} → LocalDef081 m k → Type
```

### D083: `LocalDef083`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4d2d968913ccc754c646d62d2bcf417cd5b9d4110b2be676bfd97d49874a8ef3`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.16
```

### D084: `LocalDef084`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `9350cce7e938e2c075e92242dd9895ea2ba02bdf411a808a1d46e8c300282be1`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          Real →
            Real →
              Real →
                Real →
                  Real →
                    (zHat : LocalDef081 n k.val) →
                      (preconditionerDelta : Fin k.val → LocalDef080 n) →
                        (∀ (j : Fin k.val),
                            Eq (LocalDef121 zHat j)
                              (LocalDef106 (instHAdd.hAdd preconditioner.MRinv (preconditionerDelta j))
                                (LocalDef121 (family.iteration k).vHat j))) →
                          (matrixDelta : Fin k.val → LocalDef080 n) →
                            (∀ (j : Fin k.val),
                                Eq (LocalDef121 (family.iteration k).computedC j)
                                  (LocalDef106 (instHAdd.hAdd family.system.A (matrixDelta j))
                                    (LocalDef121 zHat j))) →
                              (∀ (j : Fin k.val),
                                  Eq (LocalDef121 (family.basisFamily.basis k.val) j)
                                    (instHAdd.hAdd (LocalDef121 zHat j)
                                      (LocalDef106 family.system.Ainv
                                        (LocalDef106 (matrixDelta j) (LocalDef121 zHat j))))) →
                                Eq (family.iteration k).deltaC 0 →
                                  Eq (family.iteration k).epsilonC 0 →
                                    Eq (family.iteration k).deltaB 0 →
                                      Eq (family.iteration k).epsilonB 0 →
                                        Real → Real → Real → LocalDef049 family preconditioner k
```

### D085: `LocalDef085`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b56e2cbdae79a1e58d5c79b9e12a34b46e582903610864017bfea9b8e97c9713`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef049 family preconditioner k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.6
```

### D086: `LocalDef086`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `016be990d9e6562997c177aa1874f71efa7402ccc6972370d935b3f4dafea7a5`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        {preconditioner : LocalDef010 family} →
          {k : LocalDef026 n} → LocalDef049 family preconditioner k → Prop
```

### D087: `LocalDef087`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `5cef23cfeb936e19b0b7988e63298cf52d29246a942e2901eb35bd8ab58fee68`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      LocalDef013 n semantics → LocalDef026 n → Type
```

### D088: `LocalDef088`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `87cf04a5e2068651a900467f8158ee477865ac28341036c97845ae083f25d796`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          (core : LocalDef049 family preconditioner k) →
            (solutionBasisDelta : LocalDef081 n k.val) →
              Eq (family.iteration k).xHat
                  (LocalDef107 (instHAdd.hAdd core.zHat solutionBasisDelta) (family.iteration k).yHat) →
                LocalDef056 family preconditioner k
```

### D089: `LocalDef089`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `b784e6b43783fd820c5c035d7b910e51529d7e16a921e8ffb3f3a23ab39f4f6c`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef056 family preconditioner k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D090: `LocalDef090`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `4cde4ccc7bab7c66868f49ed20203d5fc92241921cf22fc6c8b0a001b613934b`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      LocalDef020 n semantics → LocalDef026 n → Type
```

### D091: `LocalDef091`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1ada26d0afe6a36a93c329bf7511d6ee605dbdb09560947e17203c3d31d3a79a`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef049 family preconditioner k →
            (solutionBasisDelta : LocalDef081 n k.val) →
              (solutionPreconditionerDelta : LocalDef080 n) →
                Eq (family.iteration k).xHat
                    (LocalDef106 (instHAdd.hAdd preconditioner.MRinv solutionPreconditionerDelta)
                      (LocalDef107 (instHAdd.hAdd (family.iteration k).vHat solutionBasisDelta)
                        (family.iteration k).yHat)) →
                  Real → LocalDef060 family preconditioner k
```

### D092: `LocalDef092`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `87c016c305345e674cfc17562e6417fa28c4f011d96f9c9668c558690209e001`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef060 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.5
```

### D093: `LocalDef093`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cf09e35efe02c9c8e0dfca39c9c32922056955e832949936696a5292fb763d41`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef060 family preconditioner k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.2
```

### D094: `LocalDef094`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5c63c83c2443351239918695b96d935028fbce761a000c12ef703ba7a99982f`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef060 family preconditioner k → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.3
```

### D095: `LocalDef095`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `436dbb701a39337ce5332902d90e6973e9b3a19d7776ff8eb60c5b47e5d23e93`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    (basis : (k : Nat) → LocalDef081 n k) →
      (∀ (k : Nat), instLTNat.lt 0 k → instLENat.le k n → LocalDef122 (basis k)) →
        (∀ (k : Nat),
            instLTNat.lt k n → ∀ (i : Fin n) (j : Fin k), Eq (basis k i j) (basis (instHAdd.hAdd k 1) i j.castSucc)) →
          LocalDef063 system
```

### D096: `LocalDef096`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4bfdf1aea21b236835dd2c7582c4c22271b794da188a0ba1ccc5a694afff4be4`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D097: `LocalDef097`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `5af7fc516b339d9009da5411f78f824a75063e508c6084b47f8ef7e44f62db8e`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D098: `LocalDef098`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `49bf2034c91342a98820db7017c34f0a2e9d1c3aaff5c66811d036bd3b1a1dcf`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D099: `LocalDef099`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef0cd4e713f0114adf6c09b9205814f09e9a4779fd1ba97cdfa6d00458ff172c`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D100: `LocalDef100`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f2a130fd36774a5574504267aaab72b46108b1c686d97df059b452f44cf66199`

Type:

```lean
{n : Nat} → LocalDef066 n → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.6
```

### D101: `LocalDef101`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `7bcc8692a7674f34e3a15ff70ef2f751cd9c1fac7daae1fce18d92dbba9eb545`

Type:

```lean
∀ {n : Nat} (self : LocalDef066 n), instLTNat.lt 0 n
```

### D102: `LocalDef102`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `b6ce3331a8ec6712c83ccceaf2dca3a6a89ee6e003288845219a21bd32c3a9a7`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (A Ainv ML MLinv : LocalDef080 n) →
      (b xExact : LocalDef067 n) →
        LocalDef104 A Ainv →
          LocalDef104 ML MLinv →
            Ne b 0 → Eq (LocalDef106 A xExact) b → LocalDef066 n
```

### D103: `LocalDef103`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f0caab4531a1846f654c1dd00b274cf19ace9e44cbf1773a4d95f56800e9ffd1`

Type:

```lean
{n : Nat} → LocalDef080 n → LocalDef080 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef069 Ainv) (LocalDef069 A)
```

### D104: `LocalDef104`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `77b8f45040142dc9a1f4c41dcad3fdb3c16d0ebc240adbaa5dac1c0ffabb00df`

Type:

```lean
{n : Nat} → LocalDef080 n → LocalDef080 n → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv =>
  And (∀ (x : LocalDef067 n), Eq (LocalDef106 Ainv (LocalDef106 A x)) x)
    (∀ (x : LocalDef067 n), Eq (LocalDef106 A (LocalDef106 Ainv x)) x)
```

### D105: `LocalDef105`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b9e5fd26e72448c1ee9298822e9b5726faff2cf4d27bb54e9c9330a2aa739b35`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (LocalDef124 A) (LocalDef124 Ainv)
```

### D106: `LocalDef106`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1ae9d14b7b4a526e86a7616a8ca6e9f01f9c771fcb8636b83a7aee0f1c7547c1`

Type:

```lean
{n : Nat} → LocalDef080 n → LocalDef067 n → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D107: `LocalDef107`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5e9563ecebb7f14ef3dfee0df9571dc5b992f9e32c9c0c19c6b34001b872d8e1`

Type:

```lean
{m k : Nat} → LocalDef081 m k → LocalDef067 k → LocalDef067 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D108: `LocalDef108`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2b8444b51bdd6b2f43ba4d5ab8376e63a1788f241ad49a66ee55d945464e1769`

Type:

```lean
{n k : Nat} → LocalDef080 n → LocalDef081 n k → LocalDef081 n k
```

Definition body (one-level semantic boundary):

```lean
fun {n k} A B i j => Finset.univ.sum fun q => instHMul.hMul (A i q) (B q j)
```

### D109: `LocalDef109`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `83ccdc85da23e3fc059d5d5518c2749c7999b293db657535adaacd198c92d663`

Type:

```lean
(motive : LocalDef025 → Sort u_1) →
  (choice : LocalDef025) →
    (Unit → motive LocalDef061) →
      (Unit → motive LocalDef062) → motive choice
```

Definition body (one-level semantic boundary):

```lean
fun motive choice h_1 h_2 => LocalDef120 choice (h_1 Unit.unit) (h_2 Unit.unit)
```

### D110: `LocalDef110`

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

### D111: `LocalDef111`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `50a6535dd8ce1360428870bf95756a470737cd826b008cdbfad61b0808d02dee`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.7
```

### D112: `LocalDef112`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `737380e55e6f4d002c09906b6bcf025c9bda8e34cbadd9e15e1eacd15618ad5b`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.11
```

### D113: `LocalDef113`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `8b975d7f99cb27792acfddfe57d6c62419fd06a5e22f149738ab976b8c92053c`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.8
```

### D114: `LocalDef114`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `f8030bfc92643eceb346f953d6858c99670b9bac33003239e0d7a3301ae7fe23`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.4
```

### D115: `LocalDef115`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `17f32ecc0179dc60da4f31e7911e5c48e15e77ecc3d4689d7406db80def04525`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef067 k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.22
```

### D116: `LocalDef116`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `785b5c97bf75f07f40320aa93a7623aeb13039753f9b0be30629411ab231dca4`

Type:

```lean
{m k : Nat} →
  {A : LocalDef081 m k} →
    (sigmaMin sigmaMax : Real) →
      Real.instLE.le 0 sigmaMin →
        Real.instLE.le 0 sigmaMax →
          (∀ (x : LocalDef067 k),
              Real.instLE.le (instHMul.hMul sigmaMin (LocalDef078 x))
                (LocalDef078 (LocalDef107 A x))) →
            (∀ (x : LocalDef067 k),
                Real.instLE.le (LocalDef078 (LocalDef107 A x))
                  (instHMul.hMul sigmaMax (LocalDef078 x))) →
              (instLTNat.lt 0 k →
                  Exists fun x =>
                    And (Eq (LocalDef078 x) 1)
                      (Eq (LocalDef078 (LocalDef107 A x)) sigmaMin)) →
                (instLTNat.lt 0 k →
                    Exists fun x =>
                      And (Eq (LocalDef078 x) 1)
                        (Eq (LocalDef078 (LocalDef107 A x)) sigmaMax)) →
                  LocalDef082 A
```

### D117: `LocalDef117`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `1e5461a9440d5db520105ad599559071d3c6c5eaba5025c2d2229bd770e0a7c2`

Type:

```lean
∀ {choice : LocalDef025} {n : Nat} {semantics : LocalDef003}
  {family : LocalDef027 n semantics}
  {preconditioner : LocalDef010 family} {k : LocalDef026 n}
  {core : LocalDef049 family preconditioner k},
  And (Real.instLE.le 0 core.ug)
      (And (Real.instLE.le 0 core.um)
        (And (Real.instLE.le 0 core.ua) (And (Real.instLE.le 0 core.etaR) (Real.instLE.le 0 core.rhoAR)))) →
    And (Real.instLE.le 0 core.gmresMagnitude)
        (And (Real.instLE.le 0 core.basisPreconditionerMagnitude) (Real.instLE.le 0 core.matrixMagnitude)) →
      LocalDef137
          (instHAdd.hAdd (family.iteration k).computedC (family.iteration k).leastSquaresDeltaC)
          (instHAdd.hAdd (family.iteration k).computedB (family.iteration k).leastSquaresDeltaB)
          (family.iteration k).yHat →
        (∀ (j : Fin (instHAdd.hAdd k.val 1)),
            Real.instLE.le
              (LocalDef078
                (LocalDef121
                  (LocalDef068 (family.iteration k).leastSquaresDeltaB
                    (family.iteration k).leastSquaresDeltaC)
                  j))
              (instHMul.hMul core.gmresMagnitude
                (LocalDef078
                  (LocalDef121
                    (LocalDef068 (family.iteration k).computedB (family.iteration k).computedC) j)))) →
          (∀ (j : Fin k.val),
              Real.instLE.le (LocalDef069 (core.preconditionerDelta j))
                (instHMul.hMul core.basisPreconditionerMagnitude (LocalDef069 preconditioner.MRinv))) →
            (∀ (j : Fin k.val) (i q : Fin n),
                Real.instLE.le (abs (core.matrixDelta j i q))
                  (instHMul.hMul core.matrixMagnitude (abs (family.system.A i q)))) →
              Real.instLE.le core.gmresMagnitude (instHMul.hMul (family.iteration k).dimensionFactor core.ug) →
                Real.instLE.le core.basisPreconditionerMagnitude
                    (instHMul.hMul (instHMul.hMul (family.iteration k).dimensionFactor core.um) core.etaR) →
                  Real.instLE.le core.matrixMagnitude (instHMul.hMul (family.iteration k).dimensionFactor core.ua) →
                    Real.instLT.lt 0
                        (LocalDef078 (LocalDef107 core.zHat (family.iteration k).yHat)) →
                      Eq core.rhoAR
                          (instHDiv.hDiv
                            (LocalDef078 (LocalDef136 core.zHat (family.iteration k).yHat))
                            (LocalDef078 (LocalDef107 core.zHat (family.iteration k).yHat))) →
                        semantics.small
                            (LocalDef138 choice preconditioner core.ug core.um core.ua
                              core.etaR core.rhoAR) →
                          LocalDef086 choice core
```

### D118: `LocalDef118`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `6108f0867ca7c4748ff0bdc401b9f44c593ecf6cb651694c00eaab4e73a79644`

Type:

```lean
{choice : LocalDef025} →
  {n : Nat} →
    {semantics : LocalDef003} →
      {flexible : LocalDef013 n semantics} →
        {k : LocalDef026 n} →
          (gmresContribution matrixContribution remainder : LocalDef067 n) →
            Eq (instHSub.hSub (flexible.family.iteration k).xHat flexible.family.system.xExact)
                (instHAdd.hAdd (instHAdd.hAdd gmresContribution matrixContribution) remainder) →
              semantics.secondOrder
                  (instHDiv.hDiv (LocalDef078 remainder)
                    (LocalDef078 flexible.family.system.xExact)) →
                Real.instLE.le
                    (instHDiv.hDiv (LocalDef078 gmresContribution)
                      (LocalDef078 flexible.family.system.xExact))
                    (instHMul.hMul
                      (instHMul.hMul (flexible.iteration k).core.gmresMagnitude
                        (LocalDef076 choice flexible.preconditioner))
                      (LocalDef038 choice flexible.preconditioner)) →
                  Real.instLE.le
                      (instHDiv.hDiv (LocalDef078 matrixContribution)
                        (LocalDef078 flexible.family.system.xExact))
                      (instHMul.hMul
                        (instHMul.hMul (flexible.iteration k).core.matrixMagnitude
                          (LocalDef077 choice flexible.family))
                        (flexible.iteration k).core.rhoAR) →
                    LocalDef087 choice flexible k
```

### D119: `LocalDef119`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `dec83b2bcce190dc8d99236513f01b0fcfa967640cfbf6b2cedd6b3064b9fa43`

Type:

```lean
{choice : LocalDef025} →
  {n : Nat} →
    {semantics : LocalDef003} →
      {right : LocalDef020 n semantics} →
        {k : LocalDef026 n} →
          (gmresContribution reapplicationContribution matrixContribution remainder : LocalDef067 n) →
            Eq (instHSub.hSub (right.family.iteration k).xHat right.family.system.xExact)
                (instHAdd.hAdd
                  (instHAdd.hAdd (instHAdd.hAdd gmresContribution reapplicationContribution) matrixContribution)
                  remainder) →
              semantics.secondOrder
                  (instHDiv.hDiv (LocalDef078 remainder)
                    (LocalDef078 right.family.system.xExact)) →
                Real.instLE.le
                    (instHDiv.hDiv (LocalDef078 gmresContribution)
                      (LocalDef078 right.family.system.xExact))
                    (instHMul.hMul
                      (instHMul.hMul (right.iteration k).core.gmresMagnitude
                        (LocalDef076 choice right.preconditioner))
                      (LocalDef038 choice right.preconditioner)) →
                  Real.instLE.le
                      (instHDiv.hDiv (LocalDef078 reapplicationContribution)
                        (LocalDef078 right.family.system.xExact))
                      (instHMul.hMul (right.iteration k).reapplicationMagnitude
                        (LocalDef038 choice right.preconditioner)) →
                    Real.instLE.le
                        (instHDiv.hDiv (LocalDef078 matrixContribution)
                          (LocalDef078 right.family.system.xExact))
                        (instHMul.hMul
                          (instHMul.hMul (right.iteration k).core.matrixMagnitude
                            (LocalDef077 choice right.family))
                          (right.iteration k).core.rhoAR) →
                      LocalDef090 choice right k
```

### D120: `LocalDef120`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `db5b6b665da34fd4b2f2cfdd5c7b2ef00eb713f76f374592c931860a0ee13ab5`

Type:

```lean
{motive : LocalDef025 → Sort u} →
  (t : LocalDef025) →
    motive LocalDef061 →
      motive LocalDef062 → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t frobenius inducedTwo => LocalDef135 frobenius inducedTwo t
```

### D121: `LocalDef121`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d1c96c67d25102fa9368afc8215a13cc0626a5b92b4ea3b4e4f9c82429d0c977`

Type:

```lean
{m k : Nat} → LocalDef081 m k → Fin k → LocalDef067 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A j i => A i j
```

### D122: `LocalDef122`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `84de5f440851ab2c3f7c3f00b48f7e6daa85ef2eb14e213077a5d2a91ee34c06`

Type:

```lean
{m k : Nat} → LocalDef081 m k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A => Function.Injective (LocalDef107 A)
```

### D123: `LocalDef123`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `40e9dda219091e0a8274024ac3a6a6ec9b0f2c87f705a5d5c83ed03835619d3e`

Type:

```lean
{k : Nat} → LocalDef081 (instHAdd.hAdd k 1) k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {k} H => ∀ (i : Fin (instHAdd.hAdd k 1)) (j : Fin k), instLTNat.lt (instHAdd.hAdd j.val 1) i.val → Eq (H i j) 0
```

### D124: `LocalDef124`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `32c1a2b57edb3d01327a9830854f615bd5cdaf06ad34d12929712c0b11ac6fc8`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.instL2OpNormedAddCommGroup.norm A
```

### D125: `LocalDef125`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ea659dd0af1e90317a62571898bde6fc8ded022ac6934bf0f96c8e9243b11c08`

Type:

```lean
{m k q : Nat} → LocalDef081 m k → LocalDef081 k q → LocalDef081 m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D126: `LocalDef126`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7eeb372ed49009a9fbaa619f7d7edd369b54e614c91e79ae1a32ede22433dc11`

Type:

```lean
{k : Nat} → Real → LocalDef067 (instHAdd.hAdd k 1)
```

Definition body (one-level semantic boundary):

```lean
fun {k} beta i => ite (Eq i.val 0) beta 0
```

### D127: `LocalDef127`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `0a36228ab177e3d96350f260b42b0b39cdbb2e3af19df1b61a4bdbe4767eb7c1`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.10
```

### D128: `LocalDef128`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `09771da30686fc5e2cf381c4665caae33df2500d4d8fef9e37d1cf8a4130281b`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef067 n
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.20
```

### D129: `LocalDef129`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1474e23e024f85a3713cc0794a6573e2e4071d9d614f92fe14145947ab293054`

Type:

```lean
{n : Nat} →
  {system : LocalDef066 n} →
    {semantics : LocalDef003} →
      {basisFamily : LocalDef063 system} →
        {k : LocalDef026 n} →
          LocalDef039 system semantics basisFamily k → LocalDef081 n k.val
```

Definition body (one-level semantic boundary):

```lean
fun n system semantics basisFamily k self => self.21
```

### D130: `LocalDef130`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1bc30297c5d6628f7a45cd5221fd0209542b9615afa5f93728f12b0e31dc32b5`

Type:

```lean
LocalDef003 → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D131: `LocalDef131`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `3be4219195bebca31cbfaec9715d286b9adb4e354de2ccd68d15cad129666680`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.17
```

### D132: `LocalDef132`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `b66f88e8f2b37979a6cf8ac0604007746aa5a3ad0a7d9a915cf0d778e5f444e2`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef049 family preconditioner k → Fin k.val → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.9
```

### D133: `LocalDef133`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bc8b23ced6076df849b4846f9edb6444c8d0f16683cd7ff75dd565a2147742ad`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} → LocalDef049 family preconditioner k → Real
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.18
```

### D134: `LocalDef134`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `074af1cd613a8e30f1128a283b27720fed9a26a3f6414aa4a24a7a400215a951`

Type:

```lean
{n : Nat} →
  {semantics : LocalDef003} →
    {family : LocalDef027 n semantics} →
      {preconditioner : LocalDef010 family} →
        {k : LocalDef026 n} →
          LocalDef049 family preconditioner k → Fin k.val → LocalDef080 n
```

Definition body (one-level semantic boundary):

```lean
fun n semantics family preconditioner k self => self.7
```

### D135: `LocalDef135`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `recursor`
- Distance from target type: `5`
- Semantic SHA-256: `5eadb395765804172f60cffcf963e9e11b53ba0a106131d65ba628c848ca2cf5`

Type:

```lean
{motive : LocalDef025 → Sort u} →
  motive LocalDef061 →
    motive LocalDef062 → (t : LocalDef025) → motive t
```

### D136: `LocalDef136`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1d5e840823958a7a00f483b0b70ee1122991bd46bae53c5f8981c0aa0826e62c`

Type:

```lean
{m k : Nat} → LocalDef081 m k → LocalDef067 k → LocalDef067 m
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A x i => Finset.univ.sum fun j => instHMul.hMul (abs (A i j)) (abs (x j))
```

### D137: `LocalDef137`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3007f611ab5087af1f0566bf60dfd75fc71f78dad5e293cff7cd63de4c42ed91`

Type:

```lean
{m k : Nat} → LocalDef081 m k → LocalDef067 m → LocalDef067 k → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m k} A b y =>
  ∀ (z : LocalDef067 k),
    Real.instLE.le (LocalDef078 (instHSub.hSub b (LocalDef107 A y)))
      (LocalDef078 (instHSub.hSub b (LocalDef107 A z)))
```

### D138: `LocalDef138`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6c11ce8f32486a3c6e70c22d8f56aa5b74f2d37028a4a1c5593c73846e10d01d`

Type:

```lean
LocalDef025 →
  {n : Nat} →
    {semantics : LocalDef003} →
      {family : LocalDef027 n semantics} →
        LocalDef010 family → Real → Real → Real → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun choice {n} {semantics} {family} preconditioner ug um ua etaR rhoAR =>
  Real.instMax.max (instHMul.hMul ug (LocalDef076 choice preconditioner))
    (Real.instMax.max (instHMul.hMul ug (LocalDef038 choice preconditioner))
      (Real.instMax.max
        (instHMul.hMul (instHMul.hMul um etaR) (LocalDef038 choice preconditioner))
        (Real.instMax.max (instHMul.hMul (instHMul.hMul ua (LocalDef077 choice family)) rhoAR)
          (instHMul.hMul (instHMul.hMul ua (LocalDef076 choice preconditioner))
            (LocalDef038 choice preconditioner)))))
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

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```
