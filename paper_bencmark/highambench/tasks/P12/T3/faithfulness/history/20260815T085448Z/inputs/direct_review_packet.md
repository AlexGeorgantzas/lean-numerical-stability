# Declaration dossier for P12-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p12_t3_three_product_exact
    (representable : ℝ → Prop) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace)
    (h23 : tr.th + tr.tl = x2 * x3)
    (hhigh : tr.s1 + tr.a2 = x1 * tr.th)
    (hlow : tr.a3 + tr.a4 = x1 * tr.tl)
    (ha2 : representable tr.a2)
    (hmergeS : p12Nearest representable (tr.a2 + tr.a3) tr.s2)
    (hmergeTMem : representable (tr.s2 - tr.a2))
    (hmergeT : p12Nearest representable (tr.s2 - tr.a2) tr.t)
    (hmergeRMem : representable (tr.a3 - tr.t))
    (hmergeR : p12Nearest representable (tr.a3 - tr.t) tr.r)
    (hfinalMem : representable (tr.r + tr.a4))
    (hfinal : p12Nearest representable (tr.r + tr.a4) tr.s3) :
    tr.s1 + tr.s2 + tr.s3 = x1 * x2 * x3
```

## Elaborated target type

```lean
∀ (representable : Real → Prop) (x1 x2 x3 : Real) (tr : HighamBench.P12ThreeProductTrace),
  Eq (instHAdd.hAdd tr.th tr.tl) (instHMul.hMul x2 x3) →
    Eq (instHAdd.hAdd tr.s1 tr.a2) (instHMul.hMul x1 tr.th) →
      Eq (instHAdd.hAdd tr.a3 tr.a4) (instHMul.hMul x1 tr.tl) →
        representable tr.a2 →
          HighamBench.p12Nearest representable (instHAdd.hAdd tr.a2 tr.a3) tr.s2 →
            representable (instHSub.hSub tr.s2 tr.a2) →
              HighamBench.p12Nearest representable (instHSub.hSub tr.s2 tr.a2) tr.t →
                representable (instHSub.hSub tr.a3 tr.t) →
                  HighamBench.p12Nearest representable (instHSub.hSub tr.a3 tr.t) tr.r →
                    representable (instHAdd.hAdd tr.r tr.a4) →
                      HighamBench.p12Nearest representable (instHAdd.hAdd tr.r tr.a4) tr.s3 →
                        Eq (instHAdd.hAdd (instHAdd.hAdd tr.s1 tr.s2) tr.s3) (instHMul.hMul (instHMul.hMul x1 x2) x3)
```

## Fully explicit elaborated target type

```lean
∀ (representable : Real → Prop) (x1 x2 x3 : Real) (tr : HighamBench.P12ThreeProductTrace)
  (h23 :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.th tr)
        (HighamBench.P12ThreeProductTrace.tl tr))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x2 x3))
  (hhigh :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.s1 tr)
        (HighamBench.P12ThreeProductTrace.a2 tr))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1
        (HighamBench.P12ThreeProductTrace.th tr)))
  (hlow :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.a3 tr)
        (HighamBench.P12ThreeProductTrace.a4 tr))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1
        (HighamBench.P12ThreeProductTrace.tl tr)))
  (ha2 : representable (HighamBench.P12ThreeProductTrace.a2 tr))
  (hmergeS :
    HighamBench.p12Nearest representable
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.a2 tr)
        (HighamBench.P12ThreeProductTrace.a3 tr))
      (HighamBench.P12ThreeProductTrace.s2 tr))
  (hmergeTMem :
    representable
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12ThreeProductTrace.s2 tr)
        (HighamBench.P12ThreeProductTrace.a2 tr)))
  (hmergeT :
    HighamBench.p12Nearest representable
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12ThreeProductTrace.s2 tr)
        (HighamBench.P12ThreeProductTrace.a2 tr))
      (HighamBench.P12ThreeProductTrace.t tr))
  (hmergeRMem :
    representable
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12ThreeProductTrace.a3 tr)
        (HighamBench.P12ThreeProductTrace.t tr)))
  (hmergeR :
    HighamBench.p12Nearest representable
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (HighamBench.P12ThreeProductTrace.a3 tr)
        (HighamBench.P12ThreeProductTrace.t tr))
      (HighamBench.P12ThreeProductTrace.r tr))
  (hfinalMem :
    representable
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.r tr)
        (HighamBench.P12ThreeProductTrace.a4 tr)))
  (hfinal :
    HighamBench.p12Nearest representable
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.r tr)
        (HighamBench.P12ThreeProductTrace.a4 tr))
      (HighamBench.P12ThreeProductTrace.s3 tr)),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (HighamBench.P12ThreeProductTrace.s1 tr)
        (HighamBench.P12ThreeProductTrace.s2 tr))
      (HighamBench.P12ThreeProductTrace.s3 tr))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2) x3)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P12Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P12Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P12ThreeProductTrace`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9fed7af38298cc99b2584602f8dc6a0ecae65b0e3524385d306f1f4945963b4e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D002: `HighamBench.P12ThreeProductTrace.a2`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `289f898f5679c2a96ca1c8d17f6934f7742d6ec4c68888ed4aafe5f38402d989`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D003: `HighamBench.P12ThreeProductTrace.a3`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `77edbaea043595efa13eca92f6e3b1c04d5161e54a7d4235f73f14741172470c`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D004: `HighamBench.P12ThreeProductTrace.a4`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `828d7a6b53ceead32456365013d4a8160538bc8ff2ec3ff6410283d994bb6af7`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D005: `HighamBench.P12ThreeProductTrace.r`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c7b8dc2fffc1ea267c5802c01cb0380b0063444355e3660b4c7d38051a15dea6`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D006: `HighamBench.P12ThreeProductTrace.s1`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5b515b8e9df01ce69fb87b7a40875da2512619a5bce988b0b7ab88fe47d01ae`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D007: `HighamBench.P12ThreeProductTrace.s2`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `453c5b295feb863be4420245e6f5804bd3e6dcb5965719930d27d1e921c25fca`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.7
```

### D008: `HighamBench.P12ThreeProductTrace.s3`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0b3865cb5292f8d930c4cce3f1f10e9b96457792babcc341b8baa898c5d8a9de`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.10
```

### D009: `HighamBench.P12ThreeProductTrace.t`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2354459f682bf1297409ae0d53df6f74d3a641652e499bd3a7a237ac3b28f0f4`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D010: `HighamBench.P12ThreeProductTrace.th`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ef4f8744872c06aa335e817ea788e934c6412092d84ba88ad5d050a85bc11fb2`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D011: `HighamBench.P12ThreeProductTrace.tl`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fb797a747ceba50411d7c9a8a0944efd03596db1f0470f5236b78c217cccc483`

Type:

```lean
HighamBench.P12ThreeProductTrace → Real
```

Fully explicit type:

```lean
(self : HighamBench.P12ThreeProductTrace) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D012: `HighamBench.p12Nearest`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `edcdf2d37cd85e670605f9af536f80bcc7591a77ea9445f0c81565e1f99760d0`
- Reuse SHA-256: `d8b3c420977688a5152435b75ac5713580eb4b731ef6d566708ddd46e4bfcc3a`

Hash-verified prior interpretation:

p12Nearest representable exact rounded means that rounded is representable and has absolute distance from exact no greater than that of every representable candidate.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `HighamBench.P12ThreeProductTrace.mk`

- Role: `local`
- Owner module: `HighamBench.P12Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `d172449bbd7ae28c9391ca6b6804c36b26a5182c00e2723d2f44aa99b2391565`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real → Real → Real → HighamBench.P12ThreeProductTrace
```

Fully explicit type:

```lean
(th tl s1 a2 a3 a4 s2 t r s3 : Real) → HighamBench.P12ThreeProductTrace
```

### D014: `Eq`

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

### D015: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `74aa55b0ad9407a572b103fe243ec7bfd85c500b6fe3cb2cda7e9134aa7c8ed5`

Hash-verified prior interpretation:

HAdd.hAdd projects the binary operation supplied by an HAdd instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `HMul.hMul`

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

### D017: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `910865b63624f8f852cdf917c24378a2c58fe15bd9021ef96ea7cb8572a22709`

Hash-verified prior interpretation:

HSub.hSub projects the binary operation supplied by an HSub instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `5eda97e2aeddf310e1f963c8b9a394088cd4583baa5b2cfa49162cc318cd87d2`

Hash-verified prior interpretation:

Real is mathlib's type of mathematical real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `e9db96f91871c57076af00e6fb401681a44e3b6c18c7daca0597f7bbdbdfa9a9`

Hash-verified prior interpretation:

Real.instAdd supplies the standard real addition operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instMul`

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

### D021: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `9a37ea0c3ed4633bcb29365559f29747f0d50114d73cdb3937f82dfad5f40b21`

Hash-verified prior interpretation:

Real.instSub defines real subtraction as addition of the negation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `d606ddbdeb8527fc64397dcca7d82be54c432c0d137fdfd662fb34df5358cdc7`

Hash-verified prior interpretation:

instHAdd converts an Add instance into homogeneous HAdd notation by forwarding hAdd to the instance's add operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `instHMul`

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

### D024: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `04fa48c2c3005a6026ea7d75bd00afa56b0f3a065c58e799fbbbd8cdd55084be`

Hash-verified prior interpretation:

instHSub converts a Sub instance into homogeneous HSub notation by forwarding hSub to the instance's subtraction operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`
- Reuse SHA-256: `c5359964579f42cd451c7b80335c5bc6444e0bd8f9eb2ad62d6bcc73a5827d44`

Hash-verified prior interpretation:

And is logical conjunction: both component propositions must hold.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `021045e95e0c21a2eb0a14dae03247f90624c147438f82cd2bb70bbaf7adbe27`

Hash-verified prior interpretation:

LE.le projects the binary order relation supplied by an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `f77853411748aaf532855b44e49577d858002306d195b28def05f569026eb2dd`

Hash-verified prior interpretation:

Real.instAddGroup supplies the additive-group structure of the reals, including negation and the associated algebraic laws.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `d3a74f29e3c128c65a64cd85c1ff20e38c7c45bf6fef0129f1eb1707ed54a74e`

Hash-verified prior interpretation:

Real.instLE supplies the standard ordering relation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `a13a5b29df057070012dc41ff632c26b9c967412e3c02001f5e5ad789148084a`

Hash-verified prior interpretation:

Real.lattice supplies max and min operations compatible with the standard real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `a468b89dd7f25f736a8a5bd180e4b5390358b5412c8a76a75e3c898cff46f514`

Hash-verified prior interpretation:

abs is defined as max(a,-a) in a lattice-ordered additive group.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
