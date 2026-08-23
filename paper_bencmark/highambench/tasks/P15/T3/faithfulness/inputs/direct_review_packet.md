# Declaration dossier for P15-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p15_t3_low_rank_matmul_error {b r : ℕ}
    (run : P15LowRankMatMulExecution b r) :
    let Atilde := p15LowRankMatrix run.XA run.YA
    let Btilde := p15LowRankMatrix run.YB run.XB
    let gammaC :=
      p15GammaReal (p15LowRankMatMulCost b r) run.unitRoundoff
    p15FrobNorm (run.trace.result - p15MatMul Atilde Btilde) ≤
        gammaC * p15FrobNorm Atilde * p15FrobNorm Btilde ∧
      p15FrobNorm (run.trace.result - p15MatMul run.A run.B) ≤
        gammaC * p15FrobNorm run.A * p15FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p15FrobNorm run.B +
              p15FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB)
```

## Elaborated target type

```lean
∀ {b r : Nat} (run : HighamBench.P15LowRankMatMulExecution b r),
  have Atilde := HighamBench.p15LowRankMatrix run.XA run.YA;
  have Btilde := HighamBench.p15LowRankMatrix run.YB run.XB;
  have gammaC := HighamBench.p15GammaReal (HighamBench.p15LowRankMatMulCost b r) run.unitRoundoff;
  And
    (Real.instLE.le (HighamBench.p15FrobNorm (instHSub.hSub run.trace.result (HighamBench.p15MatMul Atilde Btilde)))
      (instHMul.hMul (instHMul.hMul gammaC (HighamBench.p15FrobNorm Atilde)) (HighamBench.p15FrobNorm Btilde)))
    (Real.instLE.le (HighamBench.p15FrobNorm (instHSub.hSub run.trace.result (HighamBench.p15MatMul run.A run.B)))
      (instHAdd.hAdd
        (instHMul.hMul (instHMul.hMul gammaC (HighamBench.p15FrobNorm run.A)) (HighamBench.p15FrobNorm run.B))
        (instHMul.hMul (instHMul.hMul run.epsilon (instHAdd.hAdd 1 gammaC))
          (instHAdd.hAdd
            (instHAdd.hAdd (instHMul.hMul run.betaA (HighamBench.p15FrobNorm run.B))
              (instHMul.hMul (HighamBench.p15FrobNorm run.A) run.betaB))
            (instHMul.hMul (instHMul.hMul run.epsilon run.betaA) run.betaB)))))
```

## Fully explicit elaborated target type

```lean
∀ {b r : Nat} (run : HighamBench.P15LowRankMatMulExecution b r),
  have Atilde : HighamBench.P15Matrix b :=
    @HighamBench.p15LowRankMatrix b r (@HighamBench.P15LowRankMatMulExecution.XA b r run)
      (@HighamBench.P15LowRankMatMulExecution.YA b r run);
  have Btilde : HighamBench.P15Matrix b :=
    @HighamBench.p15LowRankMatrix b r (@HighamBench.P15LowRankMatMulExecution.YB b r run)
      (@HighamBench.P15LowRankMatMulExecution.XB b r run);
  have gammaC : Real :=
    HighamBench.p15GammaReal (HighamBench.p15LowRankMatMulCost b r)
      (@HighamBench.P15LowRankMatMulExecution.unitRoundoff b r run);
  And
    (@LE.le.{0} Real Real.instLE
      (@HighamBench.p15FrobNorm b
        (@HSub.hSub.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
          (@instHSub.{0} (HighamBench.P15Matrix b) (@Matrix.sub.{0, 0, 0} (Fin b) (Fin b) Real Real.instSub))
          (@HighamBench.P15LowRankMatMulTrace.result b r (@HighamBench.P15LowRankMatMulExecution.unitRoundoff b r run)
            (@HighamBench.P15LowRankMatMulExecution.XA b r run) (@HighamBench.P15LowRankMatMulExecution.YA b r run)
            (@HighamBench.P15LowRankMatMulExecution.XB b r run) (@HighamBench.P15LowRankMatMulExecution.YB b r run)
            (@HighamBench.P15LowRankMatMulExecution.trace b r run))
          (@HighamBench.p15MatMul b Atilde Btilde)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
          (@HighamBench.p15FrobNorm b Atilde))
        (@HighamBench.p15FrobNorm b Btilde)))
    (@LE.le.{0} Real Real.instLE
      (@HighamBench.p15FrobNorm b
        (@HSub.hSub.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
          (@instHSub.{0} (HighamBench.P15Matrix b) (@Matrix.sub.{0, 0, 0} (Fin b) (Fin b) Real Real.instSub))
          (@HighamBench.P15LowRankMatMulTrace.result b r (@HighamBench.P15LowRankMatMulExecution.unitRoundoff b r run)
            (@HighamBench.P15LowRankMatMulExecution.XA b r run) (@HighamBench.P15LowRankMatMulExecution.YA b r run)
            (@HighamBench.P15LowRankMatMulExecution.XB b r run) (@HighamBench.P15LowRankMatMulExecution.YB b r run)
            (@HighamBench.P15LowRankMatMulExecution.trace b r run))
          (@HighamBench.p15MatMul b (@HighamBench.P15LowRankMatMulExecution.A b r run)
            (@HighamBench.P15LowRankMatMulExecution.B b r run))))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
            (@HighamBench.p15FrobNorm b (@HighamBench.P15LowRankMatMulExecution.A b r run)))
          (@HighamBench.p15FrobNorm b (@HighamBench.P15LowRankMatMulExecution.B b r run)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.P15LowRankMatMulExecution.epsilon b r run)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P15LowRankMatMulExecution.betaA b r run)
                (@HighamBench.p15FrobNorm b (@HighamBench.P15LowRankMatMulExecution.B b r run)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.p15FrobNorm b (@HighamBench.P15LowRankMatMulExecution.A b r run))
                (@HighamBench.P15LowRankMatMulExecution.betaB b r run)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HighamBench.P15LowRankMatMulExecution.epsilon b r run)
                (@HighamBench.P15LowRankMatMulExecution.betaA b r run))
              (@HighamBench.P15LowRankMatMulExecution.betaB b r run))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P15Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P15Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P15LowRankMatMulExecution`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `3666f4fdd3b5324523460d402da130f9e679742d471b67c42f0ca1c642f37e71`

Type:

```lean
Nat → Nat → Type
```

Fully explicit type:

```lean
(b r : Nat) → Type
```

### D002: `HighamBench.P15LowRankMatMulExecution.A`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c889f52d19a658f1bdf5c7d86e6f8b50873ec16191b46f821aea2b958ebb822e`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.1
```

### D003: `HighamBench.P15LowRankMatMulExecution.B`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c83ec4aa89f07afd00733a11f0fcd047c5507340667477bbf2da5a93e7a1b212`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.2
```

### D004: `HighamBench.P15LowRankMatMulExecution.XA`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ab35be41a1801432331109f2759e0dd35e3d5555455b3bd1c3d79d424e7a0bab`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15RectMatrix b r
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15RectMatrix b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.3
```

### D005: `HighamBench.P15LowRankMatMulExecution.XB`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c2f06476637481b8af9fd61c190d555830eec217b552a05665859929d8f66441`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15RectMatrix b r
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15RectMatrix b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.5
```

### D006: `HighamBench.P15LowRankMatMulExecution.YA`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `655735ca6c8b50668abf58e00e7d8d3e5a49ba5baf7eed2e150fda910bde3da7`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15RectMatrix b r
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15RectMatrix b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.4
```

### D007: `HighamBench.P15LowRankMatMulExecution.YB`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c1ef8fb62a56230c489fe0f08b2f8795cb15260cd73542298b765e1c09d13449`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → HighamBench.P15RectMatrix b r
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → HighamBench.P15RectMatrix b r
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.6
```

### D008: `HighamBench.P15LowRankMatMulExecution.betaA`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `da0459358bd1eb59b7c7417b62b77993a2dc6e510f71f9e4a650fabc71e80b06`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → Real
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.8
```

### D009: `HighamBench.P15LowRankMatMulExecution.betaB`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9b96d9bc2cfabb797214f2477162811a10706bf3b08575ec0af0c5a8934dcc90`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → Real
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.9
```

### D010: `HighamBench.P15LowRankMatMulExecution.epsilon`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cf3a32d64544631bae1af9ae207b8cb82ad79c60bdfd86ed6d7003d9d4d2da65`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → Real
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.7
```

### D011: `HighamBench.P15LowRankMatMulExecution.trace`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `19fc7829d8e109d978367e4232012c66c92d9a919c6d106190faf7707f0bdb89`

Type:

```lean
{b r : Nat} →
  (self : HighamBench.P15LowRankMatMulExecution b r) →
    HighamBench.P15LowRankMatMulTrace self.unitRoundoff self.XA self.YA self.XB self.YB
```

Fully explicit type:

```lean
{b r : Nat} →
  (self : HighamBench.P15LowRankMatMulExecution b r) →
    @HighamBench.P15LowRankMatMulTrace b r (@HighamBench.P15LowRankMatMulExecution.unitRoundoff b r self)
      (@HighamBench.P15LowRankMatMulExecution.XA b r self) (@HighamBench.P15LowRankMatMulExecution.YA b r self)
      (@HighamBench.P15LowRankMatMulExecution.XB b r self) (@HighamBench.P15LowRankMatMulExecution.YB b r self)
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.21
```

### D012: `HighamBench.P15LowRankMatMulExecution.unitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `c5a7cd98cbbc6e74f3378aedbda53777780459d5437118c73a8fb1cd045f7571`

Type:

```lean
{b r : Nat} → HighamBench.P15LowRankMatMulExecution b r → Real
```

Fully explicit type:

```lean
{b r : Nat} → (self : HighamBench.P15LowRankMatMulExecution b r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r self => self.10
```

### D013: `HighamBench.P15LowRankMatMulTrace.result`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `359cb2cd213e30a09f5e3c18712b13a3462c32a22d0ac3fb7575aca56cca8326`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      HighamBench.P15LowRankMatMulTrace u XA YA XB YB → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (trace : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} {u} {XA YA XB YB} trace =>
  HighamBench.P15LowRankMatMulTrace.result.match_1 (fun trace => HighamBench.P15Matrix b) trace
    (fun middleStage leftStage finalStage => finalStage.result) fun middleStage rightStage finalStage =>
    finalStage.result
```

### D014: `HighamBench.P15Matrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

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

### D015: `HighamBench.p15FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `837bd1b4fd433e90b49e653f1245c95156c8bd043250d89a7117737646408c28`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P15Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => HighamBench.p15RectFrobNorm A
```

### D016: `HighamBench.p15GammaReal`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `271296c936d7dd54bb763543aed321ddd01215dbcf43ad0f046996eedec71821`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(k u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun k u => instHDiv.hDiv (instHMul.hMul k u) (instHSub.hSub 1 (instHMul.hMul k u))
```

### D017: `HighamBench.p15LowRankMatMulCost`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `62f7f4b7ab88235ed3725f951f20e39ecb642e295b9d0b715dca68bb80b6796f`

Type:

```lean
Nat → Nat → Real
```

Fully explicit type:

```lean
(b r : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun b r => instHAdd.hAdd b.cast (instHMul.hMul (instHMul.hMul 2 r.cast) r.cast.sqrt)
```

### D018: `HighamBench.p15LowRankMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1842193034dc631c3f6c3edebfa469daf6e8b41c15a0037f9331a904ad932e6f`

Type:

```lean
{b r : Nat} → HighamBench.P15RectMatrix b r → HighamBench.P15RectMatrix b r → HighamBench.P15Matrix b
```

Fully explicit type:

```lean
{b r : Nat} → (X Y : HighamBench.P15RectMatrix b r) → HighamBench.P15Matrix b
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X Y => HighamBench.p15RectMatMul X (HighamBench.p15RectTranspose Y)
```

### D019: `HighamBench.p15MatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `82a32c03123a1b58cce8a2734d2ddfed6b499db78b5c4e68d56caf8636e3bb0e`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → HighamBench.P15Matrix n → HighamBench.P15Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P15Matrix n) → HighamBench.P15Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D020: `HighamBench.P15LowRankMatMulExecution.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `b05e045c59874410429dc3d8ad6b5a3a2c738d070121a42ee9793e26f5f5cb7b`

Type:

```lean
{b r : Nat} →
  (A B : HighamBench.P15Matrix b) →
    (XA YA XB YB : HighamBench.P15RectMatrix b r) →
      (epsilon betaA betaB unitRoundoff : Real) →
        Real.instLE.le 0 unitRoundoff →
          Real.instLT.lt (instHMul.hMul (HighamBench.p15LowRankMatMulCost b r) unitRoundoff) 1 →
            HighamBench.p15OrthonormalColumns XA →
              HighamBench.p15OrthonormalColumns XB →
                (approximationErrorA approximationErrorB : HighamBench.P15Matrix b) →
                  Eq (HighamBench.p15LowRankMatrix XA YA) (instHAdd.hAdd A approximationErrorA) →
                    Eq (HighamBench.p15LowRankMatrix YB XB) (instHAdd.hAdd B approximationErrorB) →
                      Real.instLE.le (HighamBench.p15FrobNorm approximationErrorA) (instHMul.hMul epsilon betaA) →
                        Real.instLE.le (HighamBench.p15FrobNorm approximationErrorB) (instHMul.hMul epsilon betaB) →
                          HighamBench.P15LowRankMatMulTrace unitRoundoff XA YA XB YB →
                            HighamBench.P15LowRankMatMulExecution b r
```

Fully explicit type:

```lean
{b r : Nat} →
  (A B : HighamBench.P15Matrix b) →
    (XA YA XB YB : HighamBench.P15RectMatrix b r) →
      (epsilon betaA betaB unitRoundoff : Real) →
        (unitRoundoff_nonneg :
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              unitRoundoff) →
          (gamma_valid :
              @LT.lt.{0} Real Real.instLT
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (HighamBench.p15LowRankMatMulCost b r) unitRoundoff)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (xA_orthonormal : @HighamBench.p15OrthonormalColumns b r XA) →
              (xB_orthonormal : @HighamBench.p15OrthonormalColumns b r XB) →
                (approximationErrorA approximationErrorB : HighamBench.P15Matrix b) →
                  (approximationA_eq :
                      @Eq.{1} (HighamBench.P15Matrix b) (@HighamBench.p15LowRankMatrix b r XA YA)
                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                          (HighamBench.P15Matrix b)
                          (@instHAdd.{0} (HighamBench.P15Matrix b)
                            (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                          A approximationErrorA)) →
                    (approximationB_eq :
                        @Eq.{1} (HighamBench.P15Matrix b) (@HighamBench.p15LowRankMatrix b r YB XB)
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix b) (HighamBench.P15Matrix b)
                            (HighamBench.P15Matrix b)
                            (@instHAdd.{0} (HighamBench.P15Matrix b)
                              (@Matrix.add.{0, 0, 0} (Fin b) (Fin b) Real Real.instAdd))
                            B approximationErrorB)) →
                      (approximationErrorA_le :
                          @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b approximationErrorA)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon betaA)) →
                        (approximationErrorB_le :
                            @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm b approximationErrorB)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon betaB)) →
                          (trace : @HighamBench.P15LowRankMatMulTrace b r unitRoundoff XA YA XB YB) →
                            HighamBench.P15LowRankMatMulExecution b r
```

### D021: `HighamBench.P15LowRankMatMulTrace`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `033a99f2c6a132e74775a2fe7cb71404fc1cb419d02193c302fbf983a51feeff`

Type:

```lean
{b r : Nat} →
  Real →
    HighamBench.P15RectMatrix b r →
      HighamBench.P15RectMatrix b r → HighamBench.P15RectMatrix b r → HighamBench.P15RectMatrix b r → Type
```

Fully explicit type:

```lean
{b r : Nat} → (u : Real) → (XA YA XB YB : HighamBench.P15RectMatrix b r) → Type
```

### D022: `HighamBench.P15LowRankMatMulTrace.result.match_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a9832d0e7598fb457dd05289a18cae095f33f225bc0e94eac98a58abb89ffb9a`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (motive : HighamBench.P15LowRankMatMulTrace u XA YA XB YB → Sort u_1) →
        (trace : HighamBench.P15LowRankMatMulTrace u XA YA XB YB) →
          ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
              (leftStage : HighamBench.P15RoundedMatMulStage b r r u XA middleStage.result) →
                (finalStage :
                    HighamBench.P15RoundedMatMulStage b r b u leftStage.result (HighamBench.p15RectTranspose XB)) →
                  motive (HighamBench.P15LowRankMatMulTrace.leftAssociated middleStage leftStage finalStage)) →
            ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
                (rightStage :
                    HighamBench.P15RoundedMatMulStage r r b u middleStage.result (HighamBench.p15RectTranspose XB)) →
                  (finalStage : HighamBench.P15RoundedMatMulStage b r b u XA rightStage.result) →
                    motive (HighamBench.P15LowRankMatMulTrace.rightAssociated middleStage rightStage finalStage)) →
              motive trace
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (motive : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB → Sort u_1) →
        (trace : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) →
          (h_1 :
              (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
                (leftStage :
                    HighamBench.P15RoundedMatMulStage b r r u XA
                      (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                        middleStage)) →
                  (finalStage :
                      HighamBench.P15RoundedMatMulStage b r b u
                        (@HighamBench.P15RoundedMatMulStage.result b r r u XA
                          (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                            middleStage)
                          leftStage)
                        (@HighamBench.p15RectTranspose b r XB)) →
                    motive
                      (@HighamBench.P15LowRankMatMulTrace.leftAssociated b r u XA YA XB YB middleStage leftStage
                        finalStage)) →
            (h_2 :
                (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
                  (rightStage :
                      HighamBench.P15RoundedMatMulStage r r b u
                        (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                          middleStage)
                        (@HighamBench.p15RectTranspose b r XB)) →
                    (finalStage :
                        HighamBench.P15RoundedMatMulStage b r b u XA
                          (@HighamBench.P15RoundedMatMulStage.result r r b u
                            (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                              middleStage)
                            (@HighamBench.p15RectTranspose b r XB) rightStage)) →
                      motive
                        (@HighamBench.P15LowRankMatMulTrace.rightAssociated b r u XA YA XB YB middleStage rightStage
                          finalStage)) →
              motive trace
```

Definition body (one-level semantic boundary):

```lean
fun {b r} {u} {XA YA XB YB} motive trace h_1 h_2 =>
  HighamBench.P15LowRankMatMulTrace.casesOn trace
    (fun middleStage leftStage finalStage => h_1 middleStage leftStage finalStage)
    fun middleStage rightStage finalStage => h_2 middleStage rightStage finalStage
```

### D023: `HighamBench.P15RectMatrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8feb40d08c5292d10bb340b09678c4d176088c4c97bb1880d9f95a2c76fde9a2`

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

### D024: `HighamBench.P15RoundedMatMulStage`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3535302bbdc131800be2b6d941c9c350aa911b0ff91b290205c6899dfa886ddc`

Type:

```lean
(m n p : Nat) → Real → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix n p → Type
```

Fully explicit type:

```lean
(m n p : Nat) → (u : Real) → (A : HighamBench.P15RectMatrix m n) → (B : HighamBench.P15RectMatrix n p) → Type
```

### D025: `HighamBench.P15RoundedMatMulStage.result`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `744d41448b5b3af386989360a16106aa73d00981b39edc23bab46f3dfaaab8ec`

Type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        HighamBench.P15RoundedMatMulStage m n p u A B → HighamBench.P15RectMatrix m p
```

Fully explicit type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        (stage : HighamBench.P15RoundedMatMulStage m n p u A B) → HighamBench.P15RectMatrix m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} {u} {A} {B} stage => instHAdd.hAdd (HighamBench.p15RectMatMul A B) stage.error
```

### D026: `HighamBench.p15LowRankMatMulCost._proof_1`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `bb9e62708ab597cf99f4338108e97796364909c7609ef6ae312e9309da3679d0`

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

### D027: `HighamBench.p15RectFrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f8df59150997c9c35d296b01efb6efe480f420d12b4d3873085fbf5fff732e33`

Type:

```lean
{m n : Nat} → HighamBench.P15RectMatrix m n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P15RectMatrix m n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D028: `HighamBench.p15RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f6707f2e526a146358f007d2349847963679a3556d53c05f30fd242f90c18238`

Type:

```lean
{m n p : Nat} → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix n p → HighamBench.P15RectMatrix m p
```

Fully explicit type:

```lean
{m n p : Nat} →
  (A : HighamBench.P15RectMatrix m n) → (B : HighamBench.P15RectMatrix n p) → HighamBench.P15RectMatrix m p
```

Definition body (one-level semantic boundary):

```lean
fun {m n p} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D029: `HighamBench.p15RectTranspose`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5d09057ba3a21630e320ba9e9e5153de687ba08c185951b20149ba794d3de258`

Type:

```lean
{m n : Nat} → HighamBench.P15RectMatrix m n → HighamBench.P15RectMatrix n m
```

Fully explicit type:

```lean
{m n : Nat} → (A : HighamBench.P15RectMatrix m n) → HighamBench.P15RectMatrix n m
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A j i => A i j
```

### D030: `HighamBench.P15LowRankMatMulTrace.casesOn`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `aed07806e905cb1c87d0f04d0aaf175cf762211afc01b7dcee270c079b1f7b81`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      {motive : HighamBench.P15LowRankMatMulTrace u XA YA XB YB → Sort u} →
        (t : HighamBench.P15LowRankMatMulTrace u XA YA XB YB) →
          ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
              (leftStage : HighamBench.P15RoundedMatMulStage b r r u XA middleStage.result) →
                (finalStage :
                    HighamBench.P15RoundedMatMulStage b r b u leftStage.result (HighamBench.p15RectTranspose XB)) →
                  motive (HighamBench.P15LowRankMatMulTrace.leftAssociated middleStage leftStage finalStage)) →
            ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
                (rightStage :
                    HighamBench.P15RoundedMatMulStage r r b u middleStage.result (HighamBench.p15RectTranspose XB)) →
                  (finalStage : HighamBench.P15RoundedMatMulStage b r b u XA rightStage.result) →
                    motive (HighamBench.P15LowRankMatMulTrace.rightAssociated middleStage rightStage finalStage)) →
              motive t
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      {motive : (t : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) → Sort u} →
        (t : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) →
          (leftAssociated :
              (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
                (leftStage :
                    HighamBench.P15RoundedMatMulStage b r r u XA
                      (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                        middleStage)) →
                  (finalStage :
                      HighamBench.P15RoundedMatMulStage b r b u
                        (@HighamBench.P15RoundedMatMulStage.result b r r u XA
                          (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                            middleStage)
                          leftStage)
                        (@HighamBench.p15RectTranspose b r XB)) →
                    motive
                      (@HighamBench.P15LowRankMatMulTrace.leftAssociated b r u XA YA XB YB middleStage leftStage
                        finalStage)) →
            (rightAssociated :
                (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
                  (rightStage :
                      HighamBench.P15RoundedMatMulStage r r b u
                        (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                          middleStage)
                        (@HighamBench.p15RectTranspose b r XB)) →
                    (finalStage :
                        HighamBench.P15RoundedMatMulStage b r b u XA
                          (@HighamBench.P15RoundedMatMulStage.result r r b u
                            (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                              middleStage)
                            (@HighamBench.p15RectTranspose b r XB) rightStage)) →
                      motive
                        (@HighamBench.P15LowRankMatMulTrace.rightAssociated b r u XA YA XB YB middleStage rightStage
                          finalStage)) →
              motive t
```

Definition body (one-level semantic boundary):

```lean
fun {b r} {u} {XA YA XB YB} {motive} t leftAssociated rightAssociated =>
  HighamBench.P15LowRankMatMulTrace.rec
    (fun middleStage leftStage finalStage => leftAssociated middleStage leftStage finalStage)
    (fun middleStage rightStage finalStage => rightAssociated middleStage rightStage finalStage) t
```

### D031: `HighamBench.P15LowRankMatMulTrace.leftAssociated`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `083a8fb6d47673981cc91128d3e2d75d5776a2bdddc6436242ebf80dce7f9816`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
        (leftStage : HighamBench.P15RoundedMatMulStage b r r u XA middleStage.result) →
          HighamBench.P15RoundedMatMulStage b r b u leftStage.result (HighamBench.p15RectTranspose XB) →
            HighamBench.P15LowRankMatMulTrace u XA YA XB YB
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
        (leftStage :
            HighamBench.P15RoundedMatMulStage b r r u XA
              (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                middleStage)) →
          (finalStage :
              HighamBench.P15RoundedMatMulStage b r b u
                (@HighamBench.P15RoundedMatMulStage.result b r r u XA
                  (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                    middleStage)
                  leftStage)
                (@HighamBench.p15RectTranspose b r XB)) →
            @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB
```

### D032: `HighamBench.P15LowRankMatMulTrace.rightAssociated`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `7b9b6121e54f87a097cc8b1b5b19ab28498b151db5c70befb5cc5d733ee65ee2`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
        (rightStage : HighamBench.P15RoundedMatMulStage r r b u middleStage.result (HighamBench.p15RectTranspose XB)) →
          HighamBench.P15RoundedMatMulStage b r b u XA rightStage.result →
            HighamBench.P15LowRankMatMulTrace u XA YA XB YB
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
        (rightStage :
            HighamBench.P15RoundedMatMulStage r r b u
              (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB middleStage)
              (@HighamBench.p15RectTranspose b r XB)) →
          (finalStage :
              HighamBench.P15RoundedMatMulStage b r b u XA
                (@HighamBench.P15RoundedMatMulStage.result r r b u
                  (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                    middleStage)
                  (@HighamBench.p15RectTranspose b r XB) rightStage)) →
            @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB
```

### D033: `HighamBench.P15RoundedMatMulStage.error`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0abcbacd1d5c601c734976a11f125c8bd10fe97c10eee19e890818c87e2d81d0`

Type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        HighamBench.P15RoundedMatMulStage m n p u A B → HighamBench.P15RectMatrix m p
```

Fully explicit type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        (self : HighamBench.P15RoundedMatMulStage m n p u A B) → HighamBench.P15RectMatrix m p
```

Definition body (one-level semantic boundary):

```lean
fun m n p u A B self => self.1
```

### D034: `HighamBench.P15RoundedMatMulStage.mk`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `38c1b9c3876c1c1522bb86718966f01acf11ee602a5e5877f104ed4b52a36661`

Type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        (error : HighamBench.P15RectMatrix m p) →
          Real.instLE.le (HighamBench.p15RectFrobNorm error)
              (instHMul.hMul (instHMul.hMul (HighamBench.p15GammaReal n.cast u) (HighamBench.p15RectFrobNorm A))
                (HighamBench.p15RectFrobNorm B)) →
            HighamBench.P15RoundedMatMulStage m n p u A B
```

Fully explicit type:

```lean
{m n p : Nat} →
  {u : Real} →
    {A : HighamBench.P15RectMatrix m n} →
      {B : HighamBench.P15RectMatrix n p} →
        (error : HighamBench.P15RectMatrix m p) →
          (error_le :
              @LE.le.{0} Real Real.instLE (@HighamBench.p15RectFrobNorm m p error)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (HighamBench.p15GammaReal (@Nat.cast.{0} Real Real.instNatCast n) u)
                    (@HighamBench.p15RectFrobNorm m n A))
                  (@HighamBench.p15RectFrobNorm n p B))) →
            HighamBench.P15RoundedMatMulStage m n p u A B
```

### D035: `HighamBench.p15OrthonormalColumns`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `deb9d644f031d8e71a57f0238d55fc37a145cb41cbb82b90abe8a87780c03815`

Type:

```lean
{b r : Nat} → HighamBench.P15RectMatrix b r → Prop
```

Fully explicit type:

```lean
{b r : Nat} → (X : HighamBench.P15RectMatrix b r) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {b r} X => ∀ (j k : Fin r), Eq (Finset.univ.sum fun i => instHMul.hMul (X i j) (X i k)) (ite (Eq j k) 1 0)
```

### D036: `HighamBench.P15LowRankMatMulTrace.rec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `bb072a4d56df77ffb507e6811ead8bac55e57de78fee7437421507a773d17e53`

Type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      {motive : HighamBench.P15LowRankMatMulTrace u XA YA XB YB → Sort u} →
        ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
            (leftStage : HighamBench.P15RoundedMatMulStage b r r u XA middleStage.result) →
              (finalStage :
                  HighamBench.P15RoundedMatMulStage b r b u leftStage.result (HighamBench.p15RectTranspose XB)) →
                motive (HighamBench.P15LowRankMatMulTrace.leftAssociated middleStage leftStage finalStage)) →
          ((middleStage : HighamBench.P15RoundedMatMulStage r b r u (HighamBench.p15RectTranspose YA) YB) →
              (rightStage :
                  HighamBench.P15RoundedMatMulStage r r b u middleStage.result (HighamBench.p15RectTranspose XB)) →
                (finalStage : HighamBench.P15RoundedMatMulStage b r b u XA rightStage.result) →
                  motive (HighamBench.P15LowRankMatMulTrace.rightAssociated middleStage rightStage finalStage)) →
            (t : HighamBench.P15LowRankMatMulTrace u XA YA XB YB) → motive t
```

Fully explicit type:

```lean
{b r : Nat} →
  {u : Real} →
    {XA YA XB YB : HighamBench.P15RectMatrix b r} →
      {motive : (t : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) → Sort u} →
        (leftAssociated :
            (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
              (leftStage :
                  HighamBench.P15RoundedMatMulStage b r r u XA
                    (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                      middleStage)) →
                (finalStage :
                    HighamBench.P15RoundedMatMulStage b r b u
                      (@HighamBench.P15RoundedMatMulStage.result b r r u XA
                        (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                          middleStage)
                        leftStage)
                      (@HighamBench.p15RectTranspose b r XB)) →
                  motive
                    (@HighamBench.P15LowRankMatMulTrace.leftAssociated b r u XA YA XB YB middleStage leftStage
                      finalStage)) →
          (rightAssociated :
              (middleStage : HighamBench.P15RoundedMatMulStage r b r u (@HighamBench.p15RectTranspose b r YA) YB) →
                (rightStage :
                    HighamBench.P15RoundedMatMulStage r r b u
                      (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                        middleStage)
                      (@HighamBench.p15RectTranspose b r XB)) →
                  (finalStage :
                      HighamBench.P15RoundedMatMulStage b r b u XA
                        (@HighamBench.P15RoundedMatMulStage.result r r b u
                          (@HighamBench.P15RoundedMatMulStage.result r b r u (@HighamBench.p15RectTranspose b r YA) YB
                            middleStage)
                          (@HighamBench.p15RectTranspose b r XB) rightStage)) →
                    motive
                      (@HighamBench.P15LowRankMatMulTrace.rightAssociated b r u XA YA XB YB middleStage rightStage
                        finalStage)) →
            (t : @HighamBench.P15LowRankMatMulTrace b r u XA YA XB YB) → motive t
```

### D037: `And`

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

### D038: `Fin`

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

### D039: `HAdd.hAdd`

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

### D040: `HMul.hMul`

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

### D041: `HSub.hSub`

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

### D042: `LE.le`

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

### D043: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D044: `Nat`

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

### D045: `OfNat.ofNat`

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

### D046: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D047: `Real`

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

### D048: `Real.instAdd`

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

### D049: `Real.instLE`

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

### D050: `Real.instMul`

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

### D051: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D052: `Real.instSub`

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

### D053: `instHAdd`

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

### D054: `instHMul`

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

### D055: `instHSub`

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

### D056: `DivInvMonoid.toDiv`

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

### D057: `Fin.fintype`

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

### D058: `Finset.sum`

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

### D059: `Finset.univ`

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

### D060: `HDiv.hDiv`

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

### D061: `Matrix`

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

### D062: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D063: `Real.instAddCommMonoid`

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

### D064: `Real.instDivInvMonoid`

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

### D065: `Real.instNatCast`

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

### D066: `Real.sqrt`

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

### D067: `instHDiv`

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

### D068: `instOfNatAtLeastTwo`

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

### D069: `Eq`

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

### D070: `HPow.hPow`

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

### D071: `LT.lt`

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

### D072: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D073: `Monoid.toNatPow`

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

### D074: `Nat.AtLeastTwo`

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

### D075: `Real.instLT`

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

### D076: `Real.instMonoid`

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

### D077: `Real.instZero`

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

### D078: `Zero.toOfNat0`

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

### D079: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D080: `instHPow`

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

### D081: `instOfNatNat`

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

### D082: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D083: `ite`

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
