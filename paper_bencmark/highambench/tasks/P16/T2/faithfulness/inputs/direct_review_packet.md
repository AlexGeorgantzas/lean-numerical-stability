# Declaration dossier for P16-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t2_restarted_residual_recurrence
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (A : P16Matrix n) (b : P16Vector n) (iteration : ℕ)
    (scale : ι → ℝ) (hscale : Filter.Tendsto scale l (nhds 0))
    (hn : 0 < n) (hA : p16IsNonsingular A) (hb : b ≠ 0)
    (step : P16Lemma42BackwardStep l scale A b iteration) :
    (∀ t,
      p16MatVec A (step.xHatNext t) - b =
        step.deltaR t + p16MatVec A (step.correctionHat t) -
          step.residualHat t + p16MatVec A (step.deltaX t)) ∧
      p16FirstOrderLeAt l scale
        (fun t ↦ p16VecNorm (p16Residual A b (step.xHatNext t)))
        (fun t ↦
          step.w t * p16VecNorm (p16Residual A b (step.xHat t)) +
            (step.epsilonR t + step.epsilonU t + step.omega t) *
              (p16VecNorm b +
                p16FrobNorm A * p16VecNorm (step.xHatNext t)))
```

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (A : HighamBench.P16Matrix n) (b : HighamBench.P16Vector n)
  (iteration : Nat) (scale : ι → Real),
  Filter.Tendsto scale l (nhds 0) →
    instLTNat.lt 0 n →
      HighamBench.p16IsNonsingular A →
        Ne b 0 →
          ∀ (step : HighamBench.P16Lemma42BackwardStep l scale A b iteration),
            And
              (∀ (t : ι),
                Eq (instHSub.hSub (HighamBench.p16MatVec A (step.xHatNext t)) b)
                  (instHAdd.hAdd
                    (instHSub.hSub (instHAdd.hAdd (step.deltaR t) (HighamBench.p16MatVec A (step.correctionHat t)))
                      (step.residualHat t))
                    (HighamBench.p16MatVec A (step.deltaX t))))
              (HighamBench.p16FirstOrderLeAt l scale
                (fun t => HighamBench.p16VecNorm (HighamBench.p16Residual A b (step.xHatNext t))) fun t =>
                instHAdd.hAdd
                  (instHMul.hMul (step.w t) (HighamBench.p16VecNorm (HighamBench.p16Residual A b (step.xHat t))))
                  (instHMul.hMul (instHAdd.hAdd (instHAdd.hAdd (step.epsilonR t) (step.epsilonU t)) (step.omega t))
                    (instHAdd.hAdd (HighamBench.p16VecNorm b)
                      (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm (step.xHatNext t))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l] (A : HighamBench.P16Matrix n)
  (b : HighamBench.P16Vector n) (iteration : Nat) (scale : ι → Real)
  (hscale :
    @Filter.Tendsto.{u_1, 0} ι Real scale l
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hA : @HighamBench.p16IsNonsingular n A)
  (hb :
    @Ne.{1} (HighamBench.P16Vector n) b
      (@OfNat.ofNat.{0} (HighamBench.P16Vector n) (nat_lit 0)
        (@Zero.toOfNat0.{0} (HighamBench.P16Vector n)
          (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero))))
  (step : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b iteration),
  And
    (∀ (t : ι),
      @Eq.{1} (HighamBench.P16Vector n)
        (@HSub.hSub.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
          (@instHSub.{0} (HighamBench.P16Vector n)
            (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
          (@HighamBench.p16MatVec n A
            (@HighamBench.P16Lemma42BackwardStep.xHatNext.{u_1} n ι l scale A b iteration step t))
          b)
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
          (@instHAdd.{0} (HighamBench.P16Vector n)
            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
          (@HSub.hSub.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
            (@instHSub.{0} (HighamBench.P16Vector n)
              (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
              (@instHAdd.{0} (HighamBench.P16Vector n)
                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
              (@HighamBench.P16Lemma42BackwardStep.deltaR.{u_1} n ι l scale A b iteration step t)
              (@HighamBench.p16MatVec n A
                (@HighamBench.P16Lemma42BackwardStep.correctionHat.{u_1} n ι l scale A b iteration step t)))
            (@HighamBench.P16Lemma42BackwardStep.residualHat.{u_1} n ι l scale A b iteration step t))
          (@HighamBench.p16MatVec n A
            (@HighamBench.P16Lemma42BackwardStep.deltaX.{u_1} n ι l scale A b iteration step t))))
    (@HighamBench.p16FirstOrderLeAt.{u_1} ι l scale
      (fun (t : ι) =>
        @HighamBench.p16VecNorm n
          (@HighamBench.p16Residual n A b
            (@HighamBench.P16Lemma42BackwardStep.xHatNext.{u_1} n ι l scale A b iteration step t)))
      fun (t : ι) =>
      @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HighamBench.P16Lemma42BackwardStep.w.{u_1} n ι l scale A b iteration step t)
          (@HighamBench.p16VecNorm n
            (@HighamBench.p16Residual n A b
              (@HighamBench.P16Lemma42BackwardStep.xHat.{u_1} n ι l scale A b iteration step t))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HighamBench.P16Lemma42BackwardStep.epsilonR.{u_1} n ι l scale A b iteration step t)
              (@HighamBench.P16Lemma42BackwardStep.epsilonU.{u_1} n ι l scale A b iteration step t))
            (@HighamBench.P16Lemma42BackwardStep.omega.{u_1} n ι l scale A b iteration step t))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p16VecNorm n b)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p16FrobNorm n A)
              (@HighamBench.p16VecNorm n
                (@HighamBench.P16Lemma42BackwardStep.xHatNext.{u_1} n ι l scale A b iteration step t))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P16Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P16Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P16Lemma42BackwardStep`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cc7e94b5850044f36dcd242407033e05f98dc02d9f2a05cbc0aee09a96890223`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → (ι → Real) → HighamBench.P16Matrix n → HighamBench.P16Vector n → Nat → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (l : Filter.{u_1} ι) →
      (scale : ι → Real) → (A : HighamBench.P16Matrix n) → (b : HighamBench.P16Vector n) → (_iteration : Nat) → Type u_1
```

### D002: `HighamBench.P16Lemma42BackwardStep.correctionHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `769af4c909a60f885dad9d39234e5a3142e961f0a60a7f6798631757d8d57c3e`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.2
```

### D003: `HighamBench.P16Lemma42BackwardStep.deltaR`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cf119231a5044d1e7ac761b53aba4e6b6a506f2e53bf7f799c522867e07112fa`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.5
```

### D004: `HighamBench.P16Lemma42BackwardStep.deltaX`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ebbfa42b00624f7efe5b85b7004fb9f052455e50572b03554ec3b53b42972223`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.6
```

### D005: `HighamBench.P16Lemma42BackwardStep.epsilonR`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `03a57b28d1c44cc12001aad5e9e3afb6432711741259f32cc682f98b494412b3`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.7
```

### D006: `HighamBench.P16Lemma42BackwardStep.epsilonU`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `7883365c6ecccac756e10f63a67b7eaf4c3fc8e10afd01cc9bca10db29359bfb`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.8
```

### D007: `HighamBench.P16Lemma42BackwardStep.omega`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3cf6ef62e6479c1e6169bf35a5af1cdbb76b3a10a3b3ab7ffa382b37ca2b5e50`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.10
```

### D008: `HighamBench.P16Lemma42BackwardStep.residualHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ea54447d32d9fe6f17aea9ccc9cee6452ee73c31a78afe92793ed15b4b81cfe5`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.4
```

### D009: `HighamBench.P16Lemma42BackwardStep.w`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fe6cf77a1c88683675bad72c98883e9491e08ef4f693655d82889df6a634170a`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.9
```

### D010: `HighamBench.P16Lemma42BackwardStep.xHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `30b25aa853759dbc622941333c316d071646da5d7c8db431db338a28b101598e`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.1
```

### D011: `HighamBench.P16Lemma42BackwardStep.xHatNext`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4084414a6b8cdfb8413b898537cfd2ec985b26f28d3e3ea7b47c59f29b18dbae`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} → HighamBench.P16Lemma42BackwardStep l scale A b _iteration → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (self : @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration) →
                ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l scale A b _iteration self => self.3
```

### D012: `HighamBench.P16Matrix`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `36b086346c3347b53ec18d195e2ddb2540e7ae44e2039744f1587ecb712cd8f4`

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

### D013: `HighamBench.P16Vector`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b643f0f6e4b56118846938b88a1ae79ef2b1849df9e9a3440a9ac88a10e94782`

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

### D014: `HighamBench.p16FirstOrderLeAt`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f8fb89f45dff8ea408faebbf7940e52c3a8135ec7c9fa4489c8e3a8540da3a7b`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale lhs rhs : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (HighamBench.p16SecondOrderAt l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D015: `HighamBench.p16FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.frobeniusNormedRing.norm A
```

### D016: `HighamBench.p16IsNonsingular`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `85b5f4df299401a78ff2042ddbaff615a4f2e4dd7ac6d5eeddc8091ccb86d714`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Function.Bijective (HighamBench.p16MatVec A)
```

### D017: `HighamBench.p16MatVec`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `633fcb3583fab70e7665e594e28a11707a692d4c14a396ea9eeda2a3724f56b9`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (x : HighamBench.P16Vector n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D018: `HighamBench.p16Residual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b6efd2406b4d95a62ec33a870000fff88d929437b9b4152b36fbbe02063a3602`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (b x : HighamBench.P16Vector n) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b x => instHSub.hSub b (HighamBench.p16MatVec A x)
```

### D019: `HighamBench.p16VecNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `bd8e44de2b8f8d577e4ee9f3b2ffb202461eebd6324f041a2f505422a111cd66`

Type:

```lean
{n : Nat} → HighamBench.P16Vector n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : HighamBench.P16Vector n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D020: `HighamBench.P16Lemma42BackwardStep.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `216f0e30aef442b86f01c281f203fd669260c1cba473a8d12117075e4ff17c55`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (xHat correctionHat xHatNext residualHat deltaR deltaX : ι → HighamBench.P16Vector n) →
                (epsilonR epsilonU w omega : ι → Real) →
                  (∀ (t : ι), Eq (residualHat t) (instHAdd.hAdd (HighamBench.p16Residual A b (xHat t)) (deltaR t))) →
                    (∀ (t : ι), Eq (xHatNext t) (instHAdd.hAdd (instHAdd.hAdd (xHat t) (correctionHat t)) (deltaX t))) →
                      (∀ (t : ι),
                          Real.instLE.le
                            (HighamBench.p16VecNorm
                              (instHSub.hSub (residualHat t) (HighamBench.p16MatVec A (correctionHat t))))
                            (instHAdd.hAdd
                              (instHMul.hMul (w t) (HighamBench.p16VecNorm (HighamBench.p16Residual A b (xHat t))))
                              (instHMul.hMul (omega t)
                                (instHAdd.hAdd (HighamBench.p16VecNorm b)
                                  (instHMul.hMul (HighamBench.p16FrobNorm A)
                                    (HighamBench.p16VecNorm (xHatNext t))))))) →
                        (∀ (t : ι),
                            Real.instLE.le (HighamBench.p16VecNorm (deltaR t))
                              (instHMul.hMul (epsilonR t)
                                (instHAdd.hAdd (HighamBench.p16VecNorm b)
                                  (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm (xHat t)))))) →
                          (∀ (t : ι),
                              Real.instLE.le (HighamBench.p16VecNorm (deltaX t))
                                (instHMul.hMul (epsilonU t) (HighamBench.p16VecNorm (xHatNext t)))) →
                            (∀ (t : ι), Real.instLE.le 0 (epsilonR t)) →
                              (∀ (t : ι), Real.instLE.le 0 (epsilonU t)) →
                                (∀ (t : ι), Real.instLE.le 0 (w t)) →
                                  (∀ (t : ι), Real.instLE.le 0 (omega t)) →
                                    Filter.Tendsto epsilonR l (nhds 0) →
                                      Filter.Tendsto epsilonU l (nhds 0) →
                                        (HighamBench.p16FirstOrderLeAt l scale
                                            (fun t => HighamBench.p16VecNorm (xHat t)) fun t =>
                                            HighamBench.p16VecNorm (xHatNext t)) →
                                          HighamBench.P16Lemma42BackwardStep l scale A b _iteration
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A : HighamBench.P16Matrix n} →
          {b : HighamBench.P16Vector n} →
            {_iteration : Nat} →
              (xHat correctionHat xHatNext residualHat deltaR deltaX : ι → HighamBench.P16Vector n) →
                (epsilonR epsilonU w omega : ι → Real) →
                  (residual_equation :
                      ∀ (t : ι),
                        @Eq.{1} (HighamBench.P16Vector n) (residualHat t)
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                            (HighamBench.P16Vector n)
                            (@instHAdd.{0} (HighamBench.P16Vector n)
                              (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                            (@HighamBench.p16Residual n A b (xHat t)) (deltaR t))) →
                    (update_equation :
                        ∀ (t : ι),
                          @Eq.{1} (HighamBench.P16Vector n) (xHatNext t)
                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                              (HighamBench.P16Vector n)
                              (@instHAdd.{0} (HighamBench.P16Vector n)
                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                (HighamBench.P16Vector n)
                                (@instHAdd.{0} (HighamBench.P16Vector n)
                                  (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAdd))
                                (xHat t) (correctionHat t))
                              (deltaX t))) →
                      (correction_residual_bound :
                          ∀ (t : ι),
                            @LE.le.{0} Real Real.instLE
                              (@HighamBench.p16VecNorm n
                                (@HSub.hSub.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                  (HighamBench.P16Vector n)
                                  (@instHSub.{0} (HighamBench.P16Vector n)
                                    (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instSub))
                                  (residualHat t) (@HighamBench.p16MatVec n A (correctionHat t))))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (w t)
                                  (@HighamBench.p16VecNorm n (@HighamBench.p16Residual n A b (xHat t))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (omega t)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HighamBench.p16VecNorm n b)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HighamBench.p16FrobNorm n A) (@HighamBench.p16VecNorm n (xHatNext t))))))) →
                        (residual_error_bound :
                            ∀ (t : ι),
                              @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n (deltaR t))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (epsilonR t)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HighamBench.p16VecNorm n b)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HighamBench.p16FrobNorm n A) (@HighamBench.p16VecNorm n (xHat t)))))) →
                          (update_error_bound :
                              ∀ (t : ι),
                                @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n (deltaX t))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (epsilonU t)
                                    (@HighamBench.p16VecNorm n (xHatNext t)))) →
                            (epsilonR_nonneg :
                                ∀ (t : ι),
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (epsilonR t)) →
                              (epsilonU_nonneg :
                                  ∀ (t : ι),
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (epsilonU t)) →
                                (w_nonneg :
                                    ∀ (t : ι),
                                      @LE.le.{0} Real Real.instLE
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        (w t)) →
                                  (omega_nonneg :
                                      ∀ (t : ι),
                                        @LE.le.{0} Real Real.instLE
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          (omega t)) →
                                    (epsilonR_tendsto_zero :
                                        @Filter.Tendsto.{u_1, 0} ι Real epsilonR l
                                          (@nhds.{0} Real
                                            (@UniformSpace.toTopologicalSpace.{0} Real
                                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                              (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                      (epsilonU_tendsto_zero :
                                          @Filter.Tendsto.{u_1, 0} ι Real epsilonU l
                                            (@nhds.{0} Real
                                              (@UniformSpace.toTopologicalSpace.{0} Real
                                                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                        (iterate_norm_comparison :
                                            @HighamBench.p16FirstOrderLeAt.{u_1} ι l scale
                                              (fun (t : ι) => @HighamBench.p16VecNorm n (xHat t)) fun (t : ι) =>
                                              @HighamBench.p16VecNorm n (xHatNext t)) →
                                          @HighamBench.P16Lemma42BackwardStep.{u_1} n ι l scale A b _iteration
```

### D021: `HighamBench.p16SecondOrderAt`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9f8f2149f6244d786fa2d0abae769fb5885e4da9a6f980dcd98dfdedc9dfea99`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale remainder : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
```

### D022: `And`

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

### D023: `Eq`

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

### D024: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

Fully explicit type:

```lean
(α : Type u_1) → Type u_1
```

### D025: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → (f : Filter.{u_1} α) → Prop
```

### D026: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → (f : α → β) → (l₁ : Filter.{u_1} α) → (l₂ : Filter.{u_2} β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D027: `Fin`

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

### D028: `HAdd.hAdd`

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

### D029: `HMul.hMul`

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

### D030: `HSub.hSub`

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

### D031: `LT.lt`

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

### D032: `Nat`

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

### D033: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D034: `OfNat.ofNat`

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

### D035: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D036: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D037: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D038: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : PseudoMetricSpace.{u} α] → UniformSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D039: `Real`

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

### D040: `Real.instAdd`

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

### D041: `Real.instMul`

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

### D042: `Real.instSub`

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

### D043: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D044: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c0d1d56a04dd3ae3fce36b5fb3c2f4fe632c2bdaed84b5667c1a60a03491a3e`

Type:

```lean
PseudoMetricSpace Real
```

Fully explicit type:

```lean
PseudoMetricSpace.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ dist := fun x y => abs (instHSub.hSub x y), dist_self := Real.pseudoMetricSpace._proof_1, dist_comm := ⋯,
  dist_triangle := ⋯, edist_dist := Real.pseudoMetricSpace._proof_2, uniformity_dist := Real.pseudoMetricSpace._proof_3,
  cobounded_sets := Real.pseudoMetricSpace._proof_4 }
```

### D045: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : UniformSpace.{u} α] → TopologicalSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D046: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D047: `instHAdd`

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

### D048: `instHMul`

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

### D049: `instHSub`

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

### D050: `instLTNat`

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

### D051: `instOfNatNat`

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

### D052: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Fully explicit type:

```lean
{X : Type u_3} → [TopologicalSpace.{u_3} X] → (x : X) → Filter.{u_3} X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```

### D053: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D054: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → (p : α → Prop) → (f : Filter.{u_1} α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D055: `Fin.fintype`

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

### D056: `Finset.sum`

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

### D057: `Finset.univ`

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

### D058: `Function.Bijective`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2da1e723243113bf4396d64f6b64f6ee8db3b9e981ad6ec7448e7745e511e5e2`

Type:

```lean
{α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Sort u₁} → {β : Sort u₂} → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => And (Function.Injective f) (Function.Surjective f)
```

### D059: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D060: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D062: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`

Type:

```lean
{m : Type u_3} → {α : Type u_5} → [Fintype m] → [RCLike α] → [DecidableEq m] → NormedRing (Matrix m m α)
```

Fully explicit type:

```lean
{m : Type u_3} →
  {α : Type u_5} →
    [Fintype.{u_3} m] →
      [RCLike.{u_5} α] → [DecidableEq.{u_3 + 1} m] → NormedRing.{max u_5 u_3} (Matrix.{u_3, u_3, u_5} m m α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {α} [Fintype m] [RCLike α] [DecidableEq m] =>
  let __src := Matrix.frobeniusSeminormedAddCommGroup;
  let __src_1 := Matrix.instRing;
  { toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := ⋯, toMul := __src_1.toMul, left_distrib := ⋯,
    right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, toOne := __src_1.toOne, one_mul := ⋯,
    mul_one := ⋯, toNatCast := __src_1.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯, npow := __src_1.npow,
    npow_zero := ⋯, npow_succ := ⋯, toNeg := __src.toNeg, toSub := __src.toSub, sub_eq_add_neg := ⋯,
    zsmul := __src.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    toIntCast := __src_1.toIntCast, intCast_ofNat := ⋯, intCast_negSucc := ⋯,
    toPseudoMetricSpace := __src.toPseudoMetricSpace, eq_of_dist_eq_zero := ⋯, dist_eq := ⋯, norm_mul_le := ⋯ }
```

### D063: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D064: `Norm.norm`

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

### D065: `NormedRing.toNorm`

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

### D066: `Real.instAddCommMonoid`

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

### D067: `Real.instAddGroup`

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

### D068: `Real.instLE`

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

### D069: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D070: `Real.instRCLike`

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

### D071: `Real.lattice`

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

### D072: `Real.sqrt`

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

### D073: `abs`

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

### D074: `instDecidableEqFin`

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

### D075: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D076: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Fully explicit type:

```lean
{α : Type u_18} →
  {E : Type u_19} →
    {F : Type u_20} → [Norm.{u_19} E] → [Norm.{u_20} F] → (l : Filter.{u_18} α) → (f : α → E) → (g : α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D077: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Fully explicit type:

```lean
Norm.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```
