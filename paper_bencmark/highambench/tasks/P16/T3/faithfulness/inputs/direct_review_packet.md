# Declaration dossier for P16-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t3_mixed_precision_geometric_convergence {n : ℕ}
    (A Ainv : P16Matrix n) (c uLow uHigh : ℝ)
    (backwardError forwardError : ℕ → ℝ)
    (hc : 0 ≤ c) (huLow : 0 ≤ uLow) (huHigh : 0 ≤ uHigh)
    (hcontract : p16MixedContraction c uLow A Ainv < 1)
    (hbackward : ∀ i : ℕ,
      p16BackwardFloor c uHigh < backwardError i →
        backwardError (i + 1) ≤
          p16MixedContraction c uLow A Ainv * backwardError i)
    (hforward : ∀ i : ℕ,
      p16ForwardFloor c uHigh A Ainv < forwardError i →
        forwardError (i + 1) ≤
          p16MixedContraction c uLow A Ainv * forwardError i) :
    0 ≤ p16BackwardFloor c uHigh ∧
    0 ≤ p16ForwardFloor c uHigh A Ainv ∧
    ∀ i : ℕ,
      p16MixedContraction c uLow A Ainv ^ i ≤ 1 ∧
      ((∀ j < i, p16BackwardFloor c uHigh < backwardError j) →
        backwardError i ≤
          p16MixedContraction c uLow A Ainv ^ i * backwardError 0) ∧
      ((∀ j < i, p16ForwardFloor c uHigh A Ainv < forwardError j) →
        forwardError i ≤
          p16MixedContraction c uLow A Ainv ^ i * forwardError 0)
```

## Elaborated target type

```lean
∀ {n : Nat} (A Ainv : HighamBench.P16Matrix n) (c uLow uHigh : Real) (backwardError forwardError : Nat → Real),
  Real.instLE.le 0 c →
    Real.instLE.le 0 uLow →
      Real.instLE.le 0 uHigh →
        Real.instLT.lt (HighamBench.p16MixedContraction c uLow A Ainv) 1 →
          (∀ (i : Nat),
              Real.instLT.lt (HighamBench.p16BackwardFloor c uHigh) (backwardError i) →
                Real.instLE.le (backwardError (instHAdd.hAdd i 1))
                  (instHMul.hMul (HighamBench.p16MixedContraction c uLow A Ainv) (backwardError i))) →
            (∀ (i : Nat),
                Real.instLT.lt (HighamBench.p16ForwardFloor c uHigh A Ainv) (forwardError i) →
                  Real.instLE.le (forwardError (instHAdd.hAdd i 1))
                    (instHMul.hMul (HighamBench.p16MixedContraction c uLow A Ainv) (forwardError i))) →
              And (Real.instLE.le 0 (HighamBench.p16BackwardFloor c uHigh))
                (And (Real.instLE.le 0 (HighamBench.p16ForwardFloor c uHigh A Ainv))
                  (∀ (i : Nat),
                    And (Real.instLE.le (instHPow.hPow (HighamBench.p16MixedContraction c uLow A Ainv) i) 1)
                      (And
                        ((∀ (j : Nat),
                            instLTNat.lt j i →
                              Real.instLT.lt (HighamBench.p16BackwardFloor c uHigh) (backwardError j)) →
                          Real.instLE.le (backwardError i)
                            (instHMul.hMul (instHPow.hPow (HighamBench.p16MixedContraction c uLow A Ainv) i)
                              (backwardError 0)))
                        ((∀ (j : Nat),
                            instLTNat.lt j i →
                              Real.instLT.lt (HighamBench.p16ForwardFloor c uHigh A Ainv) (forwardError j)) →
                          Real.instLE.le (forwardError i)
                            (instHMul.hMul (instHPow.hPow (HighamBench.p16MixedContraction c uLow A Ainv) i)
                              (forwardError 0))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A Ainv : HighamBench.P16Matrix n) (c uLow uHigh : Real) (backwardError forwardError : Nat → Real)
  (hc : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
  (huLow : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uLow)
  (huHigh :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uHigh)
  (hcontract :
    @LT.lt.{0} Real Real.instLT (@HighamBench.p16MixedContraction n c uLow A Ainv)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hbackward :
    ∀ (i : Nat),
      @LT.lt.{0} Real Real.instLT (HighamBench.p16BackwardFloor c uHigh) (backwardError i) →
        @LE.le.{0} Real Real.instLE
          (backwardError
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16MixedContraction n c uLow A Ainv) (backwardError i)))
  (hforward :
    ∀ (i : Nat),
      @LT.lt.{0} Real Real.instLT (@HighamBench.p16ForwardFloor n c uHigh A Ainv) (forwardError i) →
        @LE.le.{0} Real Real.instLE
          (forwardError
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16MixedContraction n c uLow A Ainv) (forwardError i))),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (HighamBench.p16BackwardFloor c uHigh))
    (And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HighamBench.p16ForwardFloor n c uHigh A Ainv))
      (∀ (i : Nat),
        And
          (@LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HighamBench.p16MixedContraction n c uLow A Ainv) i)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            ((∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j i →
                  @LT.lt.{0} Real Real.instLT (HighamBench.p16BackwardFloor c uHigh) (backwardError j)) →
              @LE.le.{0} Real Real.instLE (backwardError i)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                    (@HighamBench.p16MixedContraction n c uLow A Ainv) i)
                  (backwardError (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            ((∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j i →
                  @LT.lt.{0} Real Real.instLT (@HighamBench.p16ForwardFloor n c uHigh A Ainv) (forwardError j)) →
              @LE.le.{0} Real Real.instLE (forwardError i)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                    (@HighamBench.p16MixedContraction n c uLow A Ainv) i)
                  (forwardError (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P16Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P16Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P16Matrix`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Semantic SHA-256: `36b086346c3347b53ec18d195e2ddb2540e7ae44e2039744f1587ecb712cd8f4`
- Reuse SHA-256: `ffbeebbf09b94304e6ba899c184a755d92d61114ead518a244e1b35f027a7c3f`

Hash-verified prior interpretation:

P16Matrix n is the type of square n-by-n real matrices, encoded as Matrix (Fin n) (Fin n) Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D002: `HighamBench.p16BackwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `67967df8562b54f2242adf4a35ff9efaafd1fd0ae5dbd7328c48a1b9cd6b9822`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(c uHigh : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun c uHigh => instHMul.hMul c uHigh
```

### D003: `HighamBench.p16ForwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a027b1dcdfeedbe6f36e815598c8dca9bb14207304dad1b9d44fdfdb160bddf1`

Type:

```lean
{n : Nat} → Real → Real → HighamBench.P16Matrix n → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (c uHigh : Real) → (A Ainv : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} c uHigh A Ainv => instHMul.hMul (instHMul.hMul c uHigh) (HighamBench.p16ConditionNumberF A Ainv)
```

### D004: `HighamBench.p16MixedContraction`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9ee8fac2026ec5474e4a6638115eab51c7f971b0be3b81939be327cc621fd4c6`

Type:

```lean
{n : Nat} → Real → Real → HighamBench.P16Matrix n → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (c uLow : Real) → (A Ainv : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} c uLow A Ainv => instHMul.hMul (instHMul.hMul c uLow) (HighamBench.p16ConditionNumberF A Ainv)
```

### D005: `HighamBench.p16ConditionNumberF`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `99e08791be0c0ac1f536d0bae3aaefaaeb6cbe5672fe1bab4bed9b1077dad35c`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : HighamBench.P16Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16FrobNorm Ainv)
```

### D006: `HighamBench.p16FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`
- Reuse SHA-256: `b968d3a2d0b45b1c3bf872da03cf05ecd6e09846c7ca209f6de536aaebd13f35`

Hash-verified prior interpretation:

p16FrobNorm applies the Frobenius norm supplied by Matrix.frobeniusNormedRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `And`

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

### D008: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `bccb905728e8370e9646c7cccd463eb104efee7e96471aa6510146b7fcf77fee`

Hash-verified prior interpretation:

HAdd.hAdd dispatches to the selected addition instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `e3fb17553b22af68df8488c36c71052c60e9c389ca88004e2bb2cf667510eb7a`

Hash-verified prior interpretation:

HMul.hMul dispatches to the selected multiplication instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `cfe780d5fbbbc0ab92d3c7ad9aaa01ffd7ac8a292473edec0fa1918a1094b0d4`

Hash-verified prior interpretation:

HPow.hPow dispatches exponentiation to the selected power instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `ea124e0d69b6ba17a9979326f7858d534d4a01dd8439b0b310a00ad2dee63b4c`

Hash-verified prior interpretation:

LE.le dispatches to a type's non-strict order relation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `LT.lt`

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

### D013: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `15956c316c87873cd8a5f65e4a06236bc1e00f8b12290d7b29e05f235c269b15`

Hash-verified prior interpretation:

Monoid.toNatPow supplies natural-number powers through repeated multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `73632ee922d91d34ae71cd78e7e89f4e2bf5221aa8e186af6381b6d23548bb4d`

Hash-verified prior interpretation:

Nat supplies the finite dimension parameter n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `b8594a4d74ac5558b8c0e4cee5af36c8130e176fdf406e80e613d0a29b0e29b2`

Hash-verified prior interpretation:

OfNat.ofNat interprets a natural-number literal in its inferred type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `One.toOfNat1`

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

### D017: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `5f86846e758b697eea44a7e2793f96c369383d12c9c1d520b9a92ee27556a4b9`

Hash-verified prior interpretation:

Real is the scalar type of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `f8156622ee780098421319cab2e680ca5557860f91b3a88e807eec8db9254fff`

Hash-verified prior interpretation:

Real.instLE supplies the usual order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D020: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `6cf22d455b7f8ebfec62855a70ce41a526711be7727e9345fa384f7d38c37e6c`

Hash-verified prior interpretation:

This instance supplies real multiplication, one, and natural powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `d78c1d7de8cc0fbb7f498f83fbdcc666ccdb17eeaf9034440b7b837a0447ab1e`

Hash-verified prior interpretation:

Real.instMul supplies ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instOne`

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

### D023: `Real.instZero`

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

### D024: `Zero.toOfNat0`

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

### D025: `instAddNat`

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

### D026: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `6f0b19eff9ebf3c2664ae08b235007344f6c38235439d850bf0e8e979215f44a`

Hash-verified prior interpretation:

instHAdd converts an Add instance into homogeneous addition notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `05f8c242dd596b816b6c96854cd7888a2a0768b6ab28d3cc9ec42a0447fe49de`

Hash-verified prior interpretation:

instHMul converts a Mul instance into homogeneous multiplication notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `7257bf463c1dc11605a76a2b99985cc2bfaee67b31ae5823beeaa4f413438044`

Hash-verified prior interpretation:

instHPow converts a Pow instance into homogeneous exponentiation notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `instLTNat`

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

### D030: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `fb29da88daaa41e54a252f4cfd720515a00510f989a752e6d9045d940d8fcc1e`

Hash-verified prior interpretation:

instOfNatNat interprets a natural-number literal as that natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `8dcc862934e50ebf52b2b22198fed54e8ab013a6fd46ca91fdb33543c1ea0b16`

Hash-verified prior interpretation:

Fin n is the finite index type with n elements.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `2b777d035e0442642a6626788335aacf6f75de997efe3278638f4e153deb6c9e`

Hash-verified prior interpretation:

Matrix m n alpha is the function type m -> n -> alpha.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `9028a532713e80ab1a2b3f461ff6d5ef04b60d38ea399e980b3219193c78f062`

Hash-verified prior interpretation:

Fin.fintype enumerates all members of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`
- Reuse SHA-256: `dc3e854d5fca03969d59a3097d29ac7c1a91e08530894defba0c2fde01075475`

Hash-verified prior interpretation:

This instance equips finite square matrices over an RCLike scalar with the Frobenius norm and ring operations.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`
- Reuse SHA-256: `788fb8f3bef930cf7ff184a094e9e72b0e0481e8b6a96ce307ad91be2b22a7d1`

Hash-verified prior interpretation:

Norm.norm extracts the real-valued norm function from a Norm instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`
- Reuse SHA-256: `08a5acf08699207ce0cadcdca3b16fbc233b269b15e46e9963b55b3be607e0ee`

Hash-verified prior interpretation:

NormedRing.toNorm projects the norm structure from a normed ring.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`
- Reuse SHA-256: `5715ed812e95f5837f773fb62677c21c46f8353eef90aaef46757edfc7a68103`

Hash-verified prior interpretation:

Real.instRCLike equips Real with the analytic and normed-field structure needed by the matrix Frobenius instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`
- Reuse SHA-256: `d71c379c0fee0456d0ab514f981cd7db5462e7ef21cc27a4ee48aaef2ce71955`

Hash-verified prior interpretation:

instDecidableEqFin decides equality of finite indices.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
