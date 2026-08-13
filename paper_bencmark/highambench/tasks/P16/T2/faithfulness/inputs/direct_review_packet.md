# Declaration dossier for P16-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t2_restarted_residual_recurrence {n : ℕ}
    (A : P16Matrix n) (b x correction xNext rhat deltaR deltaX : P16Vector n)
    (epsilonR epsilonU w omega : ℝ)
    (hresidual : rhat = p16Residual A b x + deltaR)
    (hupdate : xNext = x + correction + deltaX)
    (hcorrection :
      p16VecNorm (rhat - p16MatVec A correction) ≤
        w * p16VecNorm (p16Residual A b x) +
          omega * (p16VecNorm b + p16FrobNorm A * p16VecNorm xNext))
    (hdeltaR :
      p16VecNorm deltaR ≤
        epsilonR * (p16VecNorm b + p16FrobNorm A * p16VecNorm x))
    (hdeltaX : p16VecNorm deltaX ≤ epsilonU * p16VecNorm xNext)
    (hxmono : p16VecNorm x ≤ p16VecNorm xNext)
    (hepsilonR : 0 ≤ epsilonR) (hepsilonU : 0 ≤ epsilonU) :
    p16VecNorm (p16Residual A b xNext) ≤
      w * p16VecNorm (p16Residual A b x) +
        (epsilonR + epsilonU + omega) *
          (p16VecNorm b + p16FrobNorm A * p16VecNorm xNext)
```

## Elaborated target type

```lean
∀ {n : Nat} (A : HighamBench.P16Matrix n) (b x correction xNext rhat deltaR deltaX : HighamBench.P16Vector n)
  (epsilonR epsilonU w omega : Real),
  Eq rhat (instHAdd.hAdd (HighamBench.p16Residual A b x) deltaR) →
    Eq xNext (instHAdd.hAdd (instHAdd.hAdd x correction) deltaX) →
      Real.instLE.le (HighamBench.p16VecNorm (instHSub.hSub rhat (HighamBench.p16MatVec A correction)))
          (instHAdd.hAdd (instHMul.hMul w (HighamBench.p16VecNorm (HighamBench.p16Residual A b x)))
            (instHMul.hMul omega
              (instHAdd.hAdd (HighamBench.p16VecNorm b)
                (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm xNext))))) →
        Real.instLE.le (HighamBench.p16VecNorm deltaR)
            (instHMul.hMul epsilonR
              (instHAdd.hAdd (HighamBench.p16VecNorm b)
                (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm x)))) →
          Real.instLE.le (HighamBench.p16VecNorm deltaX) (instHMul.hMul epsilonU (HighamBench.p16VecNorm xNext)) →
            Real.instLE.le (HighamBench.p16VecNorm x) (HighamBench.p16VecNorm xNext) →
              Real.instLE.le 0 epsilonR →
                Real.instLE.le 0 epsilonU →
                  Real.instLE.le (HighamBench.p16VecNorm (HighamBench.p16Residual A b xNext))
                    (instHAdd.hAdd (instHMul.hMul w (HighamBench.p16VecNorm (HighamBench.p16Residual A b x)))
                      (instHMul.hMul (instHAdd.hAdd (instHAdd.hAdd epsilonR epsilonU) omega)
                        (instHAdd.hAdd (HighamBench.p16VecNorm b)
                          (instHMul.hMul (HighamBench.p16FrobNorm A) (HighamBench.p16VecNorm xNext)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A : HighamBench.P16Matrix n) (b x correction xNext rhat deltaR deltaX : HighamBench.P16Vector n)
  (epsilonR epsilonU w omega : Real)
  (hresidual :
    @Eq.{1} (HighamBench.P16Vector n) rhat
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
        (@instHAdd.{0} (HighamBench.P16Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        (@HighamBench.p16Residual n A b x) deltaR))
  (hupdate :
    @Eq.{1} (HighamBench.P16Vector n) xNext
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
        (@instHAdd.{0} (HighamBench.P16Vector n)
          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
          (@instHAdd.{0} (HighamBench.P16Vector n)
            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
          x correction)
        deltaX))
  (hcorrection :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p16VecNorm n
        (@HSub.hSub.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n) (HighamBench.P16Vector n)
          (@instHSub.{0} (HighamBench.P16Vector n)
            (@Pi.instSub.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instSub))
          rhat (@HighamBench.p16MatVec n A correction)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) w
          (@HighamBench.p16VecNorm n (@HighamBench.p16Residual n A b x)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) omega
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p16VecNorm n b)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p16FrobNorm n A)
              (@HighamBench.p16VecNorm n xNext))))))
  (hdeltaR :
    @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n deltaR)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilonR
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p16VecNorm n b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p16FrobNorm n A)
            (@HighamBench.p16VecNorm n x)))))
  (hdeltaX :
    @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n deltaX)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilonU
        (@HighamBench.p16VecNorm n xNext)))
  (hxmono : @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n x) (@HighamBench.p16VecNorm n xNext))
  (hepsilonR :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonR)
  (hepsilonU :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonU),
  @LE.le.{0} Real Real.instLE (@HighamBench.p16VecNorm n (@HighamBench.p16Residual n A b xNext))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) w
        (@HighamBench.p16VecNorm n (@HighamBench.p16Residual n A b x)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) epsilonR epsilonU) omega)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p16VecNorm n b)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p16FrobNorm n A)
            (@HighamBench.p16VecNorm n xNext)))))
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

### D002: `HighamBench.P16Vector`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Semantic SHA-256: `b643f0f6e4b56118846938b88a1ae79ef2b1849df9e9a3440a9ac88a10e94782`
- Reuse SHA-256: `19872ac16a67bc3ea3a212b30a07626dc48019b0cae6c060875166fef22aec8a`

Hash-verified prior interpretation:

P16Vector n is the type Fin n -> Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D003: `HighamBench.p16FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `8d9bc1fb5d3aea537c8f14c86cc475e387a8c8a49dd453f1e630adb1f5aff2bd`
- Reuse SHA-256: `b968d3a2d0b45b1c3bf872da03cf05ecd6e09846c7ca209f6de536aaebd13f35`

Hash-verified prior interpretation:

p16FrobNorm applies the Frobenius norm supplied by Matrix.frobeniusNormedRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p16MatVec`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `633fcb3583fab70e7665e594e28a11707a692d4c14a396ea9eeda2a3724f56b9`
- Reuse SHA-256: `ff61cd54b2ec6eda5a9aa8f0b8e7ac6124d874c58611d023d605d8aca8648075`

Hash-verified prior interpretation:

p16MatVec A x has component i equal to the sum over all j of A(i,j)x(j).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `HighamBench.p16Residual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `b6efd2406b4d95a62ec33a870000fff88d929437b9b4152b36fbbe02063a3602`
- Reuse SHA-256: `f906373fd2ae4ff969973499f24b761ed6e98a372af4eb6998334f4b5d8abdd6`

Hash-verified prior interpretation:

p16Residual A b x is b minus p16MatVec A x.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HighamBench.p16VecNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `bd8e44de2b8f8d577e4ee9f3b2ffb202461eebd6324f041a2f505422a111cd66`
- Reuse SHA-256: `0717e41ab5cb58bb622c1c63a16b5ff5f5a9455c6762036fdfce96e9ecf4b61f`

Hash-verified prior interpretation:

p16VecNorm x is sqrt(sum_i x(i)^2), the Euclidean norm of a finite real vector.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `1b28ff1a13cdf22d721caa93338abd5249cc7eb6f507dc6a5d633ea83e0c97a0`

Hash-verified prior interpretation:

Eq is propositional equality.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `8dcc862934e50ebf52b2b22198fed54e8ab013a6fd46ca91fdb33543c1ea0b16`

Hash-verified prior interpretation:

Fin n is the finite index type with n elements.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `bccb905728e8370e9646c7cccd463eb104efee7e96471aa6510146b7fcf77fee`

Hash-verified prior interpretation:

HAdd.hAdd dispatches to the selected addition instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `e3fb17553b22af68df8488c36c71052c60e9c389ca88004e2bb2cf667510eb7a`

Hash-verified prior interpretation:

HMul.hMul dispatches to the selected multiplication instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `adaadd5a45ad958bddb10734504475e455bf07e82d84ca9e6e3ebd74abda5ac9`

Hash-verified prior interpretation:

HSub.hSub dispatches to the selected subtraction instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `ea124e0d69b6ba17a9979326f7858d534d4a01dd8439b0b310a00ad2dee63b4c`

Hash-verified prior interpretation:

LE.le dispatches to a type's non-strict order relation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `73632ee922d91d34ae71cd78e7e89f4e2bf5221aa8e186af6381b6d23548bb4d`

Hash-verified prior interpretation:

Nat supplies the finite dimension parameter n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `b8594a4d74ac5558b8c0e4cee5af36c8130e176fdf406e80e613d0a29b0e29b2`

Hash-verified prior interpretation:

OfNat.ofNat interprets a natural-number literal in its inferred type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`
- Reuse SHA-256: `048425a1c3d89af78c873e35b5c4c8280a64d693e32a16d77ec4ca131ec5f402`

Hash-verified prior interpretation:

Pi.instAdd defines addition of functions pointwise.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5deaec32b4deac749a5db5453affea1938386e569380df7daeec26aee3cfd7c2`
- Reuse SHA-256: `7e4f54c474d01cbba73c4a3f68dedc22003a9f5579c34593237a3b13edeb1ef4`

Hash-verified prior interpretation:

Pi.instSub defines subtraction of functions pointwise.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `5f86846e758b697eea44a7e2793f96c369383d12c9c1d520b9a92ee27556a4b9`

Hash-verified prior interpretation:

Real is the scalar type of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `1c8623bbc1d69b0b4e474e73fb9ffd8f97fe69f0d8002ac114c8f80dc8caa443`

Hash-verified prior interpretation:

Real.instAdd supplies ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `f8156622ee780098421319cab2e680ca5557860f91b3a88e807eec8db9254fff`

Hash-verified prior interpretation:

Real.instLE supplies the usual order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `d78c1d7de8cc0fbb7f498f83fbdcc666ccdb17eeaf9034440b7b837a0447ab1e`

Hash-verified prior interpretation:

Real.instMul supplies ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `28a669ed7a7717bf0f62d90816c993d69673b0f934f46ace8b2b98e2b5548095`

Hash-verified prior interpretation:

Real.instSub defines a-b as a plus the negation of b.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instZero`

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

### D023: `Zero.toOfNat0`

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

### D024: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `6f0b19eff9ebf3c2664ae08b235007344f6c38235439d850bf0e8e979215f44a`

Hash-verified prior interpretation:

instHAdd converts an Add instance into homogeneous addition notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `05f8c242dd596b816b6c96854cd7888a2a0768b6ab28d3cc9ec42a0447fe49de`

Hash-verified prior interpretation:

instHMul converts a Mul instance into homogeneous multiplication notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `03db5e104fae2e6d0b6d747d3f243e737ed111811b0058be4425dae27798a6df`

Hash-verified prior interpretation:

instHSub converts a Sub instance into homogeneous subtraction notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `9028a532713e80ab1a2b3f461ff6d5ef04b60d38ea399e980b3219193c78f062`

Hash-verified prior interpretation:

Fin.fintype enumerates all members of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `29637ebea8600e099502e2c7db27e26068841b836d60078d369515ba3dea2695`

Hash-verified prior interpretation:

Finset.sum is finite commutative-monoid summation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `3e78b95fdaa9f3a25cc2fd6455bddd07d074919616e47aa4d040f9373cd3a6e3`

Hash-verified prior interpretation:

Finset.univ is the finite set of every element of a Fintype.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `cfe780d5fbbbc0ab92d3c7ad9aaa01ffd7ac8a292473edec0fa1918a1094b0d4`

Hash-verified prior interpretation:

HPow.hPow dispatches exponentiation to the selected power instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `2b777d035e0442642a6626788335aacf6f75de997efe3278638f4e153deb6c9e`

Hash-verified prior interpretation:

Matrix m n alpha is the function type m -> n -> alpha.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`
- Reuse SHA-256: `dc3e854d5fca03969d59a3097d29ac7c1a91e08530894defba0c2fde01075475`

Hash-verified prior interpretation:

This instance equips finite square matrices over an RCLike scalar with the Frobenius norm and ring operations.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `15956c316c87873cd8a5f65e4a06236bc1e00f8b12290d7b29e05f235c269b15`

Hash-verified prior interpretation:

Monoid.toNatPow supplies natural-number powers through repeated multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`
- Reuse SHA-256: `788fb8f3bef930cf7ff184a094e9e72b0e0481e8b6a96ce307ad91be2b22a7d1`

Hash-verified prior interpretation:

Norm.norm extracts the real-valued norm function from a Norm instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`
- Reuse SHA-256: `08a5acf08699207ce0cadcdca3b16fbc233b269b15e46e9963b55b3be607e0ee`

Hash-verified prior interpretation:

NormedRing.toNorm projects the norm structure from a normed ring.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `9d96c20e98e967619a3ed7aa8ac05520301970948f4f09b689c732cbf6be7050`

Hash-verified prior interpretation:

This instance supplies zero, addition, associativity, and commutativity for finite real sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `6cf22d455b7f8ebfec62855a70ce41a526711be7727e9345fa384f7d38c37e6c`

Hash-verified prior interpretation:

This instance supplies real multiplication, one, and natural powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`
- Reuse SHA-256: `5715ed812e95f5837f773fb62677c21c46f8353eef90aaef46757edfc7a68103`

Hash-verified prior interpretation:

Real.instRCLike equips Real with the analytic and normed-field structure needed by the matrix Frobenius instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `1c922958a8d6b1a22d355d9a74849b5a92c7fbb78a07b137591056fe2ea68f2b`

Hash-verified prior interpretation:

Real.sqrt is the nonnegative real square-root function.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`
- Reuse SHA-256: `d71c379c0fee0456d0ab514f981cd7db5462e7ef21cc27a4ee48aaef2ce71955`

Hash-verified prior interpretation:

instDecidableEqFin decides equality of finite indices.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D041: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `7257bf463c1dc11605a76a2b99985cc2bfaee67b31ae5823beeaa4f413438044`

Hash-verified prior interpretation:

instHPow converts a Pow instance into homogeneous exponentiation notation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D042: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `fb29da88daaa41e54a252f4cfd720515a00510f989a752e6d9045d940d8fcc1e`

Hash-verified prior interpretation:

instOfNatNat interprets a natural-number literal as that natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
