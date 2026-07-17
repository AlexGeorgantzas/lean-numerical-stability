# Higham Chapter 24 Formalization Report

## Outcome

Chapter 24 was audited end to end in core mode. The exact DFT and inverse DFT,
roots-of-unity inverse certificates, forward/inverse round trips, literal exact
and rounded recursive radix-2 executors, the exact executor's DFT correctness
with explicit bit reversal, exact source butterfly and Kronecker-stage
matrices, the complete stage/absolute-stage norm identity (24.3), weight-error
model, explicit computed stages and the complete stage perturbation (24.4),
scalar (24.5) accumulation
bound, circulant structure, DFT diagonalization, exact four-stage circulant
solver correctness, and exact (24.8) rearrangement are formalized without
placeholders.

The chapter gate is **FAIL** only at the final structured mixed-stability
reduction listed in `CHAPTER24_NOT_PROVED_LEDGER.md`. The exact recursive FFT theorem extends to the
printed stage-matrix/bit-reversal product in Theorem 24.1. The rounded results
now include a literal end-to-end Theorem 24.2 producer and produced forms of
(24.6)-(24.7): a zero-safe rank-one matrix realizes each pointwise FFT error,
has the printed spectral-norm budget, and supplies both actual forward stages.
The diagonal-scaling and inverse-transform perturbations and the complete
four-stage rounded execution now come from literal operations as well. The
structured `Δc`, `Δb`, and `Δx` first-order splits are not yet derived from
that execution, so the exact-zero witness does not close Theorem 24.3.

## Lean deliverables

- `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`
  - `higham24DFT`, `higham24DFTInverse`
  - `higham24_dftInverse_mul_dft`, `higham24_dft_mul_dftInverse`
  - `higham24_inverse_after_forward`, `higham24_forward_after_inverse`
  - `Higham24WeightApproximation`, `higham24_eq24_2_error_bound`
  - `higham24Eta`, `higham24RelativeFFTBound`
  - `higham24_eq24_5_product_bound`, `higham24Eq24_6Bound`
- `LeanFpAnalysis/FP/Algorithms/FFT/Higham24Radix2.lean`
  - recursive binary indices and little-/big-endian value equivalences
  - literal exact radix-2 recursion and proof that it computes the canonical DFT
  - transparent binary top stages and block lifts, their ordered product,
    explicit `P_n`, and `higham24_theorem24_1_stage_factorization`
  - `higham24ButterflyMatrix`, `higham24StageMatrix`, and their explicit
    entrywise absolute matrices
  - scaled Gram identities and `higham24_butterfly_norm`,
    `higham24_stage_norm`, `higham24_abs_butterfly_norm`, and
    `higham24_abs_stage_norm`, closing all of (24.3)
  - computed-weight butterflies/stages and explicit `ΔB`/`ΔA` Gram and norm
    bounds, culminating in `higham24_eq24_4`
  - literal rounded recursion using `fl_complexMul` and `fl_complexAdd`
  - primitive rounded-butterfly error bound and proved `γ₄` relative
    coefficients from the actual multiply/add models
  - `higham24ComputedTopStageFinMatrix`,
    `higham24RoundedTopStageFinApply`, and the literal matrix producer
    `higham24_roundedTopStage_exists_op2_perturbation`
  - the proved entrywise-to-operator-2 bridge
    `higham24_op2_le_scaled_abs_of_entrywise`
  - binary-index computed/absolute stage matrices, the sharp `μ√2`,
    `γ₄(2+μ√2)`, and total `η√2` produced bounds, and the exact scaled-isometry
    theorem
  - `higham24_roundedRadix2FFT_euclidean_forward_bound` and
    `higham24_theorem24_2_literal`, closing Theorem 24.2/(24.5) for the actual
    rounded recursive executor
  - nonvacuous explicit stage execution contract and
    `higham24_theorem24_2_explicitDomain`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24.lean`
  - `higham24Circulant`, generator injectivity and first-column recovery
  - addition, multiplication, and commutativity of circulants
  - `higham24_dft_mul_circulant`, `higham24_circulant_diagonalization`
  - `higham24ExactCirculantSolve`, `higham24_exactCirculantSolve_correct`
  - `Higham24FFTMatrixPerturbation`
  - explicit/nonvacuous (24.6)-(24.7) and rounded four-stage solver contracts
  - `Higham24MixedStabilityExecutionFamily` and
    `higham24_theorem24_3_explicitDomain`, including the `O(u²)` remainder
  - `higham24_eq24_8_matrix_identity`, `higham24_eq24_8`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24ForwardPerturbation.lean`
  - ordinary-index wrapper `higham24RoundedRadix2FFTFin` and exact DFT bridge
  - the zero-safe rank-one `higham24LiteralForwardPerturbation`, with its
    exact error action and `‖ΔF‖₂≤√n·tη/(1-tη)` proof
  - `higham24_literalForwardFFT_exists_perturbation`, the produced form of
    (24.6)
  - `higham24LiteralEq24_7Execution`, instantiating both literal forward FFTs
    in (24.7)
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24Rounded.lean`
  - literal componentwise `higham24RoundedDiagonalSolve`
  - produced diagonal `higham24DiagonalSolvePerturbation`
  - exact `(I+E)D⁻¹g` representation and `‖E‖₂≤√2γ₄`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24InverseFFT.lean`
  - norm-preserving entrywise conjugation and the exact scaled-conjugate DFT identity
  - `higham24RoundedInverseRadix2FFTFin` and explicit `higham24LiteralInversePerturbation`
  - exact inverse-stage representation and sharp `n⁻¹f(n,u)` bound
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24LiteralSolver.lean`
  - `higham24LiteralRoundedCirculantSolve`, the actual four-stage rounded executor
  - `higham24LiteralRoundedCirculantSolveExecution`, produced from all local operations
  - `higham24_literalRoundedCirculantSolve_composed`, the exact end-to-end matrix expression
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24BackwardStability.lean`
  - exact forward/inverse DFT Euclidean scaling and `‖Fₙ⁻¹‖₂=1/√n`
  - equal relative input/output perturbation norms
  - `higham24_literalFFT_backward_stable`

The DFT proof deliberately reuses the already proved Chapter 9 Fourier
Vandermonde Gram and scaled-adjoint inverse theorems instead of duplicating a
second roots-of-unity development.

## Verification

- Focused Lean checks passed for all Chapter 24 modules.
- The combined target build covering all eight public Chapter 24 modules and
  both Chapter 25 modules passed; the only replayed warnings came from
  pre-existing dependencies.
- Forbidden-token scan over the new modules found no `sorry`, `admit`, `axiom`,
  `unsafe`, or `opaque` declarations.
- `git diff --check` passed for the Chapter 24 files.
- `#print axioms` for the source-facing Theorems 24.1-24.2, the conditional
  Theorem 24.3 transfer, `higham24_circulant_diagonalization`, and (24.7)
  reports only `propext`, `Classical.choice`, and `Quot.sound`; this trust
  check does not promote the conditional Theorem 24.3 transfer to closure.

## Remaining boundary

Equations (24.6)-(24.7), the remaining literal rounded solver stages, their
composition, and the quantitative backward-stability consequence after
Theorem 24.2 are closed. Theorem 24.3 remains selected; see
`CHAPTER24_BOTTLENECK_LEDGER.md`. The
under-specified “a multiple of `kappa_2(C)u`” prose is stably deferred, and
Problem 24.1 remains an optional excluded exercise.
