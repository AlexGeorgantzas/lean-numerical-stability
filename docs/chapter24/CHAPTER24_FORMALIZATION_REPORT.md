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

The chapter gate is **PASS**. The exact recursive FFT theorem extends to the
printed stage-matrix/bit-reversal product in Theorem 24.1. The rounded results
are proved on visible nonvacuous execution domains: local stage inequalities
give Theorem 24.2, explicit matrix perturbations give (24.6)-(24.7), and a
componentwise asymptotic family with an actual `IsBigO` remainder gives
Theorem 24.3.

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
  - primitive rounded-butterfly error bound, nonvacuous explicit stage
    execution contract, and `higham24_theorem24_2_explicitDomain`
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

The DFT proof deliberately reuses the already proved Chapter 9 Fourier
Vandermonde Gram and scaled-adjoint inverse theorems instead of duplicating a
second roots-of-unity development.

## Verification

- Focused Lean checks passed for all Chapter 24 modules.
- The five-module Chapter 24/25 target build passed (`3052` jobs); the only
  replayed warnings came from the pre-existing Chapter 9 module.
- Forbidden-token scan over the new modules found no `sorry`, `admit`, `axiom`,
  `unsafe`, or `opaque` declarations.
- `git diff --check` passed for the Chapter 24 files.
- `#print axioms` for the source-facing Theorems 24.1-24.3,
  `higham24_circulant_diagonalization`, and (24.7) reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Remaining boundary

No precise selected row remains open. The under-specified “a multiple of
`kappa_2(C)u`” prose is stably deferred, and Problem 24.1 remains an optional
excluded exercise.
