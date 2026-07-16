# Higham Chapter 24 Source Inventory

## Audit basis

- Audit date: 2026-07-16.
- Primary source: `References/1.9780898718027.ch24.pdf`, SHA-256 `1D521873129DDF07737BF9DB2C166D003B8F1E37CEF3118303F53FB6E10935B1`.
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 24, “The Fast Fourier Transform and Applications,” printed pp. 451-457, PDF pages 1-7.
- Inspection: all seven pages were text-extracted and visually checked from rendered page images, including Figure 24.1, notes, and the Problems page.
- Mode: core. Named results, printed equations, exact algorithms, and precise quantitative prose are selected. Empirical plots, notes, and the optional exercise are accounted for but excluded.

The selected-scope gate is **FAIL** only at Theorem 24.3's structured
mixed-stability reduction.
Exact DFT/inverse foundations, a literal
recursive radix-2 executor and its canonical-DFT correctness theorem, a rounded
executor, exact source and computed butterfly/stage matrices, all four
spectral-norm identities in (24.3), the complete weight-induced stage
perturbation (24.4), the literal `Fₙ=Aₜ⋯A₁Pₙ` factorization, the scalar
product bound in (24.5), circulant closure, DFT
diagonalization, the exact four-stage circulant solver, and the algebra of
(24.8) are proved. Theorem 24.1 is closed with an explicit ordered stage product
and bit-reversal permutation. The rounded claims are closed at their strongest
honest explicit domains: `Higham24ExplicitStageExecution` exposes exact and
computed intermediate states plus only local stage inequalities;
`higham24_theorem24_2_explicitDomain` derives the printed accumulated bound.
Equations (24.6)-(24.7) are produced from the literal forward executor:
an input-dependent, zero-safe rank-one `ΔF` has the printed spectral-norm
budget, and `higham24LiteralEq24_7Execution` instantiates both forward stages.
The remaining two solver stages are also literal: componentwise
`fl_complexDiv` produces the diagonal `E`, and a conjugated forward radix-2
execution produces the inverse-FFT perturbation with its sharp `n⁻¹f(n,u)`
budget. `higham24LiteralRoundedCirculantSolveExecution` composes all four
actual stages. The quantitative backward-stability consequence after Theorem
24.2 is closed by exact forward/inverse DFT norm scaling.
`Higham24MixedStabilityExecutionFamily` separates FFT,
six-scalar-rounding, and quadratic components, and
`higham24_theorem24_3_explicitDomain` proves the printed `O(u²)` conclusion.

## Named results

| Source row | Location | Decision | Evidence and status |
|---|---|---|---|
| Theorem 24.1, Cooley-Tukey radix-2 factorization (24.1) | printed p. 452 / PDF 2 | FORMALIZE_CORE | `higham24_theorem24_1_stage_factorization` proves `Fₙ=(Aₜ⋯A₁)Pₙ` on explicit binary indices. `higham24BinaryTopStageMatrix`, the `I₂⊗M` lift, and `higham24BinaryStageProduct` transparently expand the ordered source stages; `higham24BitReversalMatrix` is the printed input permutation. **PASS**. |
| Theorem 24.2, FFT relative forward-error bound | printed p. 453 / PDF 3 | FORMALIZE_CORE | `higham24_theorem24_2_literal` proves the printed `tη/(1-tη)` endpoint directly for `higham24RoundedRadix2FFT`. Primitive complex rounding produces the arithmetic perturbation, the computed-weight absolute-stage estimate is proved, and a recursive Euclidean induction yields the bound without a trace hypothesis. **PASS**. |
| Theorem 24.3, Yalamov structured mixed stability | printed p. 456 / PDF 6 | FORMALIZE_CORE / CORE-NAMED-RESULT | The exact (24.8) algebra is proved, but `Higham24MixedStabilityExecutionFamily` assumes the FFT/scalar splits and bounds. Its exact-zero witness is not the rounded solver. **OPEN / CONDITIONAL TRANSFER**. |

## Printed equation tags

| Tag | Location | Role | Evidence and status |
|---|---|---|---|
| (24.1) | p. 452 / PDF 2 | Radix-2 factorization | `higham24_theorem24_1_stage_factorization` proves the literal ordered stage-matrix/bit-reversal product and `higham24_binaryStageProduct_mulVec` identifies it with the recursive executor. **PASS**. |
| (24.2) | p. 452 / PDF 2 | Computed-weight additive error | `Higham24WeightApproximation`, `higham24_eq24_2_error_bound`. **PASS**. |
| (24.3) | p. 453 / PDF 3 | Stage and absolute-stage 2-norm identities | `higham24_butterfly_norm`, `higham24_stage_norm`, `higham24_abs_butterfly_norm`, and `higham24_abs_stage_norm` prove `‖B‖₂=‖Aₖ‖₂=√2` and `‖|B|‖₂=‖|Aₖ|‖₂=2`; the entrywise-modulus identifications are explicit. **PASS**. |
| (24.4) | p. 453 / PDF 3 | Weight-induced stage perturbation | `higham24_eq24_4` constructs the computed stage and explicit `ΔAₖ`, proves `Ãₖ=Aₖ+ΔAₖ`, and derives `‖ΔAₖ‖₂≤μ‖Aₖ‖₂` from the (24.2) weight certificates. **PASS (EXPLICIT-DOMAIN `1≤k≤t`)**. |
| (24.5) | p. 453 / PDF 3 | Accumulated product error | `higham24_eq24_5_product_bound` proves the scalar product estimate and `higham24_roundedRadix2FFT_euclidean_forward_bound` supplies its literal rounded-executor premise recursively. **PASS**. |
| (24.6) | p. 455 / PDF 5 | Equivalent DFT perturbation form and `f(n,u)` | `higham24LiteralForwardPerturbation` is the zero-safe rank-one matrix `e xᴴ/‖x‖₂²` for the actual literal output error. `higham24_literalForwardFFT_representation` proves the exact matrix action, and `higham24_literalForwardPerturbation_norm_le` proves `‖ΔF‖₂≤√n·tη/(1-tη)` using the proved `‖Fₙ‖₂=√n`; the `x=0` case is derived from the literal error theorem. **PASS**. |
| (24.7) | p. 455 / PDF 5 | First two FFT solver stages | `higham24LiteralEq24_7Execution` instantiates both `d̂=(Fₙ+ΔF₁)c` and `ĝ=(Fₙ+ΔF₂)b` with separate perturbations produced by the literal rounded radix-2 executor and the (24.6) budget. **PASS**. |
| (24.8) | p. 455 / PDF 5 | Rearranged perturbed system | `higham24_eq24_8_matrix_identity` and `higham24_eq24_8` prove the noncommutative matrix/vector identity from explicit two-sided inverse premises. **PASS (EXPLICIT-DOMAIN)**. |

## Other source content

| Content | Location | Decision | Status |
|---|---|---|---|
| DFT definition `F_n` and `y=F_n x` | p. 452 / PDF 2 | FORMALIZE_CORE | `higham24DFT`, `higham24DFTApply`; **PASS**. |
| Inverse transform `F_n⁻¹=n⁻¹F_n*` and round trip | p. 454 / PDF 4 | FORMALIZE_CORE | Reuses the Chapter 9 roots-of-unity Gram proof; both inverse products and round trips are proved. **PASS**. |
| Backward-stability consequence after Theorem 24.2 | p. 453 / PDF 3 | FORMALIZE_CORE | `higham24_dftInverse_l2_opNorm`, `higham24_dftApply_finEuclideanNorm_eq`, and `higham24_dftInverseApply_finEuclideanNorm_eq` prove the scaled-isometry laws. `higham24_dft_backwardPerturbation_relative_norm` proves equality of the relative input/output errors, and `higham24_literalFFT_backward_stable` transfers the literal Theorem 24.2 coefficient. **PASS**. |
| Figure 24.1 MATLAB experiment | p. 454 / PDF 4 | EXCLUDED-EMPIRICAL | Accounted for; no executable source data or script is printed. |
| Circulant definition and generator | pp. 454-455 / PDFs 4-5 | FORMALIZE_CORE | `higham24Circulant`, first-column and injectivity theorems. **PASS**. |
| DFT diagonalization and eigenvalues `d=F_n c` | p. 455 / PDF 5 | FORMALIZE_CORE | `higham24_dft_mul_circulant` and `higham24_circulant_diagonalization` prove `F_n C(c) F_n⁻¹ = diag(F_n c)` for the local sign/index convention. **PASS**. |
| Four-stage FFT circulant solver | p. 455 / PDF 5 | FORMALIZE_CORE | `higham24ExactCirculantSolve` implements `d=F_n c`, `g=F_n b`, pointwise `h=D⁻¹g`, and `x=F_n⁻¹h`; `higham24_exactCirculantSolve_correct` proves `C(c)x=b` when every Fourier eigenvalue is nonzero. **PASS (EXPLICIT-DOMAIN)**. |
| Rounded four-stage FFT circulant solver | pp. 455-456 / PDFs 5-6 | FORMALIZE_CORE | `higham24LiteralRoundedCirculantSolve` performs both literal forward FFTs, literal rounded complex divisions, and the literal conjugated-forward inverse FFT. `higham24LiteralRoundedCirculantSolveExecution` produces `Δ₂`, `E`, and `Δ₃` from those operations under computed-diagonal nonbreakdown; `higham24_literalRoundedCirculantSolve_composed` proves the exact composed matrix expression. The inverse stage additionally has the sharp printed `n⁻¹f(n,u)` bound. **PASS (ALGORITHM / LOCAL PERTURBATIONS)**. |
| Circulant closure/commutativity | structural content of §24.2 | FORMALIZE_CORE | `higham24_circulant_add`, `higham24_circulant_mul`, and `higham24_circulant_mul_comm`. **PASS**. |
| Forward-error prose after Theorem 24.3 | p. 456 / PDF 6 | DEFER / DEFER-MISSING-PRECISE-STATEMENT | The source says only “a multiple of `kappa_2(C)u`” and prints no multiplier or quantified neighborhood. **DEFERRED**. |
| §24.3 Notes and References | pp. 456-457 / PDFs 6-7 | EXCLUDED-BIBLIOGRAPHIC | Accounted for. |
| Problem 24.1, high-precision convolution | p. 457 / PDF 7 | EXCLUDED-OPTIONAL-EXERCISE | Accounted for; not required to support a selected closed row. |

No mathematical footnote was found. The repeated download notice is not
chapter content.
