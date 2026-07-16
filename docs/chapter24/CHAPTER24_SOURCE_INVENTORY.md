# Higham Chapter 24 Source Inventory

## Audit basis

- Audit date: 2026-07-16.
- Primary source: `References/1.9780898718027.ch24.pdf`, SHA-256 `1D521873129DDF07737BF9DB2C166D003B8F1E37CEF3118303F53FB6E10935B1`.
- Book: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 24, “The Fast Fourier Transform and Applications,” printed pp. 451-457, PDF pages 1-7.
- Inspection: all seven pages were text-extracted and visually checked from rendered page images, including Figure 24.1, notes, and the Problems page.
- Mode: core. Named results, printed equations, exact algorithms, and precise quantitative prose are selected. Empirical plots, notes, and the optional exercise are accounted for but excluded.

The selected-scope gate is **PASS**. Exact DFT/inverse foundations, a literal
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
Equations (24.6)-(24.7) use nonvacuous matrix-perturbation and four-stage
execution contracts. `Higham24MixedStabilityExecutionFamily` separates FFT,
six-scalar-rounding, and quadratic components, and
`higham24_theorem24_3_explicitDomain` proves the printed `O(u²)` conclusion.

## Named results

| Source row | Location | Decision | Evidence and status |
|---|---|---|---|
| Theorem 24.1, Cooley-Tukey radix-2 factorization (24.1) | printed p. 452 / PDF 2 | FORMALIZE_CORE | `higham24_theorem24_1_stage_factorization` proves `Fₙ=(Aₜ⋯A₁)Pₙ` on explicit binary indices. `higham24BinaryTopStageMatrix`, the `I₂⊗M` lift, and `higham24BinaryStageProduct` transparently expand the ordered source stages; `higham24BitReversalMatrix` is the printed input permutation. **PASS**. |
| Theorem 24.2, FFT relative forward-error bound | printed p. 453 / PDF 3 | FORMALIZE_CORE | `higham24RoundedRadix2FFT` is a literal rounded recursion and `higham24_roundedButterfly_pointwise_error_bound` connects one butterfly to primitive complex rounding. On the explicit stage domain, `higham24_theorem24_2_explicitDomain` derives the printed `tη/(1-tη)` endpoint from local inequalities; `higham24ExactStageExecution` proves nonvacuity. **PASS (EXPLICIT EXECUTION DOMAIN)**. |
| Theorem 24.3, Yalamov structured mixed stability | printed p. 456 / PDF 6 | FORMALIZE_CORE / CORE-NAMED-RESULT | `higham24_eq24_8` proves the exact rearrangement. `Higham24MixedStabilityExecutionFamily` exposes the FFT, six-scalar-rounding, and remainder components, including an actual `IsBigO` field; `higham24_theorem24_3_explicitDomain` derives `η log₂(n)+6u+O(u²)`, and the exact-zero family is a concrete witness. **PASS (EXPLICIT ASYMPTOTIC EXECUTION DOMAIN)**. |

## Printed equation tags

| Tag | Location | Role | Evidence and status |
|---|---|---|---|
| (24.1) | p. 452 / PDF 2 | Radix-2 factorization | `higham24_theorem24_1_stage_factorization` proves the literal ordered stage-matrix/bit-reversal product and `higham24_binaryStageProduct_mulVec` identifies it with the recursive executor. **PASS**. |
| (24.2) | p. 452 / PDF 2 | Computed-weight additive error | `Higham24WeightApproximation`, `higham24_eq24_2_error_bound`. **PASS**. |
| (24.3) | p. 453 / PDF 3 | Stage and absolute-stage 2-norm identities | `higham24_butterfly_norm`, `higham24_stage_norm`, `higham24_abs_butterfly_norm`, and `higham24_abs_stage_norm` prove `‖B‖₂=‖Aₖ‖₂=√2` and `‖|B|‖₂=‖|Aₖ|‖₂=2`; the entrywise-modulus identifications are explicit. **PASS**. |
| (24.4) | p. 453 / PDF 3 | Weight-induced stage perturbation | `higham24_eq24_4` constructs the computed stage and explicit `ΔAₖ`, proves `Ãₖ=Aₖ+ΔAₖ`, and derives `‖ΔAₖ‖₂≤μ‖Aₖ‖₂` from the (24.2) weight certificates. **PASS (EXPLICIT-DOMAIN `1≤k≤t`)**. |
| (24.5) | p. 453 / PDF 3 | Accumulated product error | `higham24_eq24_5_product_bound` proves the scalar product lemma; `higham24_theorem24_2_explicitDomain` derives the final inequality from the local stage contract. **PASS (EXPLICIT EXECUTION DOMAIN)**. |
| (24.6) | p. 455 / PDF 5 | Equivalent DFT perturbation form and `f(n,u)` | `higham24Eq24_6Bound`, its nonnegativity theorem, `Higham24FFTMatrixPerturbation`, and `higham24_eq24_6_exact_witness` give the exact representation, budget, and concrete witness. **PASS (EXPLICIT MATRIX-PERTURBATION DOMAIN)**. |
| (24.7) | p. 455 / PDF 5 | First two FFT solver stages | `Higham24Eq24_7Execution` and `higham24_eq24_7_explicitDomain` expose both computed FFT vectors, perturbation matrices, and spectral-norm budgets. `Higham24RoundedCirculantSolveExecution` covers scaling and inverse FFT and composes to the (24.8) matrix formula; exact-zero witnesses prove nonvacuity. **PASS (EXPLICIT EXECUTION DOMAIN)**. |
| (24.8) | p. 455 / PDF 5 | Rearranged perturbed system | `higham24_eq24_8_matrix_identity` and `higham24_eq24_8` prove the noncommutative matrix/vector identity from explicit two-sided inverse premises. **PASS (EXPLICIT-DOMAIN)**. |

## Other source content

| Content | Location | Decision | Status |
|---|---|---|---|
| DFT definition `F_n` and `y=F_n x` | p. 452 / PDF 2 | FORMALIZE_CORE | `higham24DFT`, `higham24DFTApply`; **PASS**. |
| Inverse transform `F_n⁻¹=n⁻¹F_n*` and round trip | p. 454 / PDF 4 | FORMALIZE_CORE | Reuses the Chapter 9 roots-of-unity Gram proof; both inverse products and round trips are proved. **PASS**. |
| Backward-stability consequence after Theorem 24.2 | p. 453 / PDF 3 | FORMALIZE_CORE | `higham24DFTBackwardPerturbation` and `higham24_dft_backward_error_representation` prove the exact inverse-transformed backward perturbation identity; its quantitative premise is the explicit-domain Theorem 24.2 endpoint. **PASS (EXPLICIT EXECUTION DOMAIN)**. |
| Figure 24.1 MATLAB experiment | p. 454 / PDF 4 | EXCLUDED-EMPIRICAL | Accounted for; no executable source data or script is printed. |
| Circulant definition and generator | pp. 454-455 / PDFs 4-5 | FORMALIZE_CORE | `higham24Circulant`, first-column and injectivity theorems. **PASS**. |
| DFT diagonalization and eigenvalues `d=F_n c` | p. 455 / PDF 5 | FORMALIZE_CORE | `higham24_dft_mul_circulant` and `higham24_circulant_diagonalization` prove `F_n C(c) F_n⁻¹ = diag(F_n c)` for the local sign/index convention. **PASS**. |
| Four-stage FFT circulant solver | p. 455 / PDF 5 | FORMALIZE_CORE | `higham24ExactCirculantSolve` implements `d=F_n c`, `g=F_n b`, pointwise `h=D⁻¹g`, and `x=F_n⁻¹h`; `higham24_exactCirculantSolve_correct` proves `C(c)x=b` when every Fourier eigenvalue is nonzero. **PASS (EXPLICIT-DOMAIN)**. |
| Circulant closure/commutativity | structural content of §24.2 | FORMALIZE_CORE | `higham24_circulant_add`, `higham24_circulant_mul`, and `higham24_circulant_mul_comm`. **PASS**. |
| Forward-error prose after Theorem 24.3 | p. 456 / PDF 6 | DEFER / DEFER-MISSING-PRECISE-STATEMENT | The source says only “a multiple of `kappa_2(C)u`” and prints no multiplier or quantified neighborhood. **DEFERRED**. |
| §24.3 Notes and References | pp. 456-457 / PDFs 6-7 | EXCLUDED-BIBLIOGRAPHIC | Accounted for. |
| Problem 24.1, high-precision convolution | p. 457 / PDF 7 | EXCLUDED-OPTIONAL-EXERCISE | Accounted for; not required to support a selected closed row. |

No mathematical footnote was found. The repeated download notice is not
chapter content.
