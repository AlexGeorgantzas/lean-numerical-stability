# RandNLA CACM Proof-Source Ledger

This ledger records the front-loaded proof-source acquisition pass for the
full-paper RandNLA CACM formalization.  It complements
[`RANDNLA_CACM_THEOREM_LEDGER.md`](RANDNLA_CACM_THEOREM_LEDGER.md) and
[`RANDNLA_CACM_NOT_PROVED_LEDGER.md`](RANDNLA_CACM_NOT_PROVED_LEDGER.md):
the theorem ledger records Lean targets and hypotheses, the not-proved ledger
records open paper-level rows, and this file records where the missing
mathematics should come from before new proof infrastructure is added.

Reference paper: Petros Drineas and Michael W. Mahoney, "RandNLA:
Randomized Numerical Linear Algebra," Communications of the ACM 59(6),
80--90, 2016.  DOI: <https://dl.acm.org/doi/10.1145/2842602>.

## Closure Rule

External sources are proof guides, not hypotheses.  A source row closes only
when the cited statement has been formalized locally or replaced by a locally
proved theorem with exposed assumptions.  A paper-level theorem may not be
closed by citing a theorem number from another paper.

## Proof Completeness Classification

| Source target | Uploaded CACM proof status | Primary missing step | Proof-source status |
|---|---|---|---|
| Algorithm 1, equation (2), elementwise spectral concentration | Source outline plus citations only | Matrix-valued Bernstein/Khintchine concentration for the sampled residual | Closed locally for the hard-thresholded Drineas--Zouzias style source variant, including explicit floating-point scalar-radius corollaries; closed for a faithful nontruncated Frobenius/Markov FP corollary under the literal law \(p_{ij}=A_{ij}^2/\|A\|_F^2\); closed for a literal source-rate specialization when every nonzero entry satisfies the source-threshold identity condition \(\varepsilon/(2n)\le |A_{ij}|\); and closed at the exact finite-test Rademacher quadratic-form primitive needed by a Khintchine route. The fully unconditional sharp literal CACM equation (2) matrix-Bernstein/Khintchine theorem remains open |
| Algorithm 2, equation (5), Frobenius Gram bound | Sketch but elementary | Second-moment calculation and Markov high-probability conversion | Closed locally |
| Algorithm 2, equation (7), leverage-score subspace embedding | Citation-level survey statement | Matrix Chernoff/Bernstein or subspace-embedding theorem for leverage sampling | Closed locally in finite-Loewner Bennett sample-budget form, with exact and FP transfers; the final implementation-facing FP endpoints include the concrete `fl_sqrt(fl_mul s p_i)` leverage denominator routine, the actual-input \(A=UC\) right-congruence theorem, and the three modeled stored-basis rounded-copy paths |
| Algorithm 3 random-projection uniformization | Citation-level survey statement | FJLT/Gaussian/Rademacher/input-sparsity embedding and leverage uniformization | Closed locally for the SRHT/signed-Hadamard branch in exact-law and FP-transfer form. The deterministic square-orthogonal basis-invariance, equation (6) denominator-preservation, SRHT sign-diagonal orthogonality prerequisites, finite Rademacher sign law, probability-one signed-preprocessing support event, finite Rademacher moment identities, scalar signed-linear-form MGF/tail skeleton, scalar Hoeffding/two-sided signed-linear-form tail, coordinate-Hoeffding row-norm and leverage-probability auxiliaries, uniform one-step Loewner boundedness after the coordinate event, iid uniform sample-average concentration in tail-budget form, product-law preprocessing-plus-sampling composition, FP uniform-sketch transfer, flat-Hadamard expected squared row-norm theorem, source-directed expected Euclidean row-norm theorem, deterministic row-norm convexity and Lipschitz inputs, deterministic signed-Hadamard row-norm positive-flip self-bounding estimate, finite subgaussian Chernoff MGF-to-tail optimizer, positive-drop exponential-tilt self-bounding route, source-sharp all-row row-norm theorem, leverage-probability cap, logarithmic delta wrappers, exact SRHT-plus-uniform-row composition, source-sharp FP constant-budget transfer, computed-`Vhat` transfer surfaces, the exact-stored zero-transform-storage computed-left certificate, the exact-factor rounded signed-Hadamard preconditioner certificate, the rounded scale/sign-pattern table certificate and computed-left event wrapper, generated Sylvester/Walsh bit-parity sign-pattern certificates and computed-left event wrappers, the `fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0` stored-sign certificates and computed-left event wrappers, the scalar, vector-pair, propagated-input, ordered-schedule, one-stage generated-pair, rounded no-alias/list-order/no-touch generated-stage FHT certificates, stage-list append/range-succ, scaled-schedule, and columnwise scaled-schedule matrix FHT arithmetic adapters, the rounded sqrt-inverse FHT normalization-scale routine, the generic nonzero-error signed-Hadamard/sign-storage product certificate, the generic computed-input-basis transfer certificate, the computed-left/input computed-denominator perturbation event, the generated Sylvester/FHT stored-input multiply-one, add-zero, and subtract-zero actual-input endpoints, the computed-projector-from-basis certificate, the generic computed-denominator row-scaling transfer, the rounded-sqrt exact-input denominator certificate, the rounded division-then-square-root denominator certificate, the rounded reciprocal-multiply-then-square-root denominator certificate, the rounded split-square-root denominator certificate, the square-root-times-reciprocal-square-root denominator certificate, and the actual-input SRHT plus finite signed-mixing endpoints specialized to that concrete denominator are closed locally. The denominator, computed-input, computed-left/input, computed-projector, exact-factor, scale/sign-pattern, generated Sylvester sign-pattern, scaled-pattern event, stored-sign event, scalar/vector-pair/propagated/schedule/one-stage-generated-pair/stage-list-append-range-succ/scaled-schedule/columnwise-matrix FHT arithmetic, rounded sqrt-inverse FHT scale, stored actual-input matrix, and signed-Hadamard product transfers are algebraic or direct uses of the local `FPModel.model_mul`/`FPModel.model_add`/`FPModel.model_sub`/`FPModel.model_div`/`FPModel.model_sqrt`, finite probability, exact integer/Boolean bit operations, and matrix-product error primitives and required no external proof source. Open source rows are now non-SRHT Gaussian/FJLT/input-sparsity uniformization beyond the modeled signed-mixing and CountSketch paths, scale-normalization routines beyond the rounded sqrt-inverse FHT routine if used, layout-specific in-place overwrite, vectorized-layout, or storage certificates beyond the functional generated schedule and its same-stage no-alias/list-order/no-touch certificates, concrete QR/SVD/singular-vector routines instantiating `ComputedMatrix`, actual-input storage formats beyond the three modeled rounded-copy paths if used, sign-storage formats beyond the three modeled rounded-copy paths, and denominator-normalization routines beyond the five closed uniform-row paths. |
| Equation (8), least-squares relative error | Citation-level survey statement | Sampled-row subspace embedding, sketched minimizer theorem, and solver/preconditioner pipeline | Partially closed locally: deterministic/probability transfers, leverage equation (7) adapters, concrete sampled-row LS objective algebra, the canonical residual-coordinate bridge, the column/RHS representation adapter, the augmented-span orthonormal basis theorem for `[A b]`, the direct finite-Loewner preservation bridge, the exact/rounded-Gram augmented-span Bennett sample-budget LS theorems, the literal rounded sampled/scaled `A,b` high-probability transfer under explicit objective-budget slack, the additive solver-objective-gap transfer, the componentwise solver forward-error certificate transfer, the perturbed-Gram-system solver certificate transfer, the `LSQRSolveBackwardError` spec transfer, the rectangular perturbed-normal-equation adapter, induced Gram/RHS perturbation-budget lemmas, and the concrete normal-equations/Cholesky solver transfer are formalized. Rectangular QR/preconditioner and random-projection variants remain open |
| Equation (9), low-rank structural condition | Citation-level structural theorem | SVD/rank/projector/pseudoinverse foundation and structural low-rank proof | Open, but LR.1br now closes the local block source-SVD certificate constructor, LR.1bs closes the square-SVD split constructor, and LR.1bt closes the thin-rectangular split constructor: exact block decomposition, or supplied exact SVD-style tables split into head/tail blocks, construct the diagonal source-tail certificate and feed the scalar/relative equation-(9) surfaces. Remaining proof-source needs are actual rectangular SVD/source-split existence, singular-value positivity/order, Eckart--Young tail optimality, randomness-derived cross-term certificates, and computed non-probability SVD/projector/Gram/inverse/product routines. |
| Equations (10)--(11), matrix completion | Citation-level survey statement | Nuclear norm, incoherence, random sampling, dual certificate/recovery theorem | Open |
| Laplacian solvers and effective-resistance sparsification | Citation-level survey statement | Graph Laplacian/effective resistance/spectral sparsifier theorem and solver transfer | Open |

## Active Proof-Source Chain: LR.1 Equation (9) Source SVD and Eckart--Young

The current LR.1 red bottleneck is no longer blocked by packaging exact block
data into the diagonal source-tail certificate.  LR.1br proves that constructor
locally, LR.1bs proves the square-specialized split from a supplied exact
SVD-style table, LR.1bt proves the thin-rectangular split from a supplied
left column-orthonormal table plus full right orthogonal table, and LR.1bu
closes the strict-positive-head-to-nonzero handoff; none required an external
source.  The source-acquisition frontier is now the genuine rectangular
SVD/Eckart--Young step.  The selected route is the standard
Eckart--Young--Mirsky path: Eckart--Young's lower-rank approximation theorem
for least-squares/Frobenius approximation, Mirsky's unitarily invariant norm
extension, and a modern SVD/Eckart--Young textbook route such as Golub--Van
Loan for the rectangular SVD construction and singular-value ordering.  The
Lean frontier is to construct exact block bases and diagonal singular blocks
from such an SVD theorem, prove the remaining singular-value ordering fields,
derive the tail Frobenius norm identity from orthonormal source factors, and
then derive the tail-optimality inequality rather than assuming it.  LR.1bv
closes the local tail Frobenius norm identity: exact orthonormal source factors
preserve the Frobenius norm of the displayed singular-value block, so the
source-tail residual norm can now be rewritten as `||SigmaTail||_F` before the
future Eckart--Young lower-bound step.  LR.1bw propagates that identity to the
supplied square-SVD and thin-rectangular SVD surfaces, so their relative
wrappers can state tail optimality and scalar comparison directly with
`||squareSVDTailDiagonal sigma||_F`.  LR.1bx further strips away the
sketch/projector hypotheses from the D4 handoff: a supplied sigma-tail
optimality inequality now directly constructs the square or thin-rectangular
`IsBestRankApproxFrob` certificate.  LR.1cy closes the first rank-nullity
kernel lemma used by the standard Eckart--Young min-max lower-bound argument:
a rank-at-most-`r` matrix with `r+1` right coordinates has a nonzero
right-kernel vector.  The next proof-source target is the spectral
singular-value lower-bound step that uses this kernel vector against the
ordered singular block, before assembling the Frobenius tail-optimality
inequality.

| Step | Source | Exact location | Needed Lean target | Local status |
|---|---|---|---|---|
| LR.1-SVD-1 | Drineas--Mahoney CACM survey, DOI <https://dl.acm.org/doi/10.1145/2842602> | Equation (9) low-rank structural condition | Source-SVD split feeding the exact projector theorem | Block certificate constructor closed locally by LR.1br, supplied square-SVD split constructor closed locally by LR.1bs, and supplied thin-rectangular split constructor closed locally by LR.1bt; actual rectangular SVD/source-split existence and Eckart--Young remain open |
| LR.1-SVD-2 | Eckart--Young, "The Approximation of One Matrix by Another of Lower Rank," Psychometrika 1(3), 211--218, 1936, DOI <https://doi.org/10.1007/BF02288367>; Mirsky, "Symmetric gauge functions and unitarily invariant norms," Q. J. Math. 11(1), 50--59, 1960, DOI <https://doi.org/10.1093/qmath/11.1.50>; Golub--Van Loan, Matrix Computations, SVD/low-rank approximation chapters | Standard rectangular SVD, singular-value order/positivity, and best-rank Frobenius approximation theorem | Construct block bases `[U,Utail]`, `[Vperp,V]`, diagonal head/tail singular blocks, prove the source-tail Frobenius norm identity, construct the rank-nullity/min-max lower-bound chain, and construct `IsBestRankApproxFrob` from the SVD data | Source route selected. LR.1bu closes the elementary head-positive-to-nonzero handoff used by LR.1bs/LR.1bt; LR.1bv closes the exact source-tail norm identity under supplied orthonormal source factors; LR.1bw propagates that identity to supplied square/thin SVD relative wrappers; LR.1bx constructs the square/thin best-rank certificate from a supplied sigma-tail optimality inequality; LR.1cy closes the rank-nullity kernel lemma for the min-max lower-bound route. The actual rectangular SVD existence, singular-value ordering, full spectral/Frobenius Eckart--Young tail-optimality proof, and computed SVD/basis routines remain open |

## Active Proof-Source Chain: A3.4-B1 Source-Sharp SRHT Row Norms

This row is the proof-source acquisition checkpoint for the active red
bottleneck `A3.4-SRHT-row-norm-concentration`.  It separates the fully proved
coordinate-Hoeffding Algorithm 3 route from the sharper source route used by
Tropp's SRHT theorem.

### Paper Claim

CACM Algorithm 3 says randomized projection preprocessing can uniformize
leverage information before later row sampling.  The source-sharp SRHT version
is supplied by Tropp's analysis of the subsampled randomized Hadamard transform:
after multiplying an orthonormal-column matrix \(V\) by a random sign diagonal
and a flat orthogonal Hadamard matrix, all row norms are small with high
probability, and uniform row sampling then preserves the subspace geometry.

### Source Chain

| Step | Source | Exact location | Needed Lean target | Local status |
|---|---|---|---|---|
| A3.4-S1 | Drineas--Mahoney CACM survey, DOI <https://dl.acm.org/doi/10.1145/2842602> | Algorithm 3 and surrounding randomized projection discussion | Algorithm 3 preprocessing/uniformization theorem family, followed by exact and FP row-sketch transfers | Scoped coordinate-Hoeffding route closed locally; source-sharp SRHT exact preprocessing, exact uniform row-sampling composition, logarithmic wrapper, FP transfer, and computed-`Vhat` transfer surfaces are now closed locally |
| A3.4-S2 | Joel A. Tropp, "Improved analysis of the subsampled randomized Hadamard transform," Adv. Adapt. Data Anal. 3(1--2), 115--126, 2011; accepted preprint <https://tropp.caltech.edu/papers/Tro11-Improved-Analysis-preprint.pdf>, arXiv <https://arxiv.org/abs/1011.1595>, DOI <https://doi.org/10.1142/S1793536911000787> | Section 3.1, Theorem 3.1 | SRHT subspace embedding from row-norm uniformization plus row sampling | Exact product-law theorem, logarithmic parameter corollary, and matching source-sharp FP constant-budget transfer are closed locally for the signed-Hadamard/SRHT branch |
| A3.4-S3 | Same Tropp source | Section 3.1, Lemma 3.3 | For orthonormal-column \(V\), prove the all-row event \(\max_j\|e_j^*HDV\|_2 \le \sqrt{k/n}+\sqrt{8\log(\beta n)/n}\) with failure at most \(1/\beta\) | Closed in explicit-`t` form and logarithmic delta form by the source-sharp SRHT row-norm and leverage tails in A3.4-S24 |
| A3.4-S4 | Same Tropp source | Section 3.2, proof of Lemma 3.3 | Show \(HDV\) preserves orthonormal columns; define \(f(x)=\|e_j^*H\operatorname{diag}(x)V\|_2\); prove \(E f(\varepsilon)\le\sqrt{k/n}\) and Lipschitz constant \(1/\sqrt n\) | Orthonormality, expectation, deterministic Lipschitz, positive-drop self-bounding, and the row-specific concentration theorem are locally closed; only the fully general convex-Lipschitz proposition remains advisory |
| A3.4-S5 | Same Tropp source | Section 2.2, Proposition 2.1 | Rademacher convex-Lipschitz tail: for convex \(L\)-Lipschitz \(f\), \(P\{f(\varepsilon)\ge E f(\varepsilon)+Lt\}\le e^{-t^2/8}\) | Specialized signed-Hadamard row-norm instance is closed locally via positive-drop self-bounding and finite-cube Herbst. The fully general convex-Lipschitz proposition remains open because it is no longer needed for the Algorithm 3 SRHT row-norm theorem. |
| A3.4-S6 | Michel Ledoux, "On Talagrand's deviation inequalities for product measures," ESAIM Probab. Stat. 1, 63--87, 1997, DOI <https://doi.org/10.1051/ps:1997103>, primary PDF <https://www.esaim-ps.org/articles/ps/pdf/1997/01/ps-Vol1.4.pdf> | Introduction inequality (1.2), logarithmic Sobolev inequality (1.6), differential inequality (1.7), and Corollary 1.3 on pp. 63--70 | Source foundation for Tropp Proposition 2.1. Ledoux proves the upper tail \(P\{f\ge Ef+t\}\le e^{-t^2/2}\) for separately convex 1-Lipschitz \(f\) on \([0,1]^n\); Tropp's \(e^{-t^2/8}\) follows by the affine map \(x\mapsto 2x-1\) and scaling by \(2L\). | Advisory source constants now pinned down; the finite-vector affine scaling is formalized locally, but Ledoux's log-Sobolev/Laplace-transform concentration theorem remains open. |
| A3.4-S7 | Local `Preconditioning.lean` | `rademacherTraceProbability_expectationReal_rowNormSq_signedHadamard_eq`, `rademacherTraceProbability_expectationReal_sqrt_rowNormSq_signedHadamard_le` | Finite Rademacher expectation side of Tropp's Lemma 3.3 | Closed locally; focused module build passed |
| A3.4-S8 | Local `RowSamplingLeverage.lean`, `MatrixAlgebra.lean`, `Preconditioning.lean` | `hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq`, `hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le`, `abs_vecNorm2_sub_le_vecNorm2_sub`, `signedHadamard_row_vecNorm2_lipschitz` | Finite deterministic Lipschitz side of Tropp's Lemma 3.3 | Closed locally with two weak-component passes |
| A3.4-S9 | Local `FiniteProbability.lean` | `FiniteProbability.eventProb_real_le_ge_one_sub_exp_of_mgf_bound`, `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf` | Chernoff optimization from a centered subgaussian MGF to the one-sided tail needed after Ledoux/Talagrand | Closed locally; focused `FiniteProbability` build passed. This is only the MGF-to-tail step, not the Ledoux/Talagrand MGF estimate itself. |
| A3.4-S9a | Local `Preconditioning.lean`; finite Hoeffding/Rademacher foundation used before non-SRHT finite transform branches | `rademacherTraceProbability_eventProb_abs_sum_mul_sign_le_ge_one_sub_two_mul_exp_neg_sq_div` | Optimized two-sided Hoeffding tail for a finite Rademacher signed linear form with variance proxy \(\sigma^2\), obtained from the exact product MGF and auxiliary-parameter tail with \(\lambda=T/\sigma^2\) | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This is a reusable exact-probability scalar primitive for finite Rademacher/FJLT-style branches; it does not yet prove a row-norm, subspace-embedding, Gaussian, FJLT, or input-sparsity Algorithm 3 transform law. |
| A3.4-S9b | Local `Preconditioning.lean`; finite-family packaging for future non-SRHT finite transform branches | `rademacherTraceProbability_eventProb_forall_abs_sum_mul_sign_le_ge_one_sub_sum_two_mul_exp_neg_sq_div` | Simultaneous finite-family optimized Hoeffding bound for exact Rademacher signed linear forms, obtained by applying the local finite-probability union bound to A3.4-S9a | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This prepares row/entry-wise finite Rademacher/FJLT preprocessing arguments, but it is still not a completed transform row-norm, subspace-embedding, Gaussian, FJLT, input-sparsity, or floating-point implementation theorem. |
| A3.4-S9c | Local `Preconditioning.lean`; row-norm-shaped finite Rademacher foundation | `rademacherTraceProbability_eventProb_vecNorm2Sq_sum_mul_sign_le_ge_one_sub_sum_two_mul_exp_neg_sq_div` | Converts the finite-family signed-linear Hoeffding event into a squared Euclidean norm event for a vector of signed linear forms | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This is the next reusable exact-probability primitive toward dense finite Rademacher/FJLT row-norm preprocessing; it still does not instantiate a full transform distribution, subspace embedding, sampling composition, or floating-point implementation path. |
| A3.4-S9c2 / A1.5-KH1 | Local `Preconditioning.lean`; reusable finite-test matrix-Khintchine foundation for Algorithm 1 copy-difference routes and finite Rademacher/FJLT branches | `finiteQuadraticForm_rademacher_signed_matrix_sum_eq_sum`, `rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_le_ge_one_sub_sum_two_mul_exp_neg_sq_div` | Reduces each fixed quadratic form of an exact Rademacher signed matrix series \(\sum_k \omega_k M_k\) to a scalar signed linear form, then applies the local simultaneous two-sided Hoeffding theorem to a finite family of test vectors | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This is exact probability and exact arithmetic only: no floating-point quantity is computed at this layer, and it is not the final Algorithm 1 matrix spectral-norm tail. A future source-uniform Algorithm 1 theorem must still turn finite quadratic-form tests into the required spectral event or otherwise use a complete matrix Khintchine/Bernstein tail. |
| A1.5-KH2 | Local `Preconditioning.lean` and `ElementwiseSpectral.lean`; Algorithm 1 copy-difference Rademacherization adapter | `finiteQuadraticForm_rademacher_signed_matrix_sum_eq_sum_fintype`, `rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_fintype_le_ge_one_sub_sum_two_mul_exp_neg_sq_div`, `sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div` | Generalizes the finite-test theorem to arbitrary finite matrix index types, then instantiates it with the Algorithm 1 self-adjoint dilation index `Fin m ⊕ Fin n` and fixed stepwise independent-copy residual-increment differences | Closed locally by focused `lake env lean` checks and focused builds for `Preconditioning.lean` and `ElementwiseSpectral.lean`. This is exact probability and exact arithmetic only. It does not prove the probability tail for the all-copy-differences spectral event; it supplies the signed finite-test layer that such a tail can consume. |
| A1.5-KH3 | Local `MatrixAlgebra.lean` and `ElementwiseSpectral.lean`; finite-cover upgrade for Algorithm 1 signed copy-difference sums | `finiteUnitBallCover`, `finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm`, `rademacherTraceProbability_eventProb_rectOpNorm2Le_signed_sampleResidualIncrement_diff_ge_one_sub_sum_two_mul_exp_neg_sq_div_of_finiteUnitBallCover` | Proves a deterministic exact cover-to-Loewner bridge with radius \(\eta+L(2\rho+\rho^2)\), then composes it with A1.5-KH2 to obtain an exact Rademacher probability lower bound for a rectangular operator event for fixed signed copy-difference sums | Closed locally by focused `lake env lean` checks and focused builds for `MatrixAlgebra.lean` and `ElementwiseSpectral.lean`. This remains intermediate exact-law infrastructure: the coarse signed-dilation operator radius \(L\) is a visible deterministic input, not a probability tail or computed certificate, and the source-uniform all-copy-differences spectral event remains open. |
| A1.5-KH4 | Local `ElementwiseSpectral.lean`; literal all-copy-differences small-entry obstruction | `algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le`, `sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge`, `sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_pos`, `sqMagTraceProbability_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_delta_ge` | Shows that for the exact one-step literal input \(A=[1,(|L|+2)^{-1}]\), the residual difference between the tiny-entry trace and the unit-entry trace violates radius \(L\); under the exact squared-magnitude law, failure of the all-copy-differences event has probability at least the exact tiny-entry sampling probability, so any claimed \(1-\delta\) lower bound for that event must satisfy \(p_{\rm tiny}\le\delta\) | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/ElementwiseSpectral.lean`. This is an exact-law obstruction, not an FP theorem and not a final spectral tail. It rules out treating the literal all-copy support event as probability-one or hiding a uniform deterministic copy-difference radius for untruncated squared-magnitude sampling. |
| A1.5-KH5 | Local `FiniteProbability.lean` and `ElementwiseSpectral.lean`; sample-count small-entry obstruction for the literal exact spectral event | `FiniteProbability.prob_le_eventProb_of_mem`, `sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny`, `algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le`, `sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge`, `sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge`, `sqMagProb_algorithm1SmallEntrySupportMatrix_small_lt_one`, `log_inv_delta_le_nat_mul_log_inv_of_pow_le`, `log_inv_delta_div_log_inv_le_nat_of_pow_le`, `sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_log_delta_le`, `sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge`, `sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow`, `sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_sample_count_lt`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_lt_one`, `exists_delta_not_sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry`, `real_log_180000_le_18`, `algorithm1RectSourceBudget_1_2_100_one_div_30000`, `algorithm1SmallEntrySupportMatrix_100_small_prob_gt_one_div_30000`, `algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000`, `sqMagTraceProbability_not_algorithm1ExactSpectralEvent_rect_source_budget_witness`, `not_forall_algorithm1ExactSpectralEvent_of_rect_source_budget_one_div_30000` | Shows that for any positive sample count \(s\), the all-tiny trace of \(A=[1,(|L|+2)^{-1}]\) has exact product-law mass \(p_{\rm tiny}^s\), is outside the exact spectral event \(\|A-\widetilde A\|_{2\to2}\le L\), and therefore any \(1-\delta\) lower bound for that literal exact spectral event must satisfy \(p_{\rm tiny}^s\le\delta\). The newer success-probability surface gives \(\mathbb P(E_{\rm spec})\le1-p_{\rm tiny}^s<1\). For \(\delta>0\) and \(0<p_{\rm tiny}<1\), the formalized logarithmic forms force both \(\log(1/\delta)\le s\log(1/p_{\rm tiny})\) and \(\log(1/\delta)/\log(1/p_{\rm tiny})\le s\). The contradiction wrappers state the contrapositive forms directly: the advertised high-probability event cannot hold if \(\delta<p_{\rm tiny}^s\), if \(s<\log(1/\delta)/\log(1/p_{\rm tiny})\), or for some positive \(\delta\) at every fixed positive sample count. The concrete source-budget witness sets \(m=1,n=2,s=1,L=100,\delta=1/30000,A=[1,1/102]\), proves the rectangular source-style budget in exact arithmetic, and still proves the literal exact spectral-event lower bound impossible; the schema wrapper refutes the universal implication from that fixed source budget to the advertised success probability. | Closed locally by focused `lake env lean` checks and focused builds for `FiniteProbability.lean` and `ElementwiseSpectral.lean`. This is an exact-law/exact-arithmetic obstruction, not an FP theorem and not a final source-uniform matrix-tail proof. It strengthens A1.5-KH4 from the all-copy support event to the exact spectral event itself and makes the necessary sample-count order, success-probability cap, source-budget witness, source-budget-only schema refutation, and incompatibility form explicit. |
| A3.4-S9d | Local `Preconditioning.lean`; exact signed-mixing row-family specialization | `signedMixingRows`, `signedMixingRows_preconditionRows_entry`, `signedMixingRows_coeff_sq_sum_le_of_entry_sq_le`, `rademacherTraceProbability_eventProb_forall_rowNormSq_signedMixingRows_le_ge_one_sub_sum_sum_two_mul_exp_neg_sq_div`, `rademacherTraceProbability_eventProb_forall_rowNormSq_signedMixingRows_entry_sq_le_ge_one_sub_sum_sum_two_mul_exp_neg_sq_div`, `rademacherTraceProbability_eventProb_forall_rowNormSq_signedMixingRows_entry_sq_le_uniform_ge_one_sub_sum_sum_two_mul_exp_neg_sq_div` | Instantiates the vector-norm Rademacher primitive for a deterministic exact signed-mixing table \(\Pi_\omega(i,k)=G_{ik}\omega_k\), proves the entry expansion, derives the variance proxy from an exact coefficient cap and orthonormal columns, and gives a uniform-threshold row-norm corollary | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This is an exact-probability/exact-arithmetic preprocessing foundation for finite Rademacher/FJLT-style branches; it still does not prove a full transform distribution, subspace embedding, sampling composition, Gaussian/input-sparsity law, or floating-point implementation path for applying/storing `G`. |
| A3.4-S9e | Local `Preconditioning.lean`; exact signed-mixing first-moment normalization | `rademacherTraceProbability_expectationReal_sum_mul_sign_mul_sum_mul_sign_eq_sum_mul`, `signedMixingUniformRowSampleProbability`, `rademacherTraceProbability_expectationReal_signedMixingRows_entry_mul_eq`, `signedMixingUniformRowSampleProbability_expectationReal_uniformRowOuterGramSample_eq_id`, `signedMixingUniformRowSampleProbability_expectationReal_uniformRowOuterGramSample_eq_id_of_hasOrthonormalColumns` | Proves the cross-second-moment identity for finite Rademacher signed linear forms, then shows that exact Rademacher signs followed by one exact uniform signed-mixing row have expected one-row outer product \(I_n\), either from deterministic column-square normalization of `G` or directly from the stronger rectangular-isometry condition \(G^TG=I\), with \(U\) orthonormal | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This closes the exact mean/normalization layer for finite signed-mixing rows and aligns it with the sample-Gram composition assumptions; it still does not prove concentration, subspace embedding, sampling composition for averages, Gaussian/FJLT/input-sparsity laws, or floating-point implementation of `G`. |
| A3.4-S9f | Local `Preconditioning.lean` and `UniformRowSamplingComposition.lean`; exact signed-mixing sample-Gram composition | `signedMixingRows_preconditionRows_hasOrthonormalColumns`, `signedMixingUniformRowTraceProbability`, `signedMixingUniformRowSampleGramTwoSidedEvent`, `signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform` | Proves that exact signed mixing preserves orthonormal columns when \(G^T G=I\), then composes the exact signed-mixing row-norm event with the existing iid exact uniform row sample-Gram matrix concentration theorem under a uniform entry-square cap \(G_{ik}^2\le \alpha^2\) | Closed locally by focused `lake env lean` checks for `Preconditioning.lean` and `UniformRowSamplingComposition.lean`. This is an exact-probability/exact-arithmetic product-law theorem for rectangular-isometry signed mixing; it is not a Gaussian/FJLT/input-sparsity transform law and does not charge floating-point application/storage of `G` or rounded sample-Gram arithmetic. |
| A3.4-S9h | Local `Preconditioning.lean`; computed finite signed-mixing preconditioner formation | `preconditionRows_diagMatrix_eq_signedMixingRows`, `ComputedPreconditioner.flSignedMixing`, `ComputedPreconditioner.flSignedMixingExactFactors`, `ComputedPreconditioner.flSignedMixingExactFactors_entry_error_bound` | Bridges the exact signed-mixing table to the rectangular product \(G\operatorname{diag}(\omega)\), then constructs a concrete computed-preconditioner certificate for rounded formation of `G * diag(sign)`. The exact-factor theorem proves the componentwise bound \(\gamma_m\sum_k |G_{ik}|\,|\operatorname{diag}(\omega)_{kj}|\), which simplifies to \(\gamma_m |G_{ij}|\) for exact signs. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This charges a concrete preconditioner-formation operation for finite signed-mixing branches; it still does not by itself prove the downstream computed-`Vhat`, rounded row-scaling, rounded sample-Gram, or full Gaussian/FJLT/input-sparsity implementation theorem. |
| A3.4-S9i | Local `UniformRowSamplingFP.lean`; computed finite signed-mixing basis and sample-Gram endpoint | `signedMixingComputedLeftPreconditionedBasis`, `signedMixingComputedLeftPreconditionedBasisEntryErrorBudget`, `signedMixingExactFactorPreconditioner`, `signedMixingComputedLeftUniformRowPerturbBudget`, `signedMixingComputedLeftUniformRowComputedDenPerturbBudget`, `signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, `signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform` | Reuses S9f and S9h to close a nonconditional implementation-facing FP endpoint for exact supplied finite signed-mixing factors: exact Rademacher and uniform-row laws, rounded `G * diag(sign)` formation, rounded `Vhat = fl(Pihat * U)`, rounded row scaling, optional computed denominator, and rounded Gram dot products. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` and focused module build. This branch assumes the analysis input basis `U` is exact. Concrete computed-basis/SVD/QR routines, Gaussian/FJLT/input-sparsity transform laws, and layout-specific routines for `G` beyond the modeled rounded matrix product remain separate obligations; the actual-input right-factor congruence for the non-SRHT signed-mixing branch is closed separately in A3.4-S9j. |
| A3.4-S9j | Local `UniformRowSamplingFP.lean`; actual-input finite signed-mixing right-factor congruence and computed sample-Gram endpoint | `preconditionRows_preconditionColumns_assoc_rect`, `uniformRowSampleGram_rectFactoredInput_error_eq_rightGramCongruence_error`, `signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent`, `signedMixingUniformRowSampleGramTwoSidedEvent_subset_factoredInput`, `signedMixingUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, `signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent`, `signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget` | Transfers the exact signed-mixing sample-Gram event from the exact orthonormal analysis basis \(U\) to an actual input \(A=UC\) by right-Gram congruence, then plugs the same concrete rounded finite signed-mixing implementation into the factored-input event: rounded `G * diag(sign)`, rounded `Vhat = fl(Pihat * A)`, computed uniform denominator, rounded row divisions, and rounded length-`s` Gram dot products. The total-budget wrapper packages the same event as a direct \(1-\delta\) theorem whenever \(\delta_{\rm pre}+\delta_{\rm sample}\le\delta\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`. Exact Rademacher and uniform-row laws remain exact; \(U,C\) are analysis witnesses and are not claimed to be computed by this theorem. Concrete QR/SVD/basis-generation routines, Gaussian/full FJLT/input-sparsity transform laws, and layout-specific `G` routines remain separate obligations. |
| A3.4-S9j2 | Local `UniformRowSamplingFP.lean`; finite signed-mixing concrete denominator specialization | `uniformRowFlSqrtMulInvSqrtScaleDen`, `uniformRowFlSqrtMulInvSqrtScaleDen_den`, `uniformRowFlSqrtMulInvSqrtScaleDen_den_abs_error`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform`, `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget` | Instantiates the S9i/S9j generic computed-denominator theorem surfaces with the concrete row-scale denominator routine `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))` for the exact denominator `sqrt(s/r)`. The charged denominator error radius is `sqrt(s/r) * ((4u + 3u^2 + u^3)/(1-u))`. | Closed locally as a small adapter over the already proved computed-denominator endpoints and the square-root-times-reciprocal-square-root denominator certificate. The generic `WithComputedDen` statements remain infrastructure for other denominator routines, while these wrappers are the final concrete signed-mixing denominator surface. Exact Rademacher and uniform-row laws remain exact; all non-probability computations in this path are charged. |
| A3.4-S9k | Local `Preconditioning.lean`; finite CountSketch/input-sparsity exact first-moment and collision-free foundations | `CountSketchHash`, `countSketchRows`, `countSketchHashProbability`, `countSketchProbability`, `rowGram_preconditionRows_eq_of_left_hasOrthonormalColumns`, `preconditionRows_hasOrthonormalColumns_of_left_hasOrthonormalColumns`, `countSketchRows_preconditionRows_entry`, `countSketchRows_hasOrthonormalColumns_of_hash_injective`, `rowGram_preconditionRows_countSketchRows_eq_of_hash_injective`, `countSketchRows_preconditionRows_hasOrthonormalColumns_of_hash_injective`, `rademacherTraceProbability_expectationReal_countSketchRows_entry_mul_eq`, `rademacherTraceProbability_expectationReal_countSketchRows_rowGram_eq`, `countSketchProbability_expectationReal_rowGram_eq`, `countSketchProbability_expectationReal_rowGram_eq_id_of_hasOrthonormalColumns` | Defines the exact finite CountSketch hash law and exact sparse transform \(S_{ik}=\mathbf 1_{\{h(k)=i\}}\omega_k\), proves the sparse apply expansion, proves that Rademacher signs kill collision cross terms for a fixed hash, and packages the exact hash/sign product law to show \(\mathbb E[(SU)^T(SU)]=U^TU\), hence \(I\) for an exact orthonormal analysis basis. It also proves the deterministic collision-free route: any exact left preconditioner with orthonormal columns preserves Grams, and an injective CountSketch hash with signs satisfying \(\omega_k^2=1\) has orthonormal columns. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This is exact-probability/exact-arithmetic only. It does not yet prove a nontrivial hash-injectivity probability, CountSketch concentration, subspace embedding, uniform-row sampling composition, floating-point sparse apply/storage, or the complete input-sparsity Algorithm 3 FP endpoint. |
| A3.4-S9l | Local `UniformRowSampling.lean` and `Preconditioning.lean`; finite CountSketch pair-collision probability | `uniformRowTraceProbability_eventProb_pair_collision_eq_inv`, `countSketchHashPairCollision`, `countSketchHashPairNoCollision`, `countSketchHashProbability_eventProb_pairCollision_eq_inv`, `countSketchHashProbability_eventProb_pairNoCollision_eq_one_sub_inv` | Reuses the iid uniform row-trace product law for the CountSketch hash law and proves that for distinct input rows \(a\ne b\), \(\Pr[h(a)=h(b)]=1/r\) and \(\Pr[h(a)\ne h(b)]=1-1/r\). | Closed locally by focused `lake env lean` checks for `UniformRowSampling.lean` and `Preconditioning.lean`, focused module builds, and lookup validation. This is exact probability only; it does not prove a global injectivity probability, CountSketch concentration/subspace embedding, sparse floating-point apply/storage, row-sampling composition, or the complete input-sparsity Algorithm 3 endpoint. |
| A3.4-S9m | Local `Preconditioning.lean`; finite CountSketch global hash-injectivity union bound | `CountSketchDistinctPair`, `countSketchHashInjectiveEvent`, `countSketchHash_forall_pairNoCollision_iff_injective`, `countSketchHashProbability_eventProb_injective_ge_one_sub_pair_sum`, `countSketchDistinctPairBudget_le_square_inv`, `countSketchHashProbability_eventProb_injective_ge_one_sub_square_inv` | Defines the exact global injectivity event for a CountSketch hash, proves it is equivalent to pairwise no-collision over all distinct ordered input-row pairs, applies the finite-probability union-bound infrastructure to the exact pair-collision law, and derives the simplified lower bound \(\Pr[h\text{ injective}]\ge 1-m^2/r\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` and lookup validation. This is exact hash-law probability only. The simplified lower bound is non-vacuous when \(r>m^2\); it is a sufficient collision-free route, not CountSketch concentration/subspace embedding, sparse floating-point apply/storage, row-sampling composition, or the complete input-sparsity Algorithm 3 FP endpoint. |
| A3.4-S9n | Local `Preconditioning.lean`; finite CountSketch sparse floating-point apply foundation | `CountSketchBucket`, `countSketchBucketSize`, `countSketchBucketIndex`, `countSketchBucketExactTerm`, `fl_countSketchBucketProduct`, `fl_countSketchSparseApplyEntry`, `countSketchRows_preconditionRows_bucket_sum_eq`, `fl_countSketchSparseApplyEntry_error_bound`, `countSketchBucketAbsSum_le_column_abs_sum`, `fl_countSketchSparseApplyEntry_error_bound_of_abs_sign_le_one` | Defines the exact bucket \(B_i(h)=\{k:h(k)=i\}\), its canonical finite enumeration, the exact signed terms \(\omega_k A_{kj}\), and a concrete sparse floating-point entry routine that rounds each selected signed product and then accumulates the bucket left-to-right.  The proved componentwise error is \((u+\gamma_{b_i}+u\gamma_{b_i})\sum_{k\in B_i(h)}|\omega_k||A_{kj}|\), with the sign-magnitude corollary bounded by \((u+\gamma_{b_i}+u\gamma_{b_i})\|A_{:j}\|_1\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. Exact hash/sign laws and exact integer bucket selection remain exact by project convention; this charges only the non-probability arithmetic in one sparse CountSketch apply entry. The matrix wrapper is closed separately in A3.4-S9o; CountSketch concentration/subspace embedding, row-sampling composition, sparse Gram/sample-Gram FP endpoints, and the complete input-sparsity Algorithm 3 FP theorem remain open. |
| A3.4-S9o | Local `Preconditioning.lean`; finite CountSketch sparse floating-point matrix apply wrapper | `fl_countSketchSparseApply`, `fl_countSketchSparseApply_entry`, `fl_countSketchSparseApply_entry_error_bound`, `fl_countSketchSparseApply_entry_error_bound_of_abs_sign_le_one` | Packages the S9n sparse bucket routine into the computed matrix \(\widehat Y=\operatorname{fl}(S_{h,\omega}A)\) by defining every output entry as `fl_countSketchSparseApplyEntry`, then proves the S9n componentwise radius for all \(i,j\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` and focused module build. This is the matrix-level computed sparse apply object needed before Gram/sample-Gram analysis; it still does not prove CountSketch concentration/subspace embedding, row-sampling composition, rounded sparse Gram arithmetic, or the complete input-sparsity Algorithm 3 FP endpoint. |
| A3.4-S9p | Local `RowSamplingGram.lean` and `Preconditioning.lean`; finite CountSketch sparse floating-point Gram arithmetic | `rowSketch_abs_perturbed_le_of_abs_error`, `rowSketch_abs_perturbed_mul_sum_le_of_abs_error`, `rowSketchGram_entry_abs_error_bound_exact_of_entrywise`, `rowSketchGram_frob_abs_error_bound_exact_of_entrywise`, `fl_rowSketchGramDot`, `rowSketchGramDotRoundoffExactBudget`, `rowSketchGramAbsPerturbExactBudget`, `rowSketchGramFullAbsFpExactBudget`, `fl_rowSketchGramDot_roundoff_bound_of_abs_error`, `fl_rowSketchGramDot_abs_perturb_bound_exact`, `countSketchSparseApplyEntryFpAbsBudget`, `countSketchSparseApplyFpAbsBudget`, `fl_countSketchSparseGramDot`, `countSketchSparseGramDotRoundoffBudget`, `countSketchSparseGramApplyPerturbBudget`, `countSketchSparseGramFullFpPerturbBudget`, `fl_countSketchSparseGramDot_perturb_bound` | Adds a generic exact-only Gram-dot perturbation theorem for any computed row sketch with explicit absolute entry radius \(E\), then instantiates \(E\) with the S9n/S9o sparse CountSketch apply radius.  The resulting Algorithm 3 theorem computes \(\widehat Y=\operatorname{fl}(S_{h,\omega}A)\), then computes every entry of \(\widehat G=\operatorname{fl}(\widehat Y^T\widehat Y)\) with rounded length-\(r\) dot products, and proves a Frobenius bound against the exact \(G=(S_{h,\omega}A)^T(S_{h,\omega}A)\). | Closed locally by focused `lake env lean` checks for `RowSamplingGram.lean` and `Preconditioning.lean`, plus lookup validation after rebuilding dependent modules. This charges sparse apply arithmetic and Gram dot products without a hidden perturbation event. It still does not prove CountSketch concentration/subspace embedding, row-sampling composition after CountSketch, or the complete input-sparsity Algorithm 3 theorem. |
| A3.4-S9q | Local `Preconditioning.lean`; collision-free sparse CountSketch FP Gram probability endpoint | `countSketchBucketSize_le`, `fl_countSketchSparseGramDot_rowGram_perturb_bound_of_hash_injective`, `countSketchHashFlSparseGramDotRowGramPerturbEvent`, `countSketchHashInjectiveEvent_subset_flSparseGramDot_rowGram_perturbEvent`, `countSketchHashProbability_eventProb_flSparseGramDot_rowGram_perturb_ge_one_sub_square_inv` | Uses the exact collision-free preservation theorem to recenter S9p from \((S_{h,\omega}A)^T(S_{h,\omega}A)\) to the actual input Gram \(A^TA\).  A bucket-cardinality lemma lets `gammaValid fp m` cover every sparse bucket.  The exact hash-injectivity lower bound \(\Pr[h\text{ injective}]\ge1-m^2/r\) then transfers by event monotonicity to the computed event \(\|\widehat G-A^TA\|_F\le T_{\rm CSGram}^{\rm fp}(h)\) for a fixed exact sign vector whose entries square to one. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` and lookup validation. This is the collision-free sufficient FP endpoint for sparse Gram arithmetic and is non-vacuous only when \(r>m^2\); it is not the usual CountSketch concentration/subspace-embedding theorem, does not compose downstream row sampling after CountSketch, and does not close the complete input-sparsity Algorithm 3 theorem. |
| A3.4-S9r | Local `Preconditioning.lean`; full CountSketch hash-sign collision-free sparse Gram FP probability endpoint | `countSketchProbability`, `countSketchFlSparseGramDotRowGramPerturbEvent`, `countSketchProbability_injectiveFst_subset_flSparseGramDot_rowGram_perturbEvent`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_perturb_ge_one_sub_square_inv` | Lifts S9q from a fixed exact sign vector and hash-only probability to the actual exact product law over \((h,\Omega)\).  The event computes \(\widehat G(h,\Omega)=\operatorname{fl}(\operatorname{fl}(S_{h,\operatorname{rademacherSignVector}\Omega}A)^T\operatorname{fl}(S_{h,\operatorname{rademacherSignVector}\Omega}A))\) and bounds it against \(A^TA\) by the same explicit \(T_{\rm CSGram}^{\rm fp}(h,\operatorname{rademacherSignVector}\Omega)\).  Exact Rademacher signs square to one, so the first-coordinate injective-hash event is contained in the full hash-sign computed FP event; `FiniteProbability.prod_eventProb_fst_eq` and the S9m hash-injectivity union bound then give probability at least \(1-m^2/r\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` and focused module build. Sampling laws remain exact by project convention; all non-probability arithmetic in the event is charged. This is still a collision-free sufficient route, non-vacuous only when \(r>m^2\), not the standard CountSketch concentration/subspace-embedding theorem, downstream row-sampling composition, or the complete input-sparsity Algorithm 3 theorem. |
| A3.4-S9s | Local `RowSamplingLeverage.lean`, `UniformRowSamplingComposition.lean`, and `UniformRowSamplingFP.lean`; collision-free CountSketch plus iid uniform-row sample-Gram FP endpoint | `rowNormSq_le_one_of_hasOrthonormalColumns`, `countSketchUniformRowTraceProbability`, `countSketchUniformRowSampleGramTwoSidedEvent`, `countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent`, `countSketchSparseComputedPreconditionedBasis`, `countSketchSparseUniformRowComputedDenPerturbBudget`, `uniformRowFlSqrtMulInvSqrtScaleDen`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`, `countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta` | Proves the missing deterministic row-norm cap for orthonormal-column matrices, then uses S9k/S9m/S9r-style collision-free CountSketch preservation to instantiate the exact iid uniform-row matrix MGF theorem with radius \(L=r\). The final implementation-facing theorem computes the sparse CountSketch-preconditioned basis with `fl_countSketchSparseApply`, propagates its explicit entrywise radius through the sampled Gram, computes the uniform row-scale denominator for \(\sqrt{s/r}\) as `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`, and charges denominator formation, rounded row divisions, and rounded length-\(s\) Gram dot products. | Closed locally by focused Lean checks before full validation. Exact hash/sign/row-sampling laws remain exact. The final theorem has no perturbation-event or certificate-existence assumption and no extra `δComp`: the concrete computed-denominator perturbation event is proved with probability one, with denominator radius `sqrt(s/r) * ((4u + 3u^2 + u^3)/(1-u))`. This is still a collision-free sufficient route for an exact orthonormal analysis basis \(U\), not the standard CountSketch concentration/subspace-embedding theorem, not the actual-input right-congruence theorem, and not the complete input-sparsity Algorithm 3 theorem. |
| A3.4-S9t | Local `UniformRowSamplingFP.lean`; collision-free CountSketch actual-input right-congruence and computed sample-Gram endpoint | `uniformRowSampleGram_countSketchRectFactoredInput_error_eq_rightGramCongruence_error`, `countSketchUniformRowFactoredInputSampleGramTwoSidedEvent`, `countSketchUniformRowSampleGramTwoSidedEvent_subset_factoredInput`, `countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent`, `countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget` | Transfers the collision-free CountSketch uniform-row event from an exact orthonormal analysis basis \(U\) to an actual input \(A=UC\) by right-Gram congruence, then plugs the concrete sparse computed implementation into the factored-input event: rounded sparse CountSketch apply to \(A\), concrete denominator `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`, rounded row divisions, and rounded Gram dot products. The target-budget wrapper exposes the same event as a direct \(1-\delta\) theorem whenever \(m^2/r+\delta_{\rm sample}\le\delta\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`. Exact hash/sign/row-sampling laws remain exact; \(U,C\) are analysis witnesses and are not computed by this theorem. The denominator radius is `sqrt(s/r) * ((4u + 3u^2 + u^3)/(1-u))`, and generic `WithComputedDen` remains infrastructure for other routines. This is a collision-free sufficient route, weaker than standard CountSketch concentration/subspace embedding, and concrete QR/SVD/basis-generation routines remain separate obligations. |
| A3.4-S9ta | Local `UniformRowSamplingFP.lean`; collision-free CountSketch stored-sign actual-input right-congruence and computed sample-Gram endpoint | `countSketchSparseComputedPreconditionedBasisWithStoredSign`, `countSketchSparseUniformRowComputedDenStoredSignPerturbBudget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget` | Reuses the S9t actual-input right-congruence theorem and replaces the sparse computed basis by the stored-sign computed basis. The exact witnesses satisfy `A = U C` and `U^T U = I`; they are analysis-only. The implementation stores realized signs by one of the three modeled rounded-copy paths, computes sparse CountSketch on actual input `A` with the stored signs, uses the concrete `uniformRowFlSqrtMulInvSqrtScaleDen` denominator for \(\sqrt{s/r}\), rounds sampled-row divisions, and rounds length-`s` Gram dot products. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` before ledger promotion. Exact hash/sign/row-sampling laws remain exact. The final theorem has no extra `δComp`, perturbation-event hypothesis, or generic probability-loss assumption: the stored-sign computed perturbation event is proved with probability one by the concrete budget. The probability lower bound remains \(1-(m^2/r+\delta_{\rm sample})\), with direct target-budget wrappers for \(1-\delta\). This is collision-free and weaker than standard CountSketch concentration/subspace embedding; concrete QR/SVD routines remain separate computed-quantity obligations. |
| A3.4-S9tb | Local `UniformRowSamplingFP.lean`; collision-free CountSketch tree-reduced stored-sign actual-input right-congruence and computed sample-Gram endpoint | `countSketchSparseComputedPreconditionedBasisWithStoredSignTree`, `countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget` | Reuses the S9t actual-input right-congruence theorem and the S9zza tree-reduced stored-sign computed perturbation theorem. The exact witnesses satisfy `A = U C` and `U^T U = I`; they are analysis-only. The implementation stores realized signs by one of the three modeled rounded-copy paths, computes sparse CountSketch on actual input `A` with exact supplied per-bucket trees, uses the concrete `uniformRowFlSqrtMulInvSqrtScaleDen` denominator for \(\sqrt{s/r}\), rounds sampled-row divisions, and rounds length-`s` Gram dot products. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` before ledger promotion. Exact hash/sign/row-sampling laws and tree shapes remain exact; computed non-probability objects are the stored sign table, sparse products, tree-depth bucket accumulations, denominator, row divisions, and Gram dot products. The final theorem has no extra `δComp`, perturbation-event hypothesis, or generic probability-loss assumption. The probability lower bound remains \(1-(m^2/r+\delta_{\rm sample})\), with direct target-budget wrappers for \(1-\delta\). This is collision-free and weaker than standard CountSketch concentration/subspace embedding; concrete QR/SVD routines remain separate computed-quantity obligations. |
| A3.4-S9tc | Local `UniformRowSamplingFP.lean`; collision-free CountSketch permuted-bucket stored-sign actual-input right-congruence and computed sample-Gram endpoint | `countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted`, `countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget` | Reuses the S9t actual-input right-congruence theorem and the stored-sign permuted-bucket perturbation theorem. The exact witnesses satisfy `A = U C` and `U^T U = I`; they are analysis-only. The implementation stores realized signs by one of the three modeled rounded-copy paths, computes sparse CountSketch on actual input `A` with exact supplied per-bucket traversal orders, uses the concrete `uniformRowFlSqrtMulInvSqrtScaleDen` denominator for \(\sqrt{s/r}\), rounds sampled-row divisions, and rounds length-`s` Gram dot products. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` and refreshed module build before ledger promotion. Exact hash/sign/row-sampling laws and bucket traversal orders remain exact; computed non-probability objects are the stored sign table, sparse products, bucket accumulations in the selected order, denominator, row divisions, and Gram dot products. The final theorem has no extra `δComp`, perturbation-event hypothesis, or generic probability-loss assumption. The probability lower bound remains \(1-(m^2/r+\delta_{\rm sample})\), with direct target-budget wrappers for \(1-\delta\). Fixed bucket permutations are now closed; parallel reassociation and aliasing sparse-sketch layouts remain separate routines. |
| A3.4-S9u | Local `FiniteProbability.lean` and `Preconditioning.lean`; non-injective CountSketch second-moment sign/hash foundation | `FiniteProbability.expectationReal_indicator_eq_eventProb`, `countSketchHashProbability_expectationReal_pairCollisionIndicator_eq_inv`, `countSketchProbability_expectationReal_pairCollisionIndicator_eq_inv`, `rademacherTraceProbability_expectationReal_eq_zero_of_flip_neg`, `rademacherTraceProbability_expectationReal_sign_four_eq_zero_of_left_unpaired`, `rademacherTraceProbability_expectationReal_sign_four_eq_one_same_pair`, `rademacherTraceProbability_expectationReal_sign_four_eq_one_reversed_pair`, `rademacherTraceProbability_expectationReal_sign_pair_mul_sign_pair_eq`, `rademacherTraceProbability_expectationReal_sq_sum_distinctPair_mul_sign_pair_eq` | Adds the exact-probability and exact-Rademacher moment substrate for the standard non-injective CountSketch variance route. The indicator theorem converts exact event probabilities into real-valued indicator expectations, giving \(\mathbb E[1_{\{h(a)=h(b)\}}]=1/r\) under both the hash law and the full hash-sign product law. The flip-negation theorem and four-sign classifier prove that for ordered distinct sign pairs only identical and reversed pairs survive. The summed ordered-pair theorem states the exact second moment of \(\sum_{a\ne b} c_{ab}\omega_a\omega_b\) as the double sum with only identical/reversed ordered-pair kernels. | Closed locally by focused Lean checks and focused `Preconditioning` build. This is the next foundation for CountSketch concentration/subspace embedding beyond the collision-free route, but it is not yet the final Gram/Frobenius second-moment bound, Chebyshev embedding theorem, downstream uniform-row composition, or complete input-sparsity Algorithm 3 FP endpoint. Sampling probabilities and laws remain exact; no computed non-probability quantity is introduced in this exact moment layer. |
| A3.4-S9u2 | Local `Preconditioning.lean`; fixed-vector CountSketch quadratic-form moment foundation | `finiteQuadraticForm_rowGram_eq_vecNorm2Sq_rectMatMulVec`, `rowGram_singleton_col_eq_vecNorm2Sq`, `finiteQuadraticForm_rowGram_eq_rowGram_rectMatMulVec_singleton`, `rectMatMulVec_preconditionRows_eq_preconditionRows_rectMatMulVec`, `finiteQuadraticForm_rowGram_preconditionRows_eq_rowGram_preconditionRows_rectMatMulVec_singleton`, `finiteQuadraticForm_rowGram_preconditionRows_sub_rowGram_eq_rowGram_singleton_error`, `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le`, `countSketchAllPairs_vecCoeffSq_sum_eq_vecNorm2Sq_sq`, `countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq`, `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_vecNorm`, `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_frobNorm`, `countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub`, `countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_coeff_budget` | Specializes the exact CountSketch entry moment to the one-column matrix \(Ax\). The bridge lemmas prove \(x^T((SA)^T(SA)-A^TA)x={\rm rowGram}(S(Ax))_{11}-{\rm rowGram}(Ax)_{11}\), so the exact hash/sign law gives \(E[(x^T\Delta x)^2]\le2r^{-1}\sum_{a\ne b}((Ax)_a(Ax)_b)^2\). The readable wrappers give \(2\|Ax\|_2^4/r\) and \(2\|A\|_F^4\|x\|_2^4/r\), and the tail wrapper exposes the direct \(1-\delta\) condition \(2r^{-1}\sum_{a\ne b}((Ax)_a(Ax)_b)^2/\eta^2\le\delta\). | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` passed before ledger promotion. This is exact-probability/exact-arithmetic infrastructure, not a floating-point endpoint and not yet a uniform finite-cover/subspace-embedding theorem. Sampling laws remain exact; no computed non-probability quantity appears. |
| A3.4-S9u3 | Local `Preconditioning.lean`; finite-test CountSketch quadratic-form probability foundation | `countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_coeff_budget`, `countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_sum_coeff_budget`, `countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_vecNorm_budget`, `countSketchProbability_eventProb_forall_abs_rowGram_quadratic_error_le_ge_one_sub_sum_frobNorm_budget` | Applies the local exact finite-probability union bound to the S9u2 fixed-vector CountSketch tail. For a finite exact family \(z_\alpha\) and positive thresholds \(\eta_\alpha\), the simultaneous event \(\forall\alpha,\ |z_\alpha^T((SA)^T(SA)-A^TA)z_\alpha|\le\eta_\alpha\) has probability at least \(1-\sum_\alpha 2r^{-1}\sum_{a\ne b}((Az_\alpha)_a(Az_\alpha)_b)^2/\eta_\alpha^2\), and the target-budget wrapper turns the displayed sum into a direct \(1-\delta\) statement. Readable wrappers replace each coefficient sum by \(\|Az_\alpha\|_2^4\) or by \(\|A\|_F^4\|z_\alpha\|_2^4\). | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` passed before ledger promotion. This is exact-law/exact-arithmetic finite-test infrastructure; it introduces no computed non-probability quantities and no floating-point endpoint. It is not a uniform CountSketch embedding theorem by itself; S9u4 supplies the deterministic finite-cover-to-Loewner upgrade, while sharper matrix concentration remains open. |
| A3.4-S9u4 | Local `Preconditioning.lean` and `MatrixAlgebra.lean`; finite-cover CountSketch exact Loewner probability foundation | `countSketchRowGramFiniteTestEvent`, `countSketchRowGramTwoSidedLoewnerCoverEvent`, `countSketchRowGramFiniteTestFrobEvent_subset_twoSidedLoewnerCoverEvent`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget` | Combines the S9u3 finite-test event with the S9v exact Frobenius/Markov event and the local deterministic cover lemma `finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm`. If \(z_\alpha\) is a unit-ball cover with radius \(\rho\), \(\eta>0\), and \(L>0\), the two-sided Loewner radius is \(\eta+L(2\rho+\rho^2)\), and the failure loss is \(\sum_\alpha 2r^{-1}\sum_{a\ne b}((Az_\alpha)_a(Az_\alpha)_b)^2/\eta^2+2r^{-1}\sum_{j,\ell,a\ne b}(A_{aj}A_{b\ell})^2/L^2\). The coefficient target-budget theorem gives a direct \(1-\delta\) statement when this displayed loss is at most \(\delta\). The readable wrappers prove the sufficient loss \(\sum_\alpha2\|Az_\alpha\|_2^4/(r\eta^2)+2\|A\|_F^4/(rL^2)\) and its target-budget form. | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` passed before ledger promotion. This is exact-probability/exact-arithmetic infrastructure only; the Frobenius event supplies the coarse cover radius, so no operator-certificate existence assumption is used. It is not a floating-point endpoint and remains Markov/Frobenius-derived rather than the optimal CountSketch concentration theorem, but its readable bound is now a checked theorem surface. |
| A3.4-S9u5 | Local `Preconditioning.lean`; finite-cover CountSketch sparse Gram FP endpoint | `countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotRowGramTwoSidedLoewnerEvent`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_budget`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_vecNorm_add_frobNorm`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget` | Transfers the exact finite-cover Loewner event from S9u4 to the computed sparse CountSketch Gram object. The deterministic transfer splits \(\widehat G-A^TA=(G_{SA}-A^TA)+(\widehat G-G_{SA})\), applies the local two-sided Loewner additive perturbation lemma, and instantiates the concrete sparse Gram perturbation theorem `fl_countSketchSparseGramDot_perturb_bound`. The event radius becomes \(\eta+L(2\rho+\rho^2)+T_{\rm CSGram}^{fp}(h,\omega,A)\), while the exact finite-test-plus-Frobenius probability loss remains unchanged. The readable wrappers replace the coefficient loss by \(\sum_\alpha2\|Az_\alpha\|_2^4/(r\eta^2)+2\|A\|_F^4/(rL^2)\) and provide a direct target-budget theorem for that sufficient loss. | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` passed before ledger promotion. This is an implementation-facing sparse-Gram finite-cover endpoint for the modeled CountSketch Gram routine: exact hash/sign laws and the finite cover remain analysis objects, while sparse signed products, bucket accumulation, and rounded Gram dot products are charged by the concrete budget. It is still Markov/Frobenius-derived and weaker than optimal CountSketch concentration, but it no longer leaves the finite-cover theorem at an exact-only endpoint or only prose-level readable bound. |
| A3.4-S9u5a | Local `RowSamplingLeverage.lean` and `Preconditioning.lean`; orthonormal product-grid CountSketch sparse-Gram FP endpoint | `hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal`, `countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, `countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_gridNorm_add_nat_orthonormal`, `countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget`, `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_orthonormal_budget` | Specializes the S9u5 product-grid sparse-Gram route to exact orthonormal input \(U^TU=I\). The local isometry lemma gives \(\|Uz_a\|_2^2=\|z_a\|_2^2\) for every exact product-grid vector \(z_a\), and the existing Frobenius lemma gives \(\|U\|_F^2=n\). Substituting these identities into the exact, computed sparse-Gram, and stored-sign product-grid wrappers reduces the probability loss to \(\sum_a2\|z_a\|_2^4/(r\eta^2)+2n^2/(rL^2)\), with order \(\Theta((\sum_a\|z_a\|_2^4/\eta^2+n^2/L^2)/r)\). The computed sparse-Gram radius is the existing concrete sparse CountSketch budget; the stored-sign variants replace the sign-use path by the already proved stored-copy budgets for `fl_mul sign 1`, `fl_add sign 0`, and `fl_sub sign 0`. | Closed locally by focused Lean checks before ledger promotion. Exact objects are \(U\), the product-grid vectors, the hash/sign laws, and the product-grid cover geometry; probability laws remain exact by project convention. Computed non-probability objects in the stored-sign implementation path are the stored sign table, sparse signed products, bucket accumulation, and rounded Gram dot products, all charged by the displayed sparse-Gram budget. The result uses no perturbation-event hypothesis, certificate-existence assumption, or probability-computation term. It remains a finite-cover Markov/Frobenius endpoint and does not close the optimal CountSketch subspace-embedding concentration theorem or downstream uniform-row composition. |
| A3.4-S9u5b | Local `Preconditioning.lean`, `RowSamplingLeverage.lean`, and `UniformRowSamplingFP.lean`; orthonormal product-grid stored-sign downstream uniform-row FP endpoint | `countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq`, `countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq`, `hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq`, `frobNormSqRect_eq_nat_of_hasOrthonormalColumns`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget` | Composes the ordinary stored-sign product-grid CountSketch downstream uniform-row theorem with the orthonormal simplification. The local coefficient inequalities bound the exact product-grid CountSketch coefficient loss by \(\sum_a2\|Uz_a\|_2^4/(r\eta^2)+2\|U\|_F^4/(rL^2)\), and the orthonormal identities replace this by \(\sum_a2\|z_a\|_2^4/(r\eta^2)+2n^2/(rL^2)\). The downstream uniform-row term becomes \(r(mn)^2/(s\eta_{\rm row}^2)\) because \(\|U\|_F^2=n\). The final event is centered at \(I_n\), uses the concrete denominator `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, and includes the three modeled stored-sign copy routes. | Closed locally by focused Lean checks before ledger promotion. Exact objects are \(U\), exact product-grid vectors, exact hash/sign laws, and exact downstream row laws. Computed non-probability objects are stored signs, sparse signed products, bucket accumulation, concrete denominator formation, sampled-row divisions, and sampled-Gram dot products. No probability-computation term, perturbation-event hypothesis, auxiliary certificate, or generic probability-loss assumption is introduced. It remains a Markov/Frobenius finite-cover route and does not prove optimal CountSketch concentration, lower-level hash/sign generation formats, or alternate bucket-layout/downstream variants beyond the ordinary stored-sign path. |
| A3.4-S9u5c | Local `UniformRowSamplingFP.lean`; orthonormal product-grid stored-sign downstream uniform-row FP endpoints for fixed-order and tree-reduced bucket layouts | `countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget` | Reuses the ordinary S9u5b orthonormal loss simplification through a new deterministic budget adapter, then instantiates the existing stored-sign permuted-bucket and tree-reduced downstream product-grid theorems. The sufficient exact loss remains \(\sum_a2\|z_a\|_2^4/(r\eta^2)+2n^2/(rL^2)+r(mn)^2/(s\eta_{\rm row}^2)\), with order \(\Theta((\sum_a\|z_a\|_2^4/\eta^2+n^2/L^2)/r+r m^2n^2/(s\eta_{\rm row}^2))\). The permuted route charges bucket accumulation in the selected exact order; the tree route charges tree-depth accumulation under explicit `gammaValid` hypotheses for the supplied exact trees. | Closed locally by focused Lean checks before ledger promotion. Exact objects are \(U\), product-grid vectors, hash/sign laws, downstream row laws, bucket orders, and tree shapes. Computed non-probability objects are stored signs, sparse signed products, layout-specific bucket accumulation, concrete denominator formation, sampled-row divisions, and sampled-Gram dot products. No probability-computation term, perturbation-event hypothesis, auxiliary certificate, or generic probability-loss assumption is introduced. This closes the fixed-order and tree-reduced orthonormal layout refinements, while optimal CountSketch concentration and lower-level hash/sign generation remain open. |
| A3.4-S9v | Local `Preconditioning.lean`; non-injective CountSketch Frobenius/Markov sparse Gram FP endpoint | `countSketchDistinctPairSwap`, `countSketchDistinctPair_fourKernel_sum_le_two_sum_sq`, `rowGram_preconditionRows_countSketchRows_sub_rowGram_eq_distinctPair_sum`, `rademacherTraceProbability_expectationReal_countSketchRows_rowGram_entry_error_sq_eq`, `rademacherTraceProbability_expectationReal_countSketchRows_rowGram_entry_error_sq_le`, `countSketchHashProbability_expectationReal_collision_coeff_sq_eq_inv_mul`, `countSketchProbability_expectationReal_rowGram_entry_error_sq_le`, `countSketchProbability_expectationReal_rowGram_frob_error_sq_le`, `countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub`, `countSketchRowGramFrobErrorEvent`, `countSketchFlSparseGramDotRowGramFrobErrorEvent`, `countSketchRowGramFrobErrorEvent_subset_flSparseGramDotRowGramFrobErrorEvent`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub`, `countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm`, `frobNormSqRect_eq_nat_of_hasOrthonormalColumns`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_orthonormal` | Converts S9u into an actual non-injective CountSketch Gram theorem. The exact sketched Gram error is proved equal to the ordered off-diagonal collision/sign sum; the fourth-moment kernel is simplified to same/reversed ordered-pair survivors and bounded by \(2\sum c_{ab}^2\); exact hash averaging gives the entry variance factor \(2/r\); summing coordinates gives a Frobenius second moment; finite Markov gives \(\Pr(\|G_{SA}-A^TA\|_F\le\eta)\ge 1-2r^{-1}\sum_{j,l,a\ne b}(A_{aj}A_{bl})^2/\eta^2\). The computed event replaces \(G_{SA}\) by \(\widehat G=\operatorname{fl}(\operatorname{fl}(S_{h,\omega}A)^T\operatorname{fl}(S_{h,\omega}A))\) and adds the concrete sparse-Gram FP budget from S9p. The coefficient sum is bounded by \(\|A\|_F^4\), so the readable failure order is \(\Theta(\|A\|_F^4/(r\eta^2))\); for \(U^TU=I\), it is \(\Theta(n^2/(r\eta^2))\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` and focused module build. This is a genuine non-injective Frobenius/Markov route and no longer assumes a collision-free event or a perturbation certificate. It remains weaker than the standard CountSketch Loewner/subspace-embedding theorem, and it does not yet compose the non-injective route through downstream uniform-row sampling or the complete input-sparsity Algorithm 3 theorem. Sampling probabilities and laws remain exact; sparse signed products, bucket accumulation, and Gram dot products are charged in the computed event. |
| A3.4-S9w | Local `Preconditioning.lean`; non-injective CountSketch finite-Loewner sparse Gram FP endpoint | `countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent`, `countSketchFlSparseGramDotRowGramFrobErrorEvent_subset_twoSidedLoewnerEvent`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_frobNorm`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_orthonormal` | Converts the S9v computed Frobenius event into the two-sided finite-Loewner event \(-\tau I\preceq \widehat G-A^TA\preceq\tau I\) with \(\tau=\eta+T_{\rm CSGram}^{\rm fp}(h,\omega,A)\). The deterministic proof uses the existing local bridge \(\|M\|_F\le\tau\Rightarrow\|M\|_2\le\tau\) and the finite-Loewner quadratic-form wrappers. The probability lower bounds and simplified orders are unchanged from S9v: coefficient form \(1-2r^{-1}\sum(A_{aj}A_{bl})^2/\eta^2\), simplified \(1-2\|A\|_F^4/(r\eta^2)\), and orthonormal \(1-2n^2/(r\eta^2)\), with failure orders \(\Theta(\|A\|_F^4/(r\eta^2))\) and \(\Theta(n^2/(r\eta^2))\). | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`, focused module build, and lookup validation passed before ledger promotion. This is a genuine non-injective finite-Loewner sparse-Gram endpoint with all sparse apply and Gram-dot arithmetic charged. It is still Markov/Frobenius-derived, weaker than the optimal CountSketch subspace-embedding concentration theorem, and not yet composed through downstream uniform-row sampling or the complete input-sparsity Algorithm 3 theorem. Sampling probabilities and laws remain exact mathematical inputs. |
| A3.4-S9w2 | Local `Preconditioning.lean`; target-budget wrappers for S9w | `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget`, `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub_delta_of_orthonormal_budget` | Converts the S9w lower-bound expressions into direct \(1-\delta\) theorem surfaces. The exact coefficient wrapper assumes \(2r^{-1}\sum_{j,l,a\ne b}(A_{aj}A_{bl})^2/\eta^2\le\delta\); the readable Frobenius wrapper assumes \(2\|A\|_F^4/(r\eta^2)\le\delta\); and the orthonormal wrapper assumes \(2n^2/(r\eta^2)\le\delta\). In each case, the charged computed sparse-Gram finite-Loewner event has probability at least \(1-\delta\). The simplified orders are \(\Theta(\|A\|_F^4/(r\eta^2))\) and, for \(U^TU=I\), \(\Theta(n^2/(r\eta^2))\). | Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`, focused module build, and executable lookup passed before ledger promotion. This is a readability/non-vacuity corollary of S9w, not a new perturbation assumption and not an optimal CountSketch concentration theorem. Sparse signed products, bucket accumulation, and rounded Gram dot products remain charged in the S9w event radius. |
| A3.4-S9x | Local `UniformRowSampling.lean`; general iid uniform-row Frobenius/Markov sample-Gram foundation | `uniform_rowOuterGramSample_mean_eq_rowGram`, `uniformRowTraceProbability_expectationReal_centered_sum_sq`, `uniformRowTraceProbability_expectationReal_sampleAverage_sub_mean_sq`, `uniformRowTraceProbability_expectationReal_uniformRowSampleGram_entry_error_sq`, `uniformRowOuterGramSample_row_second_moment`, `uniformRowOuterGramSample_total_second_moment`, `rowNormSq_sq_sum_le_frobNormSqRect_sq`, `uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le`, `uniformRowTraceProbability_expectationReal_uniformRowSampleGram_frob_error_sq_le_frobNorm`, `uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub`, `uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm` | Removes the orthonormal-column restriction from the downstream iid uniform-row sampling foundation. For an arbitrary exact matrix \(M\), the exact one-row estimator \(mM_{i,*}^TM_{i,*}\) has mean \(M^TM\); iid sample averaging gives the coordinate variance identity; summing and bounding the centered second moment by the raw second moment proves \(E\|\widehat G-M^TM\|_F^2\le(m/s)\sum_i\|M_{i,*}\|_2^4\le(m/s)\|M\|_F^4\); finite Markov gives the matching high-probability Frobenius events. The exact row-fourth failure term has order \(\Theta(m\sum_i\|M_{i,*}\|_2^4/(s\eta^2))\) when nonzero, and the simplified Frobenius upper radius has order \(\Theta(m\|M\|_F^4/(s\eta^2))\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSampling.lean` and focused module build. This is exact-law/exact-arithmetic infrastructure for composing non-orthonormal preconditioned matrices with downstream row sampling. It deliberately does not charge floating-point arithmetic by itself; the implementation-facing theorem still needs the concrete computed preconditioned matrix, row scaling/denominator, and rounded sample-Gram budgets composed with this foundation. Sampling probabilities and laws remain exact mathematical inputs. |
| A3.4-S9y | Local `UniformRowSamplingFP.lean`; general iid uniform-row floating-point Frobenius sample-Gram endpoint | `uniformRowSampleGramRowGramFrobErrorEvent`, `uniformRowFlSampleGramDotRowGramFrobErrorEvent`, `uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent`, `uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot`, `uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen`, `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub`, `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm`, `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub`, `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm` | Composes S9x with the concrete deterministic floating-point sampled-Gram perturbation theorems. For an arbitrary exact matrix \(M\), the exact row law and exact reference \(M^TM\) stay mathematical; the exact-denominator event charges rounded row divisions and rounded length-\(s\) dot products through `uniformRowSampleGramFullFpPerturbBudget`, and the computed-denominator event also charges `ComputedUniformRowScaleDen` through `uniformRowSampleGramComputedDenFullFpPerturbBudget`. The probability terms remain \(1-m\sum_i\|M_{i,*}\|_2^4/(s\eta^2)\) and \(1-m\|M\|_F^4/(s\eta^2)\). The expanded exact-denominator radius is \(((2u+u^2)+\gamma_s(1+u)^2)\||B|^T|B|\|_F=\Theta((u+\gamma_s)\||B|^T|B|\|_F)\); the computed-denominator radius is \(\|E^T|\widehat B|+|B|^TE\|_F+\gamma_s\||\widehat B|^T|\widehat B|\|_F\), with \(E_{qj}=|\widehat B_{qj}|u+|M_{\sigma_qj}|\,|\widehat d-d|/(|\widehat d|\,|d|)\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`, focused module build, and lookup validation after rebuilding the module. This is an implementation-facing generic uniform-row sampled-Gram endpoint with no perturbation-event/certificate assumption. It is not yet the final non-injective CountSketch-plus-uniform-row theorem, because the concrete computed preconditioned matrix still needs to be composed into this generic arbitrary-matrix endpoint. Sampling probabilities and laws remain exact mathematical inputs. |
| A3.4-S9z | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; non-injective CountSketch plus downstream uniform-row FP Frobenius endpoint | `countSketchBucket_sum_sum_eq`, `frobNormSqRect_preconditionRows_countSketchRows_le`, `countSketchUniformRowSampleGramRowGramFrobEvent`, `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent`, `countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm` | Composes the non-injective CountSketch Frobenius/Markov route with exact iid uniform-row sampling from the \(r\) CountSketch output rows and with the concrete computed sparse-apply/sample-Gram implementation. The deterministic bucket partition theorem proves \(\sum_i\sum_{k:h(k)=i} f(k)=\sum_k f(k)\), and Cauchy--Schwarz gives \(\|S_{h,\omega}A\|_F^2\le m\|A\|_F^2\) for exact signs of magnitude at most one. The exact product-law theorem intersects the CountSketch Gram event and exact row-sampling event. The computed theorem forms \(\widehat V=\operatorname{flCountSketchSparseApply}(h,\omega,A)\), uses a computed \(\widehat d\) for \(\sqrt{s/r}\), rounds sampled-row divisions and Gram dot products, and proves the final Frobenius event around \(A^TA\). The exact coefficient loss is \(2r^{-1}\sum_{j,k}\sum_{a\ne b}(A_{aj}A_{bk})^2/\eta_{\rm CS}^2+r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\); the readable loss is \(2\|A\|_F^4/(r\eta_{\rm CS}^2)+r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\). | Closed locally by focused `lake env lean` checks for `Preconditioning.lean` and `UniformRowSamplingFP.lean`, focused module builds, and lookup validation after rebuilding. This is a genuine non-injective downstream row-sampling implementation endpoint with no collision-free event and no perturbation-existence assumption. It remains Markov/Frobenius-derived and weaker than the optimal CountSketch finite-Loewner/subspace-embedding concentration theorem. Sampling probabilities and laws remain exact mathematical inputs; sparse apply, computed denominator, row divisions, and sampled-Gram dot products are charged in the displayed realized radius. |
| A3.4-S9za | Local `UniformRowSamplingFP.lean`; two-sided finite-Loewner promotion of S9z | `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent`, `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm` | Applies the existing local Frobenius-to-operator/Loewner bridge to the fully computed S9z event. The event states \(-\tau I\preceq\widehat G_{\rm CS+row}^{fp}-A^TA\preceq\tau I\), where \(\tau=\eta_{\rm CS}+\eta_{\rm row}+T_{\rm CS,row}^{fp}\), and inherits the exact coefficient loss and simplified \(\Theta(\|A\|_F^4/(r\eta_{\rm CS}^2)+r m^2\|A\|_F^4/(s\eta_{\rm row}^2))\) order from S9z. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` and focused module build. No external proof source is needed: this is a deterministic norm-to-Loewner transfer after all computed sparse apply, computed denominator, row division, and Gram-dot arithmetic has already been charged. The concrete denominator wrappers are recorded in S9zb. It remains Markov/Frobenius-derived and weaker than optimal CountSketch subspace-embedding concentration. |
| A3.4-S9zb | Local `UniformRowSamplingFP.lean`; concrete-denominator sample-budget and equal-radius wrappers for S9za | `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget` | Converts the readable S9za failure expression into a direct \(1-\delta\) theorem: if \(2\|A\|_F^4/(r\eta_{\rm CS}^2)+r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\le\delta\), then the fully computed two-sided event has probability at least \(1-\delta\). The final concrete wrappers instantiate the row-scaling denominator as `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`, whose radius is `sqrt(s/r) * ((4u + 3u^2 + u^3)/(1-u))`; the older `WithComputedDen` wrappers remain infrastructure for other denominator routines. The equal-radius wrapper sets \(\eta_{\rm CS}=\eta_{\rm row}=\varepsilon/2\), so the exact non-floating-point part of the Loewner radius is \(\varepsilon\) and the irreducible failure expression is \(8\|A\|_F^4/(r\varepsilon^2)+4r m^2\|A\|_F^4/(s\varepsilon^2)\), with order \(\Theta(\|A\|_F^4/(r\varepsilon^2)+r m^2\|A\|_F^4/(s\varepsilon^2))\). | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean` before ledger promotion. This is a readable corollary of the already charged S9za implementation event, not a new perturbation assumption. It remains Markov/Frobenius-derived and weaker than optimal CountSketch subspace-embedding concentration. |
| A3.4-S9zc | Local `UniformRowSamplingFP.lean`; exact-coefficient target-budget wrappers for S9za | `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget` | Converts the sharper S9za exact coefficient loss into direct \(1-\delta\) theorem surfaces. The generic computed-denominator wrapper assumes \(2r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/\eta_{\rm CS}^2+r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\le\delta\); the equal-radius wrapper sets \(\eta_{\rm CS}=\eta_{\rm row}=\varepsilon/2\) and expands the exact condition to \(8r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/\varepsilon^2+4r m^2\|A\|_F^4/(s\varepsilon^2)\le\delta\). The irreducible equal-radius order is \(\Theta(r^{-1}\sum(A_{aj}A_{bk})^2/\varepsilon^2+r m^2\|A\|_F^4/(s\varepsilon^2))\), while the readable Frobenius upper route remains S9zb. | Validated by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`, focused module build, executable lookup after rebuilding the module, aggregate RandNLA build, full `lake build`, marker scan, no-proof-sketch wording scan, `git diff --check`, temporary axiom audit reporting only `[propext, Classical.choice, Quot.sound]`, and regenerated master summary PDF text search. This is a target-budget corollary of the already charged S9za event, not a perturbation assumption and not an optimal CountSketch subspace-embedding theorem. |
| A3.4-S9zd | Local `UniformRowSamplingFP.lean`; expanded equal-radius wrappers for S9za | `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded` | Replaces the local shorthand `let η := ε / 2` in the S9za target-budget hypotheses by checked expanded formulas. The exact-coefficient condition is \(8r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/\varepsilon^2+4r m^2\|A\|_F^4/(s\varepsilon^2)\le\delta\); the readable sufficient condition is \(8\|A\|_F^4/(r\varepsilon^2)+4r m^2\|A\|_F^4/(s\varepsilon^2)\le\delta\). The concrete-denominator siblings instantiate the same `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))` denominator routine as S9zb/S9zc. | Validated by focused Lean, focused module build, executable lookup, aggregate RandNLA build, full `lake build`, marker/temp/no-sketch scans, `git diff --check`, temporary axiom audit reporting only `[propext, Classical.choice, Quot.sound]`, and regenerated master-summary PDF text search. This is an interpretability and non-vacuity theorem-surface refinement of the already charged S9za event; it introduces no new random law, perturbation event, computed object, or certificate assumption. |
| A3.4-S9ze | Local `UniformRowSamplingFP.lean`; finite-cover CountSketch Loewner preprocessing composed through downstream uniform-row FP sampling | `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`, `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget` | Composes the exact finite-cover CountSketch two-sided Loewner event from S9u4 with exact iid uniform-row sampling and the existing concrete computed sparse-apply/sample-Gram perturbation event. The CountSketch exact radius is \(\tau_{\rm CS}=\eta+L(2\rho+\rho^2)\); the downstream theorem proves the computed event with radius \(\tau_{\rm CS}+\eta_{\rm row}+T_{\rm CS,row}^{fp}\). The exact loss is \(\sum_\alpha2r^{-1}\sum_{a\ne b}((Az_\alpha)_a(Az_\alpha)_b)^2/\eta^2+2r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/L^2+r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\), with irreducible order \(\Theta(\sum_\alpha r^{-1}\sum_{a\ne b}((Az_\alpha)_a(Az_\alpha)_b)^2/\eta^2+r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/L^2+r m^2\|A\|_F^4/(s\eta_{\rm row}^2))\). | Validated by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`, focused module build, executable lookup, aggregate RandNLA build, full `lake build`, marker/temp/no-sketch scans, `git diff --check`, temporary axiom audit reporting only `[propext, Classical.choice, Quot.sound]`, and regenerated 442-page master-summary PDF sync/text search. The theorem introduces no perturbation-event, certificate-existence, hidden computed quantity, or new probability-law assumption; sparse apply, denominator formation, row divisions, and sampled-Gram dot products remain charged by the existing realized budget. It remains finite-cover Markov/Frobenius-derived rather than optimal CountSketch subspace-embedding concentration. |
| A3.4-S9zf | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; generated Sylvester/Walsh orthogonality and final concrete-denominator SRHT endpoint | `fhtButterflyExact_sq_sum`, `fhtButterflyExact_inner_sum`, `fhtPairUpdateExact_inner_sum`, `vecNorm2Sq_fhtPairUpdateExact`, `sylvesterHadamardSignPattern_symm`, `exists_testBit_ne_of_fin_two_pow_ne`, `sylvesterStageBitFlip_bijective`, `sylvesterHadamardSignPattern_col_inner`, `sylvesterHadamardSignPattern_row_inner`, `sylvesterHadamardScaled_col_inner`, `sylvesterHadamardScaled_row_inner`, `isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Proves the normalized Sylvester/Walsh bit-parity table is orthogonal internally, using a differing-bit involution for off-diagonal column sums and the square-one sign identity for diagonal sums. The final endpoint sets \(H_{ik}=\sqrt{(2^p)^{-1}}S_p(i,k)\), \(A=UC\), the generated fast-FHT stored-sign computed preconditioner `signedHadamardSylvesterFhtScheduleStoredSignPreconditioner`, and the concrete denominator `uniformRowFlSqrtMulInvSqrtScaleDen`. It composes the source-sharp SRHT exact law with the existing computed-left/computed-denominator perturbation transfer without requiring external `IsOrthogonal H`, `HadamardFlat H`, perturbation-event, or certificate-existence hypotheses. | Focused `lake build LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP` and executable `lake env lean examples/LibraryLookup.lean` passed before ledger promotion. This closes the functional generated-FHT stored-sign actual-input route for exact analysis witnesses \(A=UC\), with exact Rademacher/uniform laws and charged sign storage, FHT butterfly arithmetic, rounded normalization, `fl(Pihat*A)`, concrete denominator formation, row divisions, and Gram dot products. Layout-specific array overwrite/copy variants remain separate rows unless the implementation uses the already modeled writeback routines. |
| A3.4-S9zg | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; generated Sylvester/Walsh FHT final endpoint with all-coordinate add-zero writeback | `flFhtPairUpdateStoredAddZeroRight`, `fhtPairUpdateStoredAddZeroRightPropagatedErrorBudget`, `flFhtPairScheduleStoredAddZeroRight_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixStoredAddZeroRight_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight`, `signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Promotes the modeled all-coordinate add-zero FHT writeback/copy routine from an exact-law computed-left perturbation event to the final actual-input concrete-denominator SRHT theorem. The endpoint uses the same internally proved Sylvester/Walsh orthogonality and flatness as S9zf and the same exact analysis witnesses \(A=UC\), but the preconditioner certificate now recurses through each generated FHT butterfly and adds the explicit writeback term \(u|y_i|\) for every coordinate after every pair update before the rounded normalization. The final sampled-Gram theorem charges stored Rademacher signs, butterfly arithmetic, all-coordinate `fl_add(output,0)` writeback, rounded normalization, `fl(Pihat*A)`, concrete denominator formation, row divisions, and Gram dot products. | Closed locally by the add-zero theorem and documented in the standalone Algorithm 3 sheet with an expanded recursive radius and small-roundoff order. This is not a new probability law and introduces no perturbation-event, certificate-existence, external orthogonality, external flatness, or generic denominator assumption. Rademacher and uniform-row laws remain exact mathematical inputs; all non-probability operations on this modeled writeback path are charged. Other memory-layout, aliasing, in-place overwrite, or vectorized writeback semantics remain separate implementation paths unless reduced to this modeled all-coordinate writeback recurrence. |
| A3.4-S9zh | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; generated Sylvester/Walsh FHT final endpoint with modified-coordinate add-zero writeback | `flFhtPairUpdateModifiedStoredAddZeroRight`, `fhtPairUpdateModifiedStoredAddZeroRightPropagatedErrorBudget`, `flFhtPairScheduleModifiedStoredAddZeroRight_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixModifiedStoredAddZeroRight_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight`, `signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Promotes the modeled modified-coordinate add-zero FHT writeback/copy routine from an exact-law computed-left perturbation event to the final actual-input concrete-denominator SRHT theorem. The endpoint uses the same internally proved Sylvester/Walsh orthogonality and flatness as S9zf, the same exact analysis witnesses \(A=UC\), and the same concrete denominator, but the preconditioner certificate adds the explicit writeback term \(u|y_i|\) only on the two coordinates modified by each butterfly pair update. The final sampled-Gram theorem charges stored Rademacher signs, butterfly arithmetic, modified-coordinate `fl_add(output,0)` writeback, rounded normalization, `fl(Pihat*A)`, concrete denominator formation, row divisions, and Gram dot products. | Closed locally by the modified-coordinate add-zero theorem and documented in the standalone Algorithm 3 sheet with an expanded recursive radius and small-roundoff/non-vacuity statement. This is not a new probability law and introduces no perturbation-event, certificate-existence, external orthogonality, external flatness, or generic denominator assumption. Rademacher and uniform-row laws remain exact mathematical inputs; all non-probability operations on this modeled modified-coordinate writeback path are charged. Other memory-layout, aliasing, in-place overwrite, or vectorized writeback semantics remain separate implementation paths unless reduced to this modeled recurrence. |
| A3.4-S9zi | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; generated Sylvester/Walsh FHT final endpoints with all-coordinate multiply-one and subtract-zero writeback | `flFhtPairUpdateStoredMulOne`, `fhtPairUpdateStoredMulOnePropagatedErrorBudget`, `flFhtPairScheduleStoredMulOne_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixStoredMulOne_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne`, `signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`, `flFhtPairUpdateStoredSubZeroRight`, `fhtPairUpdateStoredSubZeroRightPropagatedErrorBudget`, `flFhtPairScheduleStoredSubZeroRight_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixStoredSubZeroRight_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight`, `signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Promotes the modeled all-coordinate multiply-one and subtract-zero FHT writeback/copy routines from exact-law computed-left perturbation events to final actual-input concrete-denominator SRHT theorems. Both endpoints use the same internally proved Sylvester/Walsh orthogonality and flatness as S9zf, the same exact analysis witnesses \(A=UC\), and the same concrete denominator. Their preconditioner certificates recurse through each generated FHT butterfly and add the explicit writeback term \(u|y_i|\) for every coordinate after every pair update, using `fl_mul(output,1)` or `fl_sub(output,0)` instead of add-zero. The final sampled-Gram theorems charge stored Rademacher signs, butterfly arithmetic, all-coordinate writeback, rounded normalization, `fl(Pihat*A)`, concrete denominator formation, row divisions, and Gram dot products. | Closed locally by the two new final theorems and documented in the standalone Algorithm 3 sheet with a shared recursive radius, an irreducible copy contribution, a small-roundoff \(O/\Theta\) order statement, and a non-vacuity check. This is not a new probability law and introduces no perturbation-event, certificate-existence, external orthogonality, external flatness, or generic denominator assumption. Rademacher and uniform-row laws remain exact mathematical inputs; all non-probability operations on these modeled all-coordinate writeback paths are charged. Other memory-layout, aliasing, in-place overwrite, or vectorized writeback semantics remain separate implementation paths unless reduced to these modeled recurrences. |
| A3.4-S9zj | Local `Preconditioning.lean` and `UniformRowSamplingFP.lean`; generated Sylvester/Walsh FHT final endpoints with modified-coordinate multiply-one and subtract-zero writeback | `flFhtPairUpdateModifiedStoredMulOne`, `fhtPairUpdateModifiedStoredMulOnePropagatedErrorBudget`, `flFhtPairScheduleModifiedStoredMulOne_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixModifiedStoredMulOne_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne`, `signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`, `flFhtPairUpdateModifiedStoredSubZeroRight`, `fhtPairUpdateModifiedStoredSubZeroRightPropagatedErrorBudget`, `flFhtPairScheduleModifiedStoredSubZeroRight_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrixModifiedStoredSubZeroRight_sqrtInvNatScale_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight`, `signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Promotes the modeled modified-coordinate multiply-one and subtract-zero FHT writeback/copy routines from exact-law computed-left perturbation events to final actual-input concrete-denominator SRHT theorems. Both endpoints use the same internally proved Sylvester/Walsh orthogonality and flatness as S9zf, the same exact analysis witnesses \(A=UC\), and the same concrete denominator. Their preconditioner certificates recurse through each generated FHT butterfly and add the explicit writeback term \(u|y_i|\) only on the two modified outputs of each pair update, using `fl_mul(output,1)` or `fl_sub(output,0)`; untouched coordinates carry without a writeback term. The final sampled-Gram theorems charge stored Rademacher signs, butterfly arithmetic, modified-coordinate writeback, rounded normalization, `fl(Pihat*A)`, concrete denominator formation, row divisions, and Gram dot products. | Closed locally by the two new final theorems and documented in the standalone Algorithm 3 sheet with a shared modified-coordinate recursive radius, an irreducible copy contribution, a small-roundoff \(O/\Theta\) order statement, and a non-vacuity check. This is not a new probability law and introduces no perturbation-event, certificate-existence, external orthogonality, external flatness, or generic denominator assumption. Rademacher and uniform-row laws remain exact mathematical inputs; all non-probability operations on these modeled modified-coordinate writeback paths are charged. Other memory-layout, aliasing, in-place overwrite, or vectorized writeback semantics remain separate implementation paths unless reduced to these modeled recurrences. |
| A3.4-S9zk | Local `Preconditioning.lean`; rounded generated-stage FHT no-alias/order certificates | `flFhtPairUpdate_commute_of_disjoint`, `flFhtPairSchedule_commute_update_of_forall`, `fhtStagePairs_flFhtPairUpdate_commute_of_ne`, `fhtStagePairs_flFhtPairUpdate_commute_schedule_of_ne`, `flFhtPairUpdateModifiedStoredAddZeroRight_commute_of_disjoint`, `flFhtPairUpdateModifiedStoredMulOne_commute_of_disjoint`, `flFhtPairUpdateModifiedStoredSubZeroRight_commute_of_disjoint`, `flFhtPairScheduleModifiedStoredAddZeroRight_commute_update_of_forall`, `flFhtPairScheduleModifiedStoredMulOne_commute_update_of_forall`, `flFhtPairScheduleModifiedStoredSubZeroRight_commute_update_of_forall`, `fhtStagePairs_flFhtPairUpdateModifiedStoredAddZeroRight_commute_of_ne`, `fhtStagePairs_flFhtPairUpdateModifiedStoredAddZeroRight_commute_schedule_of_ne`, `fhtStagePairs_flFhtPairUpdateModifiedStoredMulOne_commute_of_ne`, `fhtStagePairs_flFhtPairUpdateModifiedStoredMulOne_commute_schedule_of_ne`, `fhtStagePairs_flFhtPairUpdateModifiedStoredSubZeroRight_commute_of_ne`, `fhtStagePairs_flFhtPairUpdateModifiedStoredSubZeroRight_commute_schedule_of_ne` | Proves that distinct generated butterfly pairs in the same FHT stage have no shared coordinates not only for the exact update, but also for the rounded base update and the three modified-coordinate writeback routines. The list-level bridges move a rounded update across a same-stage schedule of distinct generated pairs. These are deterministic layout/order certificates for the modeled functional schedules; they introduce no probability-law change and no additional floating-point radius beyond the already charged pair/update writeback routines. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean`. This closes same-stage no-alias/list-order behavior for the modeled rounded and modified-coordinate functional FHT schedules. Arbitrary in-place overwrite, vectorized memory layout, or storage routines with different semantics remain separate implementation paths. |
| A3.4-S9zl | Local `Preconditioning.lean`; rounded/generated FHT untouched-coordinate preservation | `flFhtPairSchedule_apply_of_forall_not_mem`, `flFhtPairScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`, `flFhtPairScheduleModifiedStoredMulOne_apply_of_forall_not_mem`, `flFhtPairScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`, `fhtStagePairs_flFhtPairSchedule_apply_of_forall_not_mem`, `fhtStagePairs_flFhtPairScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`, `fhtStagePairs_flFhtPairScheduleModifiedStoredMulOne_apply_of_forall_not_mem`, `fhtStagePairs_flFhtPairScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem` | Proves that any coordinate outside every pair in a supplied FHT schedule is carried unchanged by the base rounded functional schedule and by the three modified-coordinate writeback schedules. The generated-stage wrappers specialize the same statement to `fhtStagePairs n stride`. These are deterministic storage/no-touch certificates for modeled schedules that leave untouched coordinates in place; they deliberately do not apply to all-coordinate copy/writeback routines, which rewrite every entry. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` before ledger promotion. The theorem adds no probability-law change and no new floating-point radius. It narrows the remaining FHT layout work to memory layouts, in-place overwrite routines, vectorized routines, or storage semantics not reducible to the modeled base or modified-coordinate schedules. |
| A3.4-S9zm | Local `Preconditioning.lean`; rounded/generated FHT untouched-coordinate budget preservation | `fhtPairSchedulePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtPairScheduleModifiedStoredAddZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `fhtPairScheduleModifiedStoredMulOnePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtPairScheduleModifiedStoredSubZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `fhtStagePairs_fhtPairSchedulePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtStagePairs_fhtPairScheduleModifiedStoredAddZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `fhtStagePairs_fhtPairScheduleModifiedStoredMulOnePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtStagePairs_fhtPairScheduleModifiedStoredSubZeroRightPropagatedErrorBudget_apply_of_forall_not_mem` | Proves the error-radius analogue of S9zl: when coordinate `i` is outside every pair in a supplied FHT schedule, the base rounded propagated budget and the three modified-coordinate propagated budgets return exactly the incoming radius `E i`. The generated-stage wrappers specialize the same statement to `fhtStagePairs n stride`. These are deterministic budget/no-touch certificates; they add no copy term and no probability-law assumption. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` before ledger promotion. This strengthens the modeled modified-coordinate storage story by proving not only that untouched entries are not rewritten, but also that their displayed FP budgets do not grow. All-coordinate copy/writeback routines remain outside this theorem because they intentionally rewrite every entry. |
| A3.4-S9zn | Local `Preconditioning.lean`; concrete Sylvester/Walsh FHT no-touch wrappers | `flFhtSylvesterSchedule_apply_of_forall_not_mem`, `flFhtSylvesterScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`, `flFhtSylvesterScheduleModifiedStoredMulOne_apply_of_forall_not_mem`, `flFhtSylvesterScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`, `fhtSylvesterSchedulePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterScheduleModifiedStoredAddZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterScheduleModifiedStoredMulOnePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterScheduleModifiedStoredSubZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `flFhtSylvesterStageScheduleModifiedStoredAddZeroRight`, `flFhtSylvesterStageScheduleModifiedStoredMulOne`, `flFhtSylvesterStageScheduleModifiedStoredSubZeroRight`, `fhtSylvesterStageScheduleModifiedStoredAddZeroRightPropagatedErrorBudget`, `fhtSylvesterStageScheduleModifiedStoredMulOnePropagatedErrorBudget`, `fhtSylvesterStageScheduleModifiedStoredSubZeroRightPropagatedErrorBudget`, `flFhtSylvesterStageSchedule_apply_of_forall_not_mem`, `flFhtSylvesterStageScheduleModifiedStoredAddZeroRight_apply_of_forall_not_mem`, `flFhtSylvesterStageScheduleModifiedStoredMulOne_apply_of_forall_not_mem`, `flFhtSylvesterStageScheduleModifiedStoredSubZeroRight_apply_of_forall_not_mem`, `fhtSylvesterStageSchedulePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterStageScheduleModifiedStoredAddZeroRightPropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterStageScheduleModifiedStoredMulOnePropagatedErrorBudget_apply_of_forall_not_mem`, `fhtSylvesterStageScheduleModifiedStoredSubZeroRightPropagatedErrorBudget_apply_of_forall_not_mem` | Specializes S9zl and S9zm from supplied/generated stage lists to the concrete full Sylvester schedule `fhtSylvesterSchedulePairs p` and a concrete Sylvester stage `fhtSylvesterStagePairs p stage`. The full-schedule and one-stage wrappers prove both value preservation and exact incoming-radius preservation for the base rounded schedule and the three modified-coordinate writeback schedules when coordinate `i` is outside every generated pair in the relevant list. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` before ledger promotion. The theorem adds no probability-law change and no new floating-point radius; it is a concrete-interface wrapper layer that prevents future downstream statements from hiding behind raw generic pair schedules. All-coordinate copy/writeback routines remain outside this theorem because they intentionally rewrite every entry. |
| A3.4-S9zo | Local `Preconditioning.lean`; concrete Sylvester/Walsh FHT stage-order wrappers | `fhtSylvesterStagePairs_disjoint_of_ne`, `fhtSylvesterStagePairs_pairUpdateExact_commute_of_ne`, `fhtSylvesterStagePairs_pairUpdateExact_commute_schedule_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdate_commute_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdate_commute_schedule_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredAddZeroRight_commute_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredAddZeroRight_commute_schedule_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredMulOne_commute_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredMulOne_commute_schedule_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredSubZeroRight_commute_of_ne`, `fhtSylvesterStagePairs_flFhtPairUpdateModifiedStoredSubZeroRight_commute_schedule_of_ne` | Specializes the generic same-stage no-alias/list-order certificates from `fhtStagePairs n stride` to the concrete Sylvester stage list `fhtSylvesterStagePairs p stage`. Distinct concrete generated-stage pairs are disjoint, exact pair updates commute, base rounded updates commute, and the three modified-coordinate writeback updates commute pairwise and across same-stage lists of distinct pairs. | Closed locally by focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/Preconditioning.lean` before ledger promotion. The theorem adds no probability-law change and no new floating-point radius; it is a concrete-interface wrapper layer for the modeled functional stage schedules. In-place overwrite, vectorized memory layout, or storage routines with different semantics still need separate certificates. |
| A3.4-S10 | Local `MatrixAlgebra.lean`, `Preconditioning.lean` | `FiniteVecConvex`, `vecNorm2_linear_combination_convex`, `signedHadamard_row_vecNorm2_convex` | Finite deterministic convexity side of Tropp Proposition 2.1 for the signed-Hadamard row norm | Closed locally; focused `Preconditioning` build passed. This is only the algorithm-specific convexity input, not the Ledoux/Talagrand concentration theorem. |
| A3.4-S11 | Local `MatrixAlgebra.lean` | `FiniteVecLipschitzWith`, `unitCubeToRademacherVec`, `finiteVecConvex_scaled_unitCubeToRademacher`, `finiteVecLipschitzWith_scaled_unitCubeToRademacher` | Deterministic affine constant conversion from Ledoux's \([0,1]^n\) concentration statement to Tropp's Rademacher-sign statement | Closed locally; focused `lake build LeanFpAnalysis.FP.Analysis.MatrixAlgebra` passed. This does not prove Ledoux's log-Sobolev/Laplace theorem. |
| A3.4-S12 | Local `FiniteProbability.lean`; source route Ledoux (1.6)--(1.7) | `FiniteProbability.expectationReal_exp_pos`, `FiniteProbability.hasDerivAt_expectationReal_exp_mul`, `FiniteProbability.hasDerivAt_log_expectationReal_exp_mul`, `FiniteProbability.entropyReal`, `FiniteProbability.entropyReal_exp_mul_eq`, `FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le`, `FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le`, `FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero`, `FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le`, `FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le`, `FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le`, `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound`, `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le` | Finite MGF/Herbst/Laplace calculus substrate: positivity of finite exponential moments, derivative and log-derivative of the finite MGF, entropy algebra for exponential tilts, the entropy-bound-to-differential-inequality step, corrected-quotient monotonicity `lambda -> log M(lambda)/lambda - c lambda`, the right-limit `log M(lambda)/lambda -> E X` as `lambda -> 0+`, the finite Herbst extraction to `log M(lambda) <= lambda E X + c lambda^2`, the entropy-bound-to-log-Laplace wrapper, the log-Laplace-to-centered-MGF step, and the log-Laplace/entropy-to-tail wrappers | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This is a real foundation layer for the Ledoux log-Sobolev-to-Laplace route, but it does not prove Ledoux's log-Sobolev entropy inequality or the convex concentration theorem. |
| A3.4-S13 | Local `FiniteProbability.lean`; Ledoux product-measure tensorization route | `FiniteProbability.prod_expectationReal_eq`, `FiniteProbability.prod_expectationReal_fst_eq`, `FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation` | Finite product-law expectation Fubini and exact entropy chain rule/tensorization algebra for a two-factor product law | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This is a product-measure algebra dependency for a finite Ledoux log-Sobolev proof; it does not prove the coordinate log-Sobolev inequality or the separately-convex concentration theorem. |
| A3.4-S14 | Local `FiniteProbability.lean`; Ledoux Bernoulli-coordinate specialization route | `FiniteProbability.boolUniformProbability`, `FiniteProbability.boolUniformProbability_prob`, `FiniteProbability.boolUniformProbability_expectationReal`, `FiniteProbability.entropyReal_boolUniformProbability_eq` | Unbiased Bernoulli coordinate law on `Bool`, with exact point-mass, expectation, and entropy formulas | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This is the coordinate-measure object needed before a finite Bernoulli/cube log-Sobolev inequality can be stated cleanly; it does not prove that coordinate log-Sobolev inequality or the product concentration theorem. |
| A3.4-S15 | Local `FiniteProbability.lean`; Ledoux Theorem 1.2/(1.6) coordinate analogue | `FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos`, `FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos` | Scalar two-point entropy estimate and fair-Bernoulli coordinate log-Sobolev inequality for strictly positive two-point functions | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This proves an actual coordinate entropy inequality, but it is not yet the tensorized product-measure Ledoux concentration theorem or Tropp's Rademacher tail bound. |
| A3.4-S16 | Local `FiniteProbability.lean`; Ledoux product tensorization route | `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy` | One-coordinate product peel-off: `Ent_{P x Bool}(g^2)` is bounded by the expected Bernoulli-coordinate squared difference plus `Ent_P(E_Bool g^2)` | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This is the first tensorization step after the coordinate log-Sobolev inequality; it still leaves the induction/L2-section norm step needed for the full finite Bernoulli cube concentration theorem. |
| A3.4-S17 | Local `FiniteProbability.lean`; Ledoux tensorization induction route | `FiniteProbability.expectationReal_sq_nonneg`, `FiniteProbability.abs_expectationReal_mul_le_sqrt_mul_sqrt`, `FiniteProbability.sqrt_expectationReal_sq_add_le`, `FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`, `FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq` | Finite probability `L2` norm algebra: square-expectation nonnegativity, mixed Cauchy-Schwarz, triangle inequality, reverse triangle inequality, and the Bernoulli-coordinate specialization needed to control the Lipschitz constant of the conditional-second-moment section norm | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This closes the L2-section norm dependency of the tensorization induction, but the actual finite-cube induction and resulting product-measure concentration theorem remain open. |
| A3.4-S18 | Local `FiniteProbability.lean`; Ledoux tensorization induction route | `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add` | Abstract Bernoulli-product induction lift: any entropy-gradient bound for a finite law `P` and coordinate-move family `step` lifts to `P x Bool` after adding the new Bernoulli-coordinate squared-difference term and lifting the old-coordinate terms through the finite `L2` section-norm bridge | Closed locally by focused `lake build LeanFpAnalysis.FP.Analysis.FiniteProbability`. This closes the reusable induction-lift dependency; the concrete `RademacherTrace m` finite-cube theorem is now closed separately in A3.4-S19. |
| A3.4-S19 | Local `Preconditioning.lean`; concrete Bernoulli-cube iteration route | `rademacherTraceFlip`, `rademacherTraceProbMass_snoc`, `rademacherTraceProbability_expectationReal_succ_last_eq`, `rademacherTraceProbability_expectationReal_succ_eq_prod`, `rademacherTraceProbability_entropyReal_succ_eq_prod`, `rademacherTraceFlip_castSucc_snoc`, `rademacherTraceFlip_last_snoc`, `rademacherTraceProbability_entropyReal_sq_le_sum_flip` | Concrete finite-cube entropy-gradient theorem for positive functions on `RademacherTrace m`, obtained by splitting off the last Boolean coordinate with `Fin.snoc`, transporting expectation/entropy across `RademacherTrace (m+1) ≃ RademacherTrace m × Bool`, and iterating the abstract Bernoulli-product induction lift over coordinate flips | Closed locally by focused `lake build LeanFpAnalysis.FP.Algorithms.RandNLA.Preconditioning`. The row-norm-specific exponential-tilt flip-gradient and SRHT row-norm/leverage tails are closed separately in A3.4-S22--A3.4-S24; the fully general product-measure convex-Lipschitz proposition remains advisory and is not needed by the current Algorithm 3 SRHT theorem. |
| A3.4-S20 | Local `Preconditioning.lean`; entropy-gradient-to-exponential-tilt reduction | `rademacherTraceProbability_entropyReal_exp_mul_le_of_flip_tilt_sq_sum_bound`, `rademacherTraceProbability_eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_flip_tilt_sq_sum_bound` | Applies the concrete cube entropy-gradient theorem to the positive tilt \(g(\omega)=\exp(\lambda X(\omega)/2)\), reducing the visible finite-Herbst entropy hypothesis to a deterministic squared flip-gradient estimate for that tilt, then composes the result with the closed finite Herbst/Chernoff adapter | Closed locally. It remains available as a reusable conditional reduction; the row-norm-specific tilt-gradient condition is now closed separately in A3.4-S23. |
| A3.4-S21 | Local `FiniteProbability.lean` and `Preconditioning.lean`; scalar/symmetrization layer for tilt gradients | `real_exp_sub_one_le_mul_exp`, `real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp`, `real_exp_half_sub_sq_le_two_mul_half_diff_sq`, `rademacherTraceFlip_involutive`, `rademacherTraceFlipEquiv`, `rademacherTraceProbMass_flip`, `rademacherTraceProbability_expectationReal_flip`, `rademacherTraceProbability_flip_tilt_sq_sum_le_of_pointwise_pair_le`, `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_pair_le`, `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_halfdiff_sq_le`, `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_absdiff_le` | Scalar exponential half-tilt bound plus finite Rademacher flip-invariance/symmetrization: pointwise half-difference or coordinatewise absolute-difference bounds now imply the conditional squared flip-gradient expectation bound. | Closed locally by focused builds of `LeanFpAnalysis.FP.Analysis.FiniteProbability` and `LeanFpAnalysis.FP.Algorithms.RandNLA.Preconditioning`. This is a reusable but non-sharp coordinatewise bridge. The source-sharp positive-drop self-bounding route is no longer open here: it is closed by A3.4-S22--A3.4-S27, ending in the SRHT row-norm/leverage tails, exact product-law composition, and FP constant-budget transfer. |
| A3.4-S22 | Local `MatrixAlgebra.lean` and `Preconditioning.lean`; signed-Hadamard row-norm self-bounding route | `vecNorm2_inv_smul_self_of_pos`, `vecInnerProduct_inv_smul_self_eq_norm`, `vecNorm2_sub_le_inner_unit_diff`, `rademacherSignVector_flip_self`, `rademacherSignVector_flip_of_ne`, `rademacherSignVector_sub_flip`, `signedHadamard_row_inner_sq_sum_eq_inv_mul`, `signedHadamard_row_vec_sub_flip`, `signedHadamard_row_vecNorm2_positive_flip_sq_sum_le` | Sharp deterministic positive-flip self-bounding estimate for the concrete signed-Hadamard row-norm function \(F_i(\omega)=\|(H\operatorname{diag}\varepsilon(\omega)U)_{i,*}\|_2\): \(\sum_k\max(F_i(\omega)-F_i(\omega^k),0)^2\le 4/m\). | Closed locally with two weak-component passes. |
| A3.4-S23 | Local `FiniteProbability.lean` and `Preconditioning.lean`; positive-drop tilt-gradient bridge | `real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le`, `real_exp_half_sub_sq_le_lam_sq_quarter_pair_pos`, `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_posdiff_sq_sum_le`, `rademacherTraceProbability_flip_tilt_sq_sum_bound_signedHadamard_row_vecNorm2` | Converts the deterministic positive-drop self-bound into the exponential-tilt squared flip-gradient hypothesis with constant \(2/m\). | Closed locally by focused builds of `LeanFpAnalysis.FP.Analysis.FiniteProbability` and `LeanFpAnalysis.FP.Algorithms.RandNLA.Preconditioning`. |
| A3.4-S24 | Local `Preconditioning.lean`; source-sharp SRHT row-norm and leverage tails | `rademacherTraceProbability_eventProb_vecNorm2_signedHadamard_le_mean_add_ge_one_sub_exp_m_t_sq_div_eight`, `rademacherTraceProbability_eventProb_forall_vecNorm2_signedHadamard_le_sqrt_add_ge_one_sub_m_exp_m_t_sq_div_eight`, `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight`, `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_m_exp_m_t_sq_div_eight`, `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_delta`, `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_log_delta_ge_one_sub_delta`, `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta` | One-row SRHT row-norm tail, all-row row-norm flattening, squared row-norm form, equation-(6) leverage-probability cap in explicit-`t`/budget form, and logarithmic \(t=\sqrt{8\log(m/\delta)/m}\) target-failure form. | Closed locally by focused build of `LeanFpAnalysis.FP.Algorithms.RandNLA.Preconditioning`. |
| A3.4-S25 | Local `UniformRowSamplingComposition.lean`; source-sharp Algorithm 3 exact sampling composition | `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht`, `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess` | Composes the source-sharp SRHT preprocessing event with iid uniform row-sampling matrix concentration on the product law, both in explicit-`t` form and with the logarithmic preprocessing failure-budget choice substituted. | Closed locally by focused build of `LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingComposition`. |
| A3.4-S26 | Local `MatrixConcentration.lean`; logarithmic SRHT preprocessing-budget algebra | `real_sqrt_eight_log_div_pos_of_pos_lt`, `real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq` | Scalar source-constant algebra: for `0 < δ < B`, \(t=\sqrt{8\log(B/\delta)/B}\) is positive and gives \(B\exp(-Bt^2/8)=\delta\). | Closed locally by focused build of `LeanFpAnalysis.FP.Analysis.MatrixConcentration`; reused by A3.4-S24 and A3.4-S25. |
| A3.4-S27 | Local `UniformRowSamplingFP.lean`; source-sharp Algorithm 3 FP transfer | `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht`, `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess` | Transfers the source-sharp SRHT exact product-law event to rounded row scaling and rounded Gram dot products, deriving the fixed FP perturbation budget from the SRHT row-norm event itself. | Closed locally by focused build of `LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP`. |

### Active Lean Target

The active SRHT concentration target has moved past the previous red
tilt-gradient bottleneck, logarithmic preprocessing-budget wrapper, and
source-sharp floating-point transfer.  The SRHT branch is closed; broader
Gaussian/FJLT/input-sparsity uniformization requires separate proof-source
rows if brought into scope.

Broader Gaussian/FJLT/input-sparsity uniformization remains a separate
paper-level route, not part of the current SRHT closure.

## Resolved Proof-Source Chain: A2.7-B1 Leverage Rank-One Concentration

This source route replaced the coarse Frobenius/Markov leverage equation (7)
theorem with a finite-dimensional Loewner/Bennett subspace-embedding theorem
that is strong enough to feed the equation (8) leverage-score least-squares
sample-budget corollary.

### Paper Claim

CACM Algorithm 2 with equation (6) samples rows from an orthonormal basis
\(U\in\mathbb R^{m\times n}\) using
\[
  p_i=\|U_{i*}\|_2^2/n.
\]
Equation (7) states a high-probability subspace-embedding bound for
\(U^T S^T S U-I\). The CACM paper cites the result as part of the
RandNLA least-squares/sketching theory rather than proving the full
matrix-concentration theorem in the survey article.

### Source Chain

| Step | Source | Exact location | Needed Lean target | Local status |
|---|---|---|---|---|
| A2.7-S1 | Drineas--Mahoney CACM survey, DOI <https://dl.acm.org/doi/10.1145/2842602> | Algorithm 2, equations (6)--(7) | Source-aligned leverage-score row-sampling event | Closed locally in finite-Loewner sample-budget form, with a separate older Frobenius/Markov opNorm2 corollary |
| A2.7-S2 | Drineas, Mahoney, Muthukrishnan, and Sarlos, "Faster Least Squares Approximation," Numerische Mathematik 117 (2011), author PDF <https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_NumMath_2011.pdf> | Appendix Theorem 4 | Row/column sampling covariance approximation under probabilities \(p_i\ge\beta\|U_{i*}\|^2/\|U\|_F^2\); for \(U^TU=I\), this specializes to leverage sampling with \(\|U\|_F^2=n\) | Advisory source route; not a Lean theorem yet |
| A2.7-S3 | Oliveira, "Sums of random Hermitian matrices and an inequality by Rudelson," arXiv:1004.3821, <https://arxiv.org/abs/1004.3821> | Lemma 1 and surrounding rank-one covariance concentration setup | Finite product-law rank-one covariance concentration theorem from PSD summands, identity expectation, and a uniform Loewner bound | Closed locally in finite-Loewner exponential-tail and Bennett sample-budget forms |
| A2.7-S4 | Local `RowSamplingGram.lean` and `RowSamplingLeverage.lean` | `rowOuterGramSample_eq_zero_of_prob_zero`, `finiteQuadraticForm_rowOuterGramSample_eq_sq_div`, `finitePSD_rowOuterGramSample`, `leverage_rowOuterGramSample_finitePSD`, `leverage_rowOuterGramSample_mean_eq_id`, `leverage_rowOuterGramSample_finiteLoewnerLe_nat` | One-sample PSD, expectation \(I_n\), and \(Y_iY_i^T/p_i\preceq nI\) side conditions | Closed locally |
| A2.7-S5 | Local `RowSamplingTraceMGF.lean` | `rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le`, `rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`, `rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one` | Product-law trace-MGF iteration, finite-real adapter, and scalarization bridge for Algorithm 2 row traces | Closed locally |
| A2.7-S6 | Local `RowSamplingLeverageMGF.lean` reusing `Analysis/LiebTrace.lean` and `Analysis/MatrixConcentration.lean` | `leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero`, `leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq`, `leverage_rowOuterGramSample_centered_log_cgf_le`, `leverage_rowOuterGramSample_neg_centered_log_cgf_le`, `real_bernstein_tail_le_half_delta_of_quadratic_budget`, `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`, `leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget` | Centered one-sample leverage covariance Bernstein log-CGF bounds, exact variance, row-trace MGF composition, two-sided finite-Loewner exponential-tail theorem, Bennett sample-budget theorem, and sharper FP transfer | Closed locally |

### Next Lean Target

The A2.7 proof-source chain is closed for the finite-Loewner sample-budget
interpretation of equation (7).  The next paper-level frontier is no longer
this row; continue with the next open ledger item, or optionally add a cosmetic
single-denominator simplification of the two displayed Bennett budgets.

## Historical Proof-Source Chain: A1.5-B1 Closed

The `A1.5-B1` proof-source chain below is retained as the source audit trail.
It is no longer an active bottleneck for the cited square source-aligned
theorem: the final exact source sample-budget theorem, deterministic
truncation transfer, and support-aware floating-point gamma-budget transfer are
now formalized locally.  Future proof-source acquisition should target the next
open row in the not-proved ledger unless the user explicitly asks for the
optional untruncated/general-rectangular Algorithm 1 variant.

### Paper Claim

CACM Algorithm 1, equation (2), states that element-wise sampling with
probabilities proportional to squared magnitudes yields a high-probability
spectral-norm residual bound of order
\[
  \|A-\widetilde A\|_2
  \lesssim
  \sqrt{\frac{(m+n)\log(m+n)}{s}}\ \|A\|_F .
\]

The CACM article explicitly says the proof uses the zero-mean and bounded
variance structure of the residual matrix, and cites Drineas--Zouzias and
matrix measure concentration literature.

### Source Chain

| Step | Source | Exact location | Needed Lean target | Local status |
|---|---|---|---|---|
| A1.5-S1 | Drineas--Mahoney CACM survey | Algorithm 1 and equation (2) | Source-aligned statement of element-wise spectral residual event | The faithful literal-law Frobenius/Markov FP fallback is closed by `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square`. The literal support-radius trace-MGF route is closed in free-`theta` and Bennett-denominator forms by `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_scaled_radius_gamma_supportRadius` and `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius`; it is nonconditional and fully charges FP arithmetic, but its sample budget depends on the reciprocal-entry scale `H(A)`. The literal source-rate no-small-entry specialization is closed by `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square` and `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square`. The fully unconditional sharp literal matrix-Bernstein/Khintchine equation (2) theorem with no reciprocal-entry, truncation, or no-small-entry dependence remains open. The closed source theorem below is only for a hard-thresholded variant |
| A1.5-S1a | Same CACM survey plus the local Tropp/Bernstein literal support-radius route | Algorithm 1 and equation (2), stated for literal squared-magnitude sampling with an explicit nonzero-entry floor | Readable exact and floating-point literal support-radius theorem with all reciprocal-entry terms bounded by `alpha` | Closed locally by `elementwiseLiteralContributionRadius_le_of_entry_abs_ge`, `elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge`, `smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge`, `algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_entry_floor`, and `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_entry_floor`. This row gives the interpretable floor-bound surface `G(A) <= m*n*||A||_F^2/alpha`, `H(A) <= ||A||_F + m*n*||A||_F^2/alpha`, sample-budget order `Theta(((max(m,n)||A||_F^2 + H_alpha(A)r)log((m+n)/delta))/r^2)`, and rounded radius order `Theta(r + sqrt(m*n)*m*n*||A||_F^2*gamma_{s+1}/alpha)`. The floor is an explicit theorem hypothesis; it does not close the fully source-uniform literal equation (2) theorem. |
| A1.5-S2 | Drineas--Zouzias, "A Note on Element-wise Matrix Sparsification via a Matrix-valued Bernstein Inequality," arXiv:1006.0407 / IPL 111 (2011), 385--389, <https://arxiv.org/abs/1006.0407> | Algorithm 1 and Theorem 1 | Truncated elementwise sampler with \(s\) chosen from the theorem implies \(\|A-\widetilde A\|_2\le \varepsilon\) with high probability | Closed locally by the source sample-budget theorem plus deterministic truncation transfer for the square route and by the rectangular hard-thresholded route `sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect`; the literal no-small-entry specializations `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square` and `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_rect` are closed only when the source threshold is proved to be the identity on the literal input. |
| A1.5-S3 | Same Drineas--Zouzias paper | Section 4, Lemmas 1--4 | Prove truncation cost, sampled-half spectral event, and combine them | Closed locally for hard-thresholded source variants: square with `tau=eps/(2n)` and rectangular with `tau=eps/(2*sqrt(m*n))` |
| A1.5-S4 | Same Drineas--Zouzias paper | Proof of Lemma 4, application of "Theorem 2" matrix Bernstein | Instantiate finite matrix Bernstein for the retained residual increments | Closed locally by the specialized trace-MGF/Bernstein route; not packaged as a general reusable theorem |
| A1.5-S5 | Tropp, "User-friendly tail bounds for sums of random matrices," Found. Comput. Math. 12 (2012), 389--434, arXiv:1004.4389, <https://arxiv.org/abs/1004.4389> and journal DOI <https://doi.org/10.1007/s10208-011-9099-z> | Theorem 3.2 and Corollary 3.3 | Lieb trace concavity and one-step trace expectation inequality | Closed locally by `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`, `liebTraceConcavityTarget_all`, and `FiniteProbability.expectationReal_trace_normed_exp_add_le`; no Lieb hypothesis is hidden. |
| A1.5-S6 | Same Tropp paper | Theorem 3.6 and Corollary 3.7 | Trace-MGF domination for independent self-adjoint sums | Last-mile MGF-to-eigenvalue Markov, one-step trace-MGF, iid product-law trace-MGF iteration, the finite-real trace-exponential adapter, the scalar Bernstein parabola with constants, the explicit CFC scalar-to-operator Bernstein-parabola lift, the generic centered one-sample log-CGF variance proxy, the support-aware log-CGF variants, and the Algorithm 1 truncated dilation-increment instantiation `sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le` are closed locally. The remaining source target is the Bernstein/Khintchine tail conversion needed for the CACM equation (2) constants. |
| A1.5-S7 | Same Tropp paper | Theorem 1.4 and Theorem 1.6 | Matrix Bernstein and rectangular matrix Bernstein via self-adjoint dilation | Self-adjoint dilation and variance prerequisites are now sharpened for the literal rectangular law by `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect`, `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect`, and `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect`, giving the exact proxy \(\max(m,n)\|A\|_F^2/s^2\). The rectangular hard-thresholded trace-MGF/two-sided scaled-eigenvalue skeleton consumes that proxy through `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect`, `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect`, `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_rect`, and `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_rect`; the downstream `theta` optimization, Bernstein denominator, rectangular sample-budget simplification, truncation transfer, and FP gamma-radius wrappers are now closed by `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_rect`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_rect`, `sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect`, and `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_rect`. The literal no-small-entry square and rectangular specializations are closed by `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square`, `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_rect`, and `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_rect`; these use the source theorem only after proving the thresholded input equals the literal input. The scalar independent-copy symmetrization dependency is closed by `FiniteProbability.expectationReal_abs_sub_mean_le_prod_expectationReal_abs_sub`, `FiniteProbability.expectationReal_abs_le_prod_expectationReal_abs_sub_of_expectation_eq_zero`, and the Algorithm 1 instantiation `sqMagTraceProbability_expectationReal_abs_rectSelfAdjointDilation_elementwiseTraceResidual_le_prod_abs_sub`; the fixed-vector Euclidean independent-copy layer is closed by `FiniteProbability.expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2`, `FiniteProbability.expectationReal_vecNorm2_sub_mean_le_prod_expectationReal_vecNorm2_sub`, `FiniteProbability.expectationReal_vecNorm2_le_prod_expectationReal_vecNorm2_sub_of_expectation_eq_zero`, and `sqMagTraceProbability_expectationReal_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_prod_vecNorm2_sub`; and the operator-predicate all-copy-differences bridge is closed by `FiniteProbability.rectOpNorm2Le_of_entrywise_mean_zero_of_copy_diff_rectOpNorm2Le`, `sqMagTraceProbability_rectOpNorm2Le_elementwiseTraceResidual_of_all_copy_diffs`, `algorithm1ExactAllCopyDiffSpectralEvent_subset_exactSpectralEvent`, and `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_of_all_copy_diff`. The literal support route is also formally ruled out for a uniform deterministic radius by `exists_sqMagPositive_sampleResidualIncrement_not_rectOpNorm2Le` and at the event level by `sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_smallEntry_pos`: small nonzero entries create positive-probability residual increments with arbitrarily large operator action, and the one-step exact product law assigns positive probability to the bad spectral-radius event. The nonuniform literal support-radius Bernstein route is closed by `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bennett_radius_supportRadius`, `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius`, and the FP scalar wrapper `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius`. The source-uniform literal Bernstein/Khintchine tail theorem remains open exactly at the probability tail for the all-copy-differences event, without a uniform deterministic support radius, or else the theorem statement must retain reciprocal-entry/truncation/no-small-entry dependence. |
| A1.5-S8 | Tropp, "An Introduction to Matrix Concentration Inequalities," preprint, <https://tropp.caltech.edu/books/Tro14-Introduction-Matrix-preprint.pdf> | Theorem 8.1.1; Definition 8.1.2; Proposition 8.1.3; Theorem 8.1.4; Lemma 8.1.6; equation (8.1.2); Proposition 8.3.5; Section 8.3.5; Sections 8.6--8.8; equation (8.8.1) | Alternate exposition of Lieb concavity and the relative-entropy proof route | The relative-entropy route is closed locally through the Effros product-index perspective bridge: `cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`, `cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`, `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`, `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`, and `liebTraceConcavityTarget_all`. The iid trace-MGF iteration, finite-real trace-exponential adapter, scalar Bernstein parabola/constants, CFC scalar-to-operator Bernstein-parabola lift, generic one-sample log-CGF variance proxy, support-aware variants, and Algorithm 1 truncated dilation instantiation are also closed; the remaining Tropp-monograph source target is the matrix Bernstein/Khintchine tail layer and final constant optimization. |
| A1.5-S9 | Tropp, "From joint convexity of quantum relative entropy to a concavity theorem of Lieb," Proc. Amer. Math. Soc. 140(5), 1757--1760, 2012, arXiv:1101.1070, <https://arxiv.org/abs/1101.1070>, DOI <https://doi.org/10.1090/S0002-9939-2011-11141-9> | Abstract and paper route | Source explicitly reduces Lieb concavity to joint convexity of quantum relative entropy plus the Carlen--Lieb argument | Advisory source for the next bottleneck route; not formalized locally and not used as a hidden hypothesis |
| A1.5-S10 | Edward G. Effros, "A Matrix Convexity Approach to Some Celebrated Quantum Inequalities," Proc. Natl. Acad. Sci. USA 106(4), 1006--1008, 2009, arXiv:0802.1234, <https://arxiv.org/abs/0802.1234>, DOI <https://doi.org/10.1073/pnas.0807965106> | Theorem 2.1, Theorem 2.2, and Corollary 2.3: Hansen-Pedersen-Jensen, matrix perspective, and relative-entropy joint convexity route | Primary route for proving joint convexity via the operator-convex perspective \(L_A R_X^{-1}\) or equivalent finite-dimensional matrix perspective machinery | Closed locally for the finite-dimensional `CStarMatrix` target by the product-index perspective trace and equality bridge. The theorem is used as a formalized local proof route, not as a citation-only hypothesis. |
| A1.5-S11 | Göran Lindblad, "Completely positive maps and entropy inequalities," Communications in Mathematical Physics 40, 147--151, 1975, DOI <https://doi.org/10.1007/BF01609396> | Joint convexity/monotonicity lineage for quantum relative entropy | Historical primary source for the theorem Tropp labels as Lindblad's joint-convexity theorem | Advisory source only; the current chosen Lean route is the Effros/Tropp matrix-perspective proof because it is closer to finite matrix algebra |
| A1.5-S12 | Frank Hansen and Gert K. Pedersen, "Jensen's Operator Inequality," Bulletin of the London Mathematical Society 35(4), 553--564, 2003, arXiv:math/0204049, <https://arxiv.org/abs/math/0204049> | Theorem 2.1 and inequality (5): definitive operator Jensen inequality for noncommutative convex combinations | Source foundation behind Effros's matrix perspective theorem for operator-convex functions; the standard proof uses block matrices, so the Lean target must expose all finite matrix sizes | The concrete `x log x` two-point Jensen target is now closed locally by `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`. The proof uses the previously closed all-finite ordinary operator-convexity input, block-column/range-reflection algebra, CFC pinching, compression/integral linearity, strict-positive compression, and the new nonlinear corner theorems `cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum` and `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`. The generic all-functions Hansen-Pedersen transfer theorem remains unproved and is not advertised as closed, but it is no longer needed for the concrete `x log x` dependency. |
| A1.5-S12a | Same Hansen--Pedersen source route | Block reflection should be usable as a unitary symmetry in the pinching route | Range-reflection unitary addendum | The reflection layer now also proves `cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent` and `cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`, registering \(2P-I\) in mathlib's `unitary` submonoid. This is formalized locally and is a substrate for the future CFC conjugation/pinching theorem; it does not close the nonlinear transfer theorem by itself. |
| A1.5-S12b | Same Hansen--Pedersen source route | CFC must commute with the unitary symmetry used in the pinching argument | Unitary-conjugation CFC substrate | Closed locally by `cstarMatrix_cfc_unitary_conj`, which proves \(f(UTU^*)=Uf(T)U^*\) for unitary finite C-star \(U\), self-adjoint \(T\), and \(f\) continuous on \(\sigma(T)\). The nonlinear pinching average/compression Jensen theorem remains open. |
| A1.5-S12c | Same Hansen--Pedersen source route | The reflection/pinching route must preserve the strict-positive CFC domain | Unitary-conjugation strict-positivity substrate | Closed locally by `cstarMatrix_unitary_conj_isStrictlyPositive` and `cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`, which prove strict positivity is preserved by unitary conjugation and by the range reflection \(2VV^*-I\) when \(V^*V=I\). The nonlinear pinching average/compression Jensen theorem remains open. |
| A1.5-S12d | Same Hansen--Pedersen source route | The compressed argument \(V^*DV\) must remain in the strict-positive domain when \(D=\operatorname{diag}(T_1,T_2)\) is strict positive and \(V^*V=I\) | Block-compression strict-positivity substrate | Closed locally by `cstarMatrix_isStrictlyPositive_of_matrix_posDef`, `cstarMatrixColumnPair_mulVec_injective_of_sum`, `cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and `cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum`. The nonlinear compression/Jensen theorem remains open. |
| A1.5-S12e | Same Hansen--Pedersen source route | The pinching route needs the algebraic identities that compression by \(V\) is unchanged after averaging \(D\) with \(RDR\), that the averaged block is invariant under/commutes with \(R=2VV^*-I\), that it commutes with \(VV^*\), and that its action on \(V,V^*\) factors through the compressed corner | Algebraic pinching-average compression/invariance/range-reduction substrate | Closed locally by `cstarMatrix_mul_projectionReflection_of_mul_eq_self`, `cstarMatrix_reflectionAverage_compression_of_fixed`, `cstarMatrix_reflectionAverage_conj_of_involutive`, `cstarMatrix_reflectionAverage_commute_of_involutive`, `cstarMatrix_commute_projection_of_commute_reflection`, `cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum`, `cstarMatrixColumnPair_reflectionAverage_compression_of_sum`, `cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum`, `cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`, `cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`, `cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute`, `cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute`, `cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum`, and `cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum`, with rectangular distributivity/scalar helpers. This proves \(V^*R=V^*\), \(V^*((D+RDR)/2)V=V^*DV\), \(R((D+RDR)/2)R=(D+RDR)/2\), \(R((D+RDR)/2)=((D+RDR)/2)R\), commutation with \(VV^*\), and range-reduction identities through \(V^*DV\). The nonlinear CFC pinching/Jensen theorem remains open. |
| A1.5-S12f | Same Hansen--Pedersen source route | Ordinary operator convexity and unitary CFC conjugation should give the reflection-average pinching inequality before the corner CFC step | Reflection-average CFC pinching inequality | Closed locally by `cstarMatrix_compression_nonneg`, `cstarMatrix_compression_mono`, `cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum`, and `cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`. This proves \(f((D+RDR)/2)\le (f(D)+Rf(D)R)/2\) and its compression \(V^*f((D+RDR)/2)V\le V^*f(D)V\), assuming the all-finite ordinary operator-convexity target. The remaining source-faithful step is the nonlinear corner identity \(V^*f((D+RDR)/2)V=f(V^*DV)\) or an Effros/perspective route that bypasses it. |
| A1.5-S12g | Same Hansen--Pedersen source route plus the direct shifted-inverse integral route | The nonlinear corner identity can be attacked first on the shifted inverse kernels that reconstruct \(x\log x\) by the already formalized integral representation | Shifted-inverse corner identity for the reflection-average block | Closed locally by `cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq`, `cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq`, and `cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum`. This proves \(V^*(sI+(D+RDR)/2)^{-1}V=(sI+V^*DV)^{-1}\) for \(s>0\) and strict-positive \(D\). It is superseded by the later compression/integral assembly and concrete two-point Jensen theorem `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`; the current open source theorem is the finite Effros perspective / relative-entropy joint-convexity layer. |
| A1.5-S13 | Julius Bendat and Seymour Sherman, "Monotone and convex operator functions," Trans. Amer. Math. Soc. 79 (1955), 58--71, DOI <https://doi.org/10.1090/S0002-9947-1955-0082655-4>, AMS PDF <https://www.ams.org/journals/tran/1955-079-01/S0002-9947-1955-0082655-4/S0002-9947-1955-0082655-4.pdf> | Section 3 main convexity/monotonicity theorem: matrix convexity is characterized through monotonicity of divided differences | Alternate proof route for `cstarMatrixXLogXPositiveOperatorConvexTarget`, using operator monotonicity of logarithmic divided differences | Advisory alternate source plus local route targets: the derivative and divided-difference monotonicity layers are formalized through `cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone`, `cstarMatrixXLogXDividedDifferenceMonotoneTarget`, and `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`, with the conditional adapter `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`. The finite Bendat-Sherman bridge theorem itself is still not formalized, but the chosen direct unit-interval shifted-inverse route has already closed ordinary `x log x` operator convexity, so this bridge is no longer the selected blocker for A1.5-B1. |
| A1.5-S14 | Standard finite-matrix Schur-complement proof; locally formalized through mathlib's `Matrix.PosDef.fromBlocks₁₁` theorem and the direct unit-interval kernel route | Arithmetic-harmonic mean / inverse convexity of the positive-definite cone, shifted inverse kernels, and the integral representation of \(x\log x\) | Direct integral-representation route for operator convexity of \(x\log x\), where shifted inverse kernels are the key nonlinear term | Closed locally. The finite matrix substrate is closed by `matrix_posDef_inverse_schur_block`, `matrix_weighted_inverse_schur_block`, `matrix_posDef_weighted_sum`, and `matrix_inv_convex_posDef`, lifted to finite C-star/CFC inverse-kernel form by `cstarMatrix_nonneg_of_matrix_posSemidef`, `cstarMatrix_le_of_matrix_le`, and `cstarMatrix_cfc_inv_convex_isStrictlyPositive`, and shifted to the \(x\mapsto(s+x)^{-1}\), \(s>0\), family by `cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one` and `cstarMatrix_cfc_shifted_inv_convex_nonneg`. The actual reconstruction kernel was corrected to \(x(x-1)/(u+(1-u)x)\), not the auxiliary \((x-1)^2\) kernel. The scalar and CFC assembly are closed by `real_xlog_eq_unit_interval_xlog_kernel_integral`, `real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`, `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`, `continuousOn_uncurry_unit_interval_xlog_kernel_spectrum`, `real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`, `ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`, `hasFiniteIntegral_const_max_one_spectrum_bound_sq`, `cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`, `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`, and `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`. These are locally proved and not used as hidden hypotheses. |

### Chosen Route

Continue the Tropp matrix-Laplace route from the newly closed local Lieb
theorem toward the iterated independent-sum trace-MGF theorem.  It fits the existing
local infrastructure:
self-adjoint dilations, finite Loewner/PSD order, Hermitian eigenvalue
bridges, matrix-exponential trace interfaces, complex C-star embeddings,
operator-log monotonicity, trace positivity/monotonicity, finite
C-star-valued expectation, finite Jensen, local relative-entropy
joint convexity, and one-step trace-MGF domination are already formalized.

### Deferred Routes

- Ahlswede--Winter/Golden-Thompson route: older and potentially weaker for
  constants; would require Golden-Thompson and trace-exponential iteration
  foundations that are not currently local.
- Covering-net route: product-grid cover geometry is now local, but this route
  still requires explicit fine grids and sharp scalar tails for every net
  vector.  It is more elementary than Lieb but less source-faithful to the
  Drineas--Zouzias/Tropp chain.
- Noncommutative Khintchine route: useful for some spectral norm estimates,
  but the current Algorithm 1 source chain and local prerequisites are closer
  to matrix Bernstein.

### Bottleneck Theorem

The finite-dimensional Lieb trace-concavity foundation is now closed locally
for complex C-star matrices:
\[
  A \mapsto \operatorname{Re}\operatorname{tr}
  \exp\!\bigl(H+\log A\bigr)
\]
is concave on the strictly positive cone, for fixed self-adjoint \(H\).
The finite Jensen adapter now yields the one-step Tropp inequality
\[
  \mathbb E\,\operatorname{tr}\exp(H+X)
  \le
  \operatorname{tr}\exp\!\left(H+\log \mathbb E\,\exp X\right),
\]
using the repository's chosen `CStarMatrix` exponential/log vocabulary.

Current target status: **open foundation** for the iterated independent-sum
trace-MGF domination and matrix Bernstein/Khintchine layers.  The closed local
Lean names are
`cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`,
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`,
`liebTraceConcavityTarget_all`, and
`FiniteProbability.expectationReal_trace_normed_exp_add_le`.
The chosen relative-entropy branch also has scalar/vector
relative-entropy nonnegativity via `realRelativeEntropy_nonneg` and
`finiteRealRelativeEntropy_nonneg`, the finite log-sum inequality
`finite_log_sum_inequality`, scalar/vector joint convexity via
`realRelativeEntropy_jointConvex` and
`finiteRealRelativeEntropy_jointConvex`, plus the local C-star vocabulary
`cstarMatrixRelativeEntropy`, diagonal normalization theorem
`cstarMatrixRelativeEntropy_self`, and scalar-identity matrix case
`cstarMatrixRelativeEntropy_algebraMap_real_nonneg`.  It also has the real
diagonal matrix case via `cstarMatrix_log_realDiagonal`,
`cstarMatrixRelativeEntropy_realDiagonal`, and
`cstarMatrixRelativeEntropy_realDiagonal_nonneg`, reducing the C-star matrix
expression on real diagonals to finite-vector relative entropy, and the
real-diagonal joint-convexity subcase via
`cstarMatrixRelativeEntropy_realDiagonal_jointConvex`.  It now also
has the left/right multiplication endomorphism substrate for the Effros
operator-perspective route via `cstarMatrixLeftMul`, `cstarMatrixRightMul`,
their real weighted-sum laws, `cstarMatrixLeftRightMul_commute`, and the
strict-positivity-to-endomorphism-unit lemmas
`cstarMatrixLeftMul_isUnit_of_isStrictlyPositive` and
`cstarMatrixRightMul_isUnit_of_isStrictlyPositive`.  It also has the
product/power algebra for this endomorphism layer via
`cstarMatrixLeftMul_mul`, `cstarMatrixRightMul_mul`,
`cstarMatrixLeftMul_pow`, and `cstarMatrixRightMul_pow`.  It also has the
explicit ratio endomorphism \(L_X R_A^{-1}\) via
`cstarMatrixLeftRightRatio`, `cstarMatrixLeftRightRatio_apply`,
`cstarMatrixLeftRightRatio_apply_unit`,
`cstarMatrixLeftRightRatio_apply_of_unit_eq`, and
`cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive`.  It also has the
finite Kronecker lift substrate for the Tropp/Effros perspective route via
`matrix_kronecker_left_identity_real_smul_add`,
`matrix_kronecker_right_identity_real_smul_add`,
`matrix_kronecker_left_identity_mul_right_identity`,
`matrix_kronecker_right_identity_mul_left_identity`,
`matrix_kronecker_left_right_commute`,
`matrix_kronecker_posDef_left_identity`, and
`matrix_kronecker_posDef_right_identity`, plus trace normalization through
`matrix_trace_kronecker`, `matrix_trace_kronecker_left_identity`, and
`matrix_trace_kronecker_right_identity`.  It now also has the
Hansen-Pedersen source split via `cstarMatrixPositiveOperatorConvexTarget`,
the identity sanity theorem `cstarMatrixPositiveOperatorConvexTarget_id`,
the all-finite-size ordinary convexity target
`cstarMatrixPositiveOperatorConvexAllFiniteTarget`, the all-finite identity
sanity theorem `cstarMatrixPositiveOperatorConvexAllFiniteTarget_id`, the
transfer targets `cstarMatrixPositiveHansenPedersenTransferTarget` and
`cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`, the concrete
positive-cone `x log x` route targets
`cstarMatrixXLogXPositiveOperatorConvexTarget`,
`cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget`, and
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`, the assembled two-point target
`cstarMatrixHansenPedersenJensenTwoPointTarget`, the identity sanity theorem
`cstarMatrixHansenPedersenJensenTwoPointTarget_id`, and the concrete assembled
positive-cone `x log x` target
`cstarMatrixXLogXHansenPedersenJensenTarget`, with assembly adapter
`cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`.
Because ordinary `x log x` operator convexity is now closed locally, the
transfer-only bridge
`cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer` records that the
fixed-size target is blocked by the transfer theorem.  The source-faithful
all-finite bridge
`cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer` records that
the standard block-matrix route is blocked by
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`.  The block-column,
range-projection/reflection, block-diagonal star-algebra/order substrate, and
block-diagonal CFC decomposition for that standard proof are now locally closed in
`CStarMatrixBridge`/`LiebTrace` by
`cstarMatrixBlockDiagonal`, `cstarMatrixColumnPair`,
`cstarMatrixColumnPair_conjTranspose_mul_self`,
`cstarMatrixBlockDiagonal_mul_columnPair`,
`cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`,
`cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum`,
`cstarMatrixBlockDiagonal_star`, `cstarMatrixBlockDiagonal_mul`,
`cstarMatrixBlockDiagonal_isUnit`, `cstarMatrixBlockDiagonal_nonneg`, and
`cstarMatrixBlockDiagonal_isStrictlyPositive`, plus
`cstarMatrixColumnPairRangeProjection_mul_self_of_sum`,
`cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`,
`cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`, and
`cstarMatrixColumnPairRangeReflection_mul_self_of_sum`,
`cstarMatrixColumnPairRangeReflection_isUnit_of_sum`,
`cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`,
`cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`,
`cstarMatrixBlockDiagonal_cfc`, `cstarMatrix_cfc_unitary_conj`,
`cstarMatrix_unitary_conj_isStrictlyPositive`, and
`cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`,
`cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and
`cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum`,
`cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_compression_of_sum`,
`cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`,
`cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum`, and
`cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum`,
`cstarMatrix_compression_mono`,
`cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`;
`cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq`,
`cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq`, and
`cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum` close the
shifted-inverse kernel corner identity.  The compression/integral layer
`cstarMatrix_compression_setIntegral` and the unit-interval kernel corner
`cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum` now assemble
the full nonlinear corner
`cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`, which closes the
concrete two-point Hansen--Pedersen theorem through
`cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`.  The
affine-corrected normalized entropy-kernel target is also closed by
`realEntropyKernel`,
`cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel`,
`cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`,
`cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one`, and
`cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
The square-root side conditions for finite perspective statements are now also
closed by `cstarMatrixPositiveSqrt`, `cstarMatrixPositiveInvSqrt`,
`cstarMatrixPositiveSqrt_mul_self`, `cstarMatrixPositiveInvSqrt_mul_sqrt`,
`cstarMatrixPositiveSqrt_mul_invSqrt`,
`cstarMatrixPositiveInvSqrt_isUnit`,
`cstarMatrixPositiveInvSqrt_mul_self_mul`, and
`cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive`.
The next source theorem is the finite Effros superoperator perspective /
relative-entropy joint-convexity theorem, not this corner, affine-kernel, or
ordinary square-root assembly.
For the Bendat--Sherman alternate route it also has
`cstarMatrix_cfc_one_add_log_eq_one_add_log`,
`cstarMatrixXLogXDerivativeMonotoneTarget`, and
`cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone`, which close the
operator monotonicity of the formal derivative \(1+\log x\) but not the
source theorem or the missing operator-convexity target.  The source-faithful
first-divided-difference route is now named by
`realXLogXDividedDifference`,
`realXLogXDividedDifference_eq_log_add_ratio`,
`realXLogXDividedDifference_eq_log_add_normalized`,
`cstarMatrixXLogXDividedDifferenceMonotoneTarget`, and
`cstarMatrixBendatShermanDividedDifferenceBridgeTarget`.  The adapter
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`
records the conditional dependency wiring from the divided-difference route to
the concrete `x log x` operator-convexity target.  The earlier derivative-only
bridge name remains recorded as a diagnostic route artifact, not as the
source-faithful theorem.  The divided-difference monotonicity target is now
closed by
`cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`;
the remaining Bendat--Sherman step is the bridge from that monotonicity to
operator convexity, but it is now only an alternate route.  The selected direct
integral route has finite complex matrix inverse convexity closed by
`matrix_inv_convex_posDef`, finite C-star CFC inverse-kernel convexity closed
by `cstarMatrix_cfc_inv_convex_isStrictlyPositive`, the shifted-positive
inverse-kernel family closed by `cstarMatrix_cfc_shifted_inv_convex_nonneg`,
and the corrected \(x\log x\) kernel route closed by
`real_xlog_eq_unit_interval_xlog_kernel_integral`,
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
`cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`,
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`,
and `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
The ordinary `x log x` operator-convexity input is therefore closed locally;
the next open Hansen-Pedersen/Effros source dependency is the transfer/Jensen
or perspective layer, not this operator-convexity input.
It now also
has the conditional route theorem
`liebTraceConcavityTarget_of_relativeEntropy_route`, which derives
`liebTraceConcavityTarget H` from joint convexity plus the normalized
variational formula, and the optimizer-candidate equality
`cstarMatrixEntropyVariationalObjective_liebOptimizer` for the normalized
variational objective.  The maximality part of the normalized variational
formula is reduced to `cstarMatrixRelativeEntropyNonnegOnStrictPositive` by
`cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`.  After the
Hermitian-CFC bridge closure below, the variational formula is no longer open,
so the remaining route foundation is
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.  Finally,
nonnegativity is reduced to the source-aligned generalized Klein first-order
trace inequality by
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`.
The generalized Klein inequality itself is now proved by
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`,
using the compact Hermitian entropy trace inequality
`matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg` and the
C-star-to-plain-matrix positivity bridge
`cstarMatrix_isStrictlyPositive_to_matrix_posDef`.  This also closes local
matrix relative-entropy nonnegativity via
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`, the
normalized variational formula via
`cstarMatrixEntropyVariationalFormula_of_hermitianCfc`, and the reduction from
joint convexity alone to Lieb concavity via
`liebTraceConcavityTarget_of_relativeEntropy_jointConvex`.  These do not prove
general noncommutative matrix relative-entropy joint convexity, arbitrary
self-adjoint Lieb concavity, trace-MGF domination, matrix Bernstein/Khintchine,
or CACM equation (2).

Locality status: a repository/mathlib search on 2026-05-27 found no existing
quantum or matrix relative-entropy joint-convexity theorem, arbitrary-\(H\)
Lieb trace-concavity theorem, or matrix Bernstein theorem to reuse.  Mathlib
has scalar `convexOn_mul_log`, but
`.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
lists only `CFC.log_monotoneOn` as a main declaration and explicitly records
operator-log concavity and operator convexity of `x => x * log x` as TODOs in
its module header.  Therefore the local-reuse route for
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` and the assembled
`cstarMatrixXLogXHansenPedersenJensenTarget` is ruled out with evidence: the
needed Hansen-Pedersen transfer/Jensen theorem is not currently a hidden
mathlib theorem.  The ordinary `cstarMatrixXLogXPositiveOperatorConvexTarget`
is no longer open, because it is closed locally by
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
Its all-finite-size packaging is also closed locally by
`cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`.
The block-column compression identities, block-diagonal star/order laws, and
range-projection/reflection/block-diagonal CFC decomposition for the standard proof are also no longer open:
`cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`,
`cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum`,
`cstarMatrixBlockDiagonal_nonneg`, and
`cstarMatrixBlockDiagonal_isStrictlyPositive`, together with
`cstarMatrixColumnPairRangeProjection_mul_self_of_sum`,
`cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`,
`cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`, and
`cstarMatrixColumnPairRangeReflection_mul_self_of_sum`,
`cstarMatrixColumnPairRangeReflection_isUnit_of_sum`,
`cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`,
`cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`,
`cstarMatrixBlockDiagonal_cfc`, `cstarMatrix_cfc_unitary_conj`,
`cstarMatrix_unitary_conj_isStrictlyPositive`, and
`cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`,
`cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and
`cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum`,
`cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_compression_of_sum`,
`cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`,
`cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum`, and
`cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum`,
`cstarMatrix_compression_mono`,
`cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum`, and
`cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`,
plus the shifted-inverse corner family
`cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum`, the
compression integral theorem `cstarMatrix_compression_setIntegral`, and the
full corner theorem `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`
close the `[A;B]`/`diag(T1,T2)`
algebra/order/range-projection/reflection/CFC-conjugation/domain/compression/pinching-average
inequality layer and the concrete nonlinear \(x\log x\) Jensen step.  This
old source layer has now been superseded by the closed Effros
perspective/relative-entropy joint-convexity route.
The Kronecker substrate above uses existing mathlib
Kronecker-product algebra, trace factorization, and `Matrix.PosDef.kronecker`,
but it does not supply operator convexity, a matrix-perspective theorem, or
the relative-entropy trace representation.  The front-loaded source check for
the next theorem points to Hansen--Pedersen operator Jensen as the source
foundation for Effros's perspective theorem.  The Lean-facing source route is
now split into `cstarMatrixXLogXPositiveOperatorConvexTarget`,
`cstarMatrixXLogXHansenPedersenTransferTarget`, and then
`cstarMatrixXLogXHansenPedersenJensenTarget`; the concrete final target is now
closed by `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`,
while the generic transfer theorem remains unproved and is not needed for the
current concrete path.

## Other Open Paper-Level Source Rows

These rows are the current source-plan backlog after the A1.5-B1 source route
closed.  Before hard Lean work on any row, refresh the local search and inspect
the listed primary sources for the exact theorem shape and constants.

| Ledger row | Paper claim | Primary sources to inspect | Expected Lean foundations | Status |
|---|---|---|---|---|
| A2 spectral improvement | CACM discussion after equation (5): spectral norm requires Khintchine or matrix Bernstein | Rudelson--Vershynin, "Sampling from large matrices"; Tropp matrix Bernstein; Drineas--Kannan--Mahoney matrix multiplication paper | Matrix Khintchine/Bernstein, row-sampling variance proxies, operator norm events | Open |
| LS.3 | Equation (8) sampling/projection gives relative-error least-squares solution | Drineas--Mahoney--Muthukrishnan, "Sampling algorithms for l2 regression and applications"; Drineas--Mahoney--Muthukrishnan--Sarlos, "Faster least squares approximation"; Sarlos FOCS 2006 | Subspace embedding, residual preservation, sketched minimizer theorem, FP solver/preconditioner transfer | Deterministic bridge, preservation-to-objective probability transfer, exact/FP leverage operator-event adapters, concrete sampled-row LS objective algebra, canonical residual coordinates, the column/RHS representation adapter, the augmented-span orthonormal basis theorem, the direct finite-Loewner preservation bridge, exact/rounded-Gram augmented-span Bennett sample-budget LS theorems, literal rounded sampled-row residual/objective perturbation bounds, the high-probability literal rounded-minimizer transfer under explicit objective-budget slack, the additive solver-objective-gap transfer, the componentwise solver forward-error certificate transfer, the perturbed-Gram-system solver certificate transfer, the `LSQRSolveBackwardError` spec transfer, and the concrete normal-equations/Cholesky solver transfer are closed. Deriving the QR backward-error spec from concrete rectangular QR/preconditioner FP analysis and random-projection variants remain open |
| A3.4 | Algorithm 3 random projections uniformize leverage/importance scores | Ailon--Chazelle FJLT; Drineas--Magdon-Ismail--Mahoney--Woodruff leverage approximation; Clarkson--Woodruff and Meng--Mahoney input-sparsity embeddings; Tropp, "Improved analysis of the subsampled randomized Hadamard transform," Lemma 3.3 and Theorem 3.1 | Random projection model, FJLT/Gaussian/Rademacher concentration, leverage-score uniformization | SRHT/signed-Hadamard exact route closed locally: deterministic FP preprocessing, orthogonal Frobenius preservation, orthonormal-column basis preservation, equation (6) denominator preservation, SRHT sign-diagonal deterministic prerequisites, finite Rademacher sign law, probability-one signed-preprocessing support theorem, finite Rademacher moments, scalar signed-linear-form MGF/tail skeleton, scalar Hoeffding/two-sided signed-linear-form tail, coordinate-Hoeffding row-norm and leverage-probability auxiliaries, uniform one-step Loewner boundedness after the coordinate event, iid uniform sample-average concentration in tail-budget form, product-law preprocessing-plus-sampling composition, FP uniform-sketch transfer, `HadamardFlat`, flat-Hadamard expected row norm, source-directed expected Euclidean row norm, deterministic convexity/Lipschitz/self-bounding, positive-drop exponential-tilt concentration, source-sharp row-norm/leverage caps, logarithmic delta wrappers, exact SRHT-plus-uniform-row composition, source-sharp FP constant-budget transfer, computed-`Vhat` transfer surfaces, the exact-stored zero-transform-storage computed-left certificate, the exact-factor rounded signed-Hadamard preconditioner certificate, the rounded scale/sign-pattern table certificate and computed-left event wrapper, generated Sylvester/Walsh bit-parity sign-pattern certificates and computed-left event wrappers, the `fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0` stored-sign certificates and computed-left event wrappers, the scalar, vector-pair, propagated-input, ordered-schedule, one-stage generated-pair, rounded no-alias/list-order/no-touch generated-stage FHT certificates, stage-list append/range-succ, scaled-schedule, and columnwise scaled-schedule matrix FHT arithmetic adapters, the rounded sqrt-inverse FHT normalization-scale routine, the generic nonzero-error signed-Hadamard/sign-storage product certificate, the generic computed-input-basis transfer certificate, the computed-projector-from-basis certificate, the generic computed-denominator row-scaling transfer, the rounded-sqrt exact-input denominator certificate, the rounded division-then-square-root denominator certificate, and the rounded reciprocal-multiply-then-square-root denominator certificate. Remaining proof-source work is for non-SRHT Gaussian/FJLT/input-sparsity distributions, scale-normalization routines beyond the rounded sqrt-inverse FHT routine if used, layout-specific in-place overwrite, vectorized-layout, or storage certificates beyond the functional generated schedule and its same-stage no-alias/list-order/no-touch certificates, concrete QR/SVD/singular-vector routines, sign-storage formats beyond the three modeled rounded-copy paths, and denominator-normalization routines beyond the five closed uniform-row paths. |
| A3.4-FHT-generated-schedule | Algorithm 3 generated full Sylvester/Walsh FHT schedule, FP propagation, and stage-factorization bridge | Local Lean definitions plus standard Sylvester/Hadamard recurrence target; no new external source for the schedule/error/stage-factorization adapters themselves | Exact finite stage-list generation, list membership over `List.range p`, append/flatMap schedule composition, propagated FHT butterfly FP arithmetic, rounded square-root scale, columnwise computed-matrix packaging | Closed locally through `fhtSylvesterSchedulePairs`, `mem_fhtSylvesterSchedulePairs_iff`, `mem_fhtSylvesterSchedulePairs_iff_stage_rule`, `fhtPairScheduleExact_append`, `flFhtPairSchedule_append`, `fhtPairSchedulePropagatedErrorBudget_append`, `fhtPairScheduleExact_flatMap_sylvesterStagePairs`, `flFhtPairSchedule_flatMap_sylvesterStagePairs`, `fhtPairSchedulePropagatedErrorBudget_flatMap_sylvesterStagePairs`, `fhtSylvesterStageScheduleListExact_append`, `flFhtSylvesterStageScheduleList_append`, `fhtSylvesterStageScheduleListPropagatedErrorBudget_append`, `fhtSylvesterStageScheduleListExact_range_succ`, `flFhtSylvesterStageScheduleList_range_succ`, `fhtSylvesterStageScheduleListPropagatedErrorBudget_range_succ`, `fhtSylvesterScheduleExact_eq_stageScheduleListExact`, `flFhtSylvesterSchedule_eq_stageScheduleList`, `fhtSylvesterSchedulePropagatedErrorBudget_eq_stageScheduleList`, `flFhtSylvesterSchedule_propagated_error_bound`, `flFhtScaledSylvesterScheduleMatrix_sqrtInvNatScale_error_bound`, and `ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNat_entry_error_bound`. This row required only local list membership/composition facts and the previously closed `FPModel` butterfly/scale theorems. The transform-correctness theorem identifying the exact stage-by-stage recurrence with the Sylvester/Hadamard parity table is closed locally; remaining items are implementation-specific layout/storage/overwrite certificates beyond the functional generated-FHT preconditioner path. |
| A3.4-FHT-realization | Algorithm 3 generated FHT realization against the Sylvester/Walsh bit-parity table | Local Lean definitions plus the standard Sylvester/Walsh recurrence; no external source needed | Exact bit-parity matrix-vector application, partial-transform recurrence, range induction, scaled columnwise transfer, signed-input `H D U` bridge | Closed locally through `sylvesterHadamardPartialParityWeight_succ`, `sylvesterHadamardPartialSignPattern_succ_eq_or_neg`, `sylvesterHadamardPartialSignPattern_succ_eq_of_stage_bit_false`, `sylvesterHadamardPartialSignPattern_succ_eq_or_neg_of_stage_bit_true`, `sylvesterHadamardPartialParityWeight_eq_of_bits`, `sylvesterHadamardPartialSignPattern_eq_of_bits`, `sylvesterHadamardPartialSignPattern_upper_partner_eq_of_mod_lt`, `sylvesterHadamardPartialSignPattern_upper_eq_lower_partner_of_mod_ge`, `sylvesterHadamardPartialUnscaledApply_succ_lower`, `sylvesterHadamardPartialUnscaledApply_succ_upper`, `fhtSylvesterStageScheduleExact_partialUnscaledApply_eq_succ`, `fhtSylvesterStageScheduleListExact_range_eq_partialUnscaledApply`, `fhtSylvesterScheduleRealizesSignPattern_generated`, `fhtScaledSylvesterScheduleMatrixExact_eq_sylvesterHadamardScaledMatrixApply`, and `fhtScaledSylvesterScheduleMatrixExact_signed_eq_preconditionRows`, building on the earlier generated-stage coordinate, bit, partner, sign, and stage-list recurrences. Remaining proof-source work after exact realization is implementation-specific layout/storage/overwrite/copy certificates beyond the functional generated-FHT preconditioner path, non-SRHT Gaussian/FJLT/input-sparsity distributions, concrete QR/SVD/singular-vector routines, additional sign-storage formats, and extra denominator-normalization routines if an implementation uses them. |
| A3.4-FHT-fast-preconditioner | Algorithm 3 fast generated-FHT implementation path for `H D_ω` | Local Lean definitions; no external source needed beyond the generated FHT recurrence already closed | Computed diagonal sign input, exact diagonal FHT-to-`H D` bridge, rounded generated FHT `ComputedPreconditioner`, exact-law computed-left perturbation wrappers | Closed locally through `ComputedMatrix.flRowSignMul`, `ComputedMatrix.flRowSignMul_entry_error_bound`, `fhtScaledSylvesterScheduleMatrixExact_diag_eq_matMul_diag`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule_entry_error_bound`, `signedHadamardSylvesterFhtSchedulePreconditioner`, `signedHadamardSylvesterFhtScheduleStoredSignPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, and `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`. Remaining proof-source work is only for concrete array-layout overwrite/copy behavior if a selected implementation differs from the functional pair-update schedule. |
| A3.4-FHT-stored-add-zero-writeback | Algorithm 3 generated FHT implementation path with rounded add-zero output writeback/copy | Local Lean definitions; no external source needed beyond the generated FHT recurrence and local `FPModel.model_add` | Functional pair-update schedule followed by `fl_add(output,0)` writeback/copy at each pair update, propagated budgets, rounded sqrt-inverse scale, computed-matrix and computed-preconditioner packaging, exact-law computed-left perturbation wrappers | Closed locally through `flFhtPairUpdateStoredAddZeroRight`, `fhtPairUpdateStoredAddZeroRightPropagatedErrorBudget`, `flFhtPairUpdateStoredAddZeroRight_propagated_error_bound`, `flFhtPairScheduleStoredAddZeroRight_propagated_error_bound`, `flFhtSylvesterScheduleStoredAddZeroRight_propagated_error_bound`, `flFhtScaledPairScheduleStoredAddZeroRight_sqrtInvNatScale_error_bound`, `flFhtScaledPairScheduleMatrixStoredAddZeroRight_sqrtInvNatScale_error_bound`, `flFhtScaledSylvesterScheduleMatrixStoredAddZeroRight_sqrtInvNatScale_error_bound`, `ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNatStoredAddZeroRight_entry_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight_entry_error_bound`, `signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner`, `signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, and `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`. Remaining source work is only for array-memory orders, aliasing, overwrite semantics, vectorized layouts, or storage formats not represented by this pair-update plus add-zero writeback model. |
| A3.4-FHT-modified-add-zero-writeback | Algorithm 3 generated FHT implementation path with modified-coordinate rounded add-zero output writeback/copy | Local Lean definitions; no external source needed beyond the generated FHT recurrence and local `FPModel.model_add` | Functional pair-update schedule followed by `fl_add(output,0)` writeback/copy only on the two pair outputs modified at each pair update, propagated budgets with an explicit coordinate indicator, rounded sqrt-inverse scale, computed-matrix and computed-preconditioner packaging, exact-law computed-left perturbation wrappers | Closed locally through `flFhtPairUpdateModifiedStoredAddZeroRight`, `fhtPairUpdateModifiedStoredAddZeroRightPropagatedErrorBudget`, `flFhtPairUpdateModifiedStoredAddZeroRight_propagated_error_bound`, `flFhtPairScheduleModifiedStoredAddZeroRight_propagated_error_bound`, `flFhtSylvesterScheduleModifiedStoredAddZeroRight_propagated_error_bound`, `flFhtScaledPairScheduleModifiedStoredAddZeroRight_sqrtInvNatScale_error_bound`, `flFhtScaledPairScheduleMatrixModifiedStoredAddZeroRight_sqrtInvNatScale_error_bound`, `flFhtScaledSylvesterScheduleMatrixModifiedStoredAddZeroRight_sqrtInvNatScale_error_bound`, `ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNatModifiedStoredAddZeroRight_entry_error_bound`, `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight_entry_error_bound`, `signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner`, `signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner`, `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`, and `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`. Remaining source work is only for array-memory orders, aliasing, overwrite semantics, vectorized layouts, or storage formats not represented by this modified-coordinate writeback model. |
| LR.1 | Equation (9) structural low-rank approximation condition | Boutsidis--Mahoney--Drineas column subset selection; Halko--Martinsson--Tropp SIAM Review; Sarlos random projection low-rank analysis | Rectangular SVD, rank, projections, pseudoinverse, best rank-\(k\), unitarily invariant norms | Open; exact right-Gram PSD/order/nonnegativity adapter closed locally in LR.1by, basis-indexed right-Gram eigenvector/diagonalization adapter closed locally in LR.1bz, full-positive basis-indexed reconstruction adapter closed locally in LR.1ca, zero projected-column adapter closed locally in LR.1cb, zero-safe basis-indexed reconstruction adapter closed locally in LR.1cc, arbitrary selected-index head/tail plus rank-card packaging closed locally in LR.1cd, selected-head sketch-space factorization closed locally in LR.1ce, selected split equation-(9) certificate adapter closed locally in LR.1cf, selected cardinality rank handoff closed locally in LR.1cg, and injective selected-index embedding handoff closed locally in LR.1ch. Ordered top-singular-direction selection, rectangular source split existence, and Eckart--Young remain open |
| MC.1 | Equations (10)--(11) matrix completion via nuclear-norm minimization | Candes--Recht exact matrix completion; Recht simpler matrix completion; Gross recovery from few coefficients; Chen--Bhojanapalli--Sanghavi--Ward coherent matrix completion | Nuclear norm, incoherence/leverage, convex optimization, sampling model, dual certificate | Open |
| LAP.1 | Effective-resistance sampling sparsifies graph Laplacians and supports fast solves | Spielman--Srivastava graph sparsification by effective resistances; Batson--Spielman--Srivastava--Teng CACM; Koutis--Miller--Peng solver work | Graph Laplacian, incidence matrices, effective resistance/leverage equivalence, spectral sparsification, solver transfer | Open |

## Local Search Result

The local repository and bundled mathlib search found:

- local finite probability, Markov, Chebyshev, Chernoff, scalar MGF, finite
  Jensen, C-star expectation, and trace/eigenvalue adapters;
- mathlib operator-log monotonicity, already wrapped locally as
  `cstarMatrix_log_le_log`;
- mathlib logarithm/exponential inverse theorems, now wrapped locally as
  `log(exp X)=X` for self-adjoint `CStarMatrix` objects and `exp(log A)=A`
  for strictly positive `CStarMatrix` objects;
- no direct local or bundled mathlib proof of operator-log concavity; the
  bundled `ExpLog/Order.lean` file records operator-log concavity as future
  infrastructure while only exposing operator monotonicity locally available as
  `CFC.log_le_log`;
- no local Golden-Thompson theorem;
- a local finite-dimensional Lieb trace-concavity theorem, one-step trace-MGF
  theorem, iid product-law trace-MGF iteration, and the source-aligned
  Algorithm 1 Bernstein specialization;
- no reusable general-purpose matrix Bernstein or matrix Khintchine theorem
  packaged independently of the Algorithm 1 source-aligned route.

Therefore A1.5-B1 is a genuine proof-source bottleneck, not a failure to reuse
an already present local theorem.  The active blocker is tracked separately in
`docs/RANDNLA_CACM_BOTTLENECK_LEDGER.md`.

## Next Concrete Proof Queue

1. Closed: state the finite-dimensional Lieb trace-concavity target and its
   strictly-positive domain in
   `LeanFpAnalysis/FP/Analysis/LiebTrace.lean`.
2. Search mathlib for lower-level ingredients: differentiability/Fréchet
   derivative of matrix log/exp, convexity of trace exponential, relative
   entropy, or available CFC concavity infrastructure.
3. If the direct Lieb proof is too large, split the route into named
   dependencies: strict-positive cone convexity (closed by
   `strictPositiveCStarMatrixCone_convex`), self-adjointness of `H + log A`
   (closed by `liebTraceArgument_isSelfAdjoint` and
   `liebTraceArgument_isStarNormal`), trace-exponential real-valuedness and
   positivity (closed by `cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint`,
   `liebTraceCfcExp_nonneg`, `liebTraceFunctional_trace_im_eq_zero`, and
   `liebTraceFunctional_nonneg`), `log (exp X)=X` for self-adjoint matrices
   (closed by `cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint`,
   `cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint`, and
   `cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint`), `exp (log A)=A` for
   strictly positive matrices (closed by
   `cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive`,
   `cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive`, and
   `cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive`),
   CFC-to-standard-exponential normalization of the local Lieb functional
   (closed by `liebTraceFunctional_eq_normedSpace_exp`), the \(H=0\)
   normalization of the local functional on the strictly positive cone
   (closed by `liebTraceFunctional_zero_eq_trace`), the affine \(H=0\)
   special case of the local Lieb concavity target (closed by
   `liebTraceConcavityTarget_zero`), positive support for finite probability
   laws (closed by `FiniteProbability.exists_prob_pos`), strict positivity of
   finite C-star expectations of pointwise strictly positive random matrices
   (closed by `FiniteProbability.expectationCStarMatrix_isStrictlyPositive`),
   strict positivity of self-adjoint finite complex C-star matrix exponentials
   (closed by
   `cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint`,
   `cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint`,
   `cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint`, and
   `liebTraceCfcExp_isStrictlyPositive`), the conditional one-step
   Tropp/Jensen trace-MGF inequality from an explicit Lieb hypothesis (closed
   by
   `FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`),
   scalar/vector relative-entropy nonnegativity (closed by
   `realRelativeEntropy_nonneg` and `finiteRealRelativeEntropy_nonneg`),
   the finite log-sum and commutative joint-convexity layer (closed by
   `finite_log_sum_inequality`, `realRelativeEntropy_jointConvex`, and
   `finiteRealRelativeEntropy_jointConvex`),
   relative-entropy vocabulary and diagonal normalization (closed by
   `cstarMatrixRelativeEntropy` and `cstarMatrixRelativeEntropy_self`),
   the scalar-identity matrix relative-entropy case (closed by
   `cstarMatrixRelativeEntropy_algebraMap_real_nonneg`),
   the real diagonal matrix relative-entropy case (closed by
   `cstarMatrix_log_realDiagonal`,
   `cstarMatrixRelativeEntropy_realDiagonal`, and
   `cstarMatrixRelativeEntropy_realDiagonal_nonneg`),
   the real diagonal matrix relative-entropy joint-convexity subcase (closed
   by `cstarMatrixRelativeEntropy_realDiagonal_jointConvex`),
   the left/right multiplication endomorphism substrate for the Effros
   perspective route (closed by `cstarMatrixLeftMul`,
   `cstarMatrixRightMul`, `cstarMatrixLeftRightMul_commute`,
   `cstarMatrixLeftMul_isUnit_of_isStrictlyPositive`, and
   `cstarMatrixRightMul_isUnit_of_isStrictlyPositive`),
   the product/power algebra for \(L_A\) and \(R_A\) (closed by
   `cstarMatrixLeftMul_mul`, `cstarMatrixRightMul_mul`,
   `cstarMatrixLeftMul_pow`, and `cstarMatrixRightMul_pow`),
   the explicit \(L_X R_A^{-1}\) ratio endomorphism and base-point
   normalization (closed by `cstarMatrixLeftRightRatio`,
   `cstarMatrixLeftRightRatio_apply`, `cstarMatrixLeftRightRatio_apply_unit`,
   `cstarMatrixLeftRightRatio_apply_of_unit_eq`, and
   `cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive`),
   the conditional route reduction from joint convexity plus the normalized
   variational formula to Lieb concavity (closed by
   `liebTraceConcavityTarget_of_relativeEntropy_route`), the optimizer-candidate
   equality part of that normalized formula (closed by
   `cstarMatrixEntropyVariationalObjective_liebOptimizer`), the reduction of
   variational maximality to relative-entropy nonnegativity (closed by
   `cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`), the
   reduction of relative-entropy nonnegativity to generalized Klein
   first-order trace convexity (closed by
   `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`),
   the converse/equivalence clarification (closed by
   `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg`
   and
   `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg`),
   the Hermitian spectral-overlap expansion and nonnegative-kernel step
   (closed by `matrixTrace_sum_hermitianCfc_mul_cfc_re` and
   `matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg`), the
   positive-spectrum scalar entropy specialization (closed by
   `realEntropy_firstOrderKernel_nonneg` and
   `matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg`), the compact
   Hermitian entropy trace inequality (closed by
   `matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`), the
   C-star-to-plain-matrix positivity bridge (closed by
   `cstarMatrix_nonneg_to_matrix_posSemidef` and
   `cstarMatrix_isStrictlyPositive_to_matrix_posDef`), the local generalized
   Klein theorem (closed by
   `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`),
   local matrix relative-entropy nonnegativity (closed by
   `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`), the
   normalized variational formula (closed by
   `cstarMatrixEntropyVariationalFormula_of_hermitianCfc`), and the reduction
   from joint convexity alone to the Lieb target (closed by
   `liebTraceConcavityTarget_of_relativeEntropy_jointConvex`), the final
   product-index perspective trace representation (closed by
   `cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`
   and `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`),
   finite-dimensional relative-entropy joint convexity (closed by
   `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`), arbitrary
   self-adjoint finite-dimensional Lieb concavity (closed by
   `liebTraceConcavityTarget_all`), and the unconditional one-step Tropp
   trace-MGF inequality (closed by
   `FiniteProbability.expectationReal_trace_normed_exp_add_le`).
   The ordinary finite perspective theorem for
   \(f(x)=x\log x-(x-1)\) is now closed by
   `cstarMatrixEntropyKernelPerspective_jointConvex`, using the local
   square-root algebra and perspective weights.  It is still not by itself a
   source-faithful representation of Umegaki relative entropy; the later
   product-index equality bridge supplies that representation.  The current
   proof-source target is the iterated independent-sum trace-MGF theorem and
   then matrix Bernstein.  The product-index vectorization action
   \(A\otimes B^{\mathsf T}:M\mapsto AMB\) and the vectorized-identity trace
   pairing \(v_I^*(A\otimes B^{\mathsf T})v_I=\operatorname{tr}(AB)\) are now
   formalized by `matrix_kronecker_transpose_mulVec_matrixVec` and
   `matrixComplexQuadraticForm_vecId_kronecker_transpose`.  The polynomial
   power layer is also closed by `matrix_kronecker_transpose_pow`,
   `matrix_kronecker_transpose_pow_mulVec_matrixVec`, `matrixVec_one`, and
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow`, giving
   \(v_I^*(A\otimes B^{\mathsf T})^k v_I=\operatorname{tr}(A^kB^k)\).  The
   finite-polynomial packaging is closed by `matrixComplexQuadraticForm_sum`,
   `matrixComplexQuadraticForm_smul`, and
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial`, and the
   standard polynomial-evaluation bridge is closed by
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval`.  The
   finite-dimensional continuity hook for passing matrix polynomial identities
   through limits is closed by `continuous_matrixComplexQuadraticForm`, and
   polynomial evaluation continuity is closed by
   `continuous_matrix_polynomial_aeval`.  The source-faithful
   right-multiplication polynomial perspective layer is also now closed:
   `matrixVecId_inner_matrixVec`,
   `matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint`,
   `matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint`,
   `matrix_kronecker_transpose_posSemidef`,
   `matrix_kronecker_transpose_posDef`,
   `matrix_kronecker_inv_transpose_posDef`, `matrixSelfAdjointCfc`,
   `matrixSelfAdjointCfc_polynomial`,
   `exists_realPolynomial_near_log_on_Icc`,
   `exists_realPolynomial_near_xlog_on_Icc`,
   `exists_realPolynomial_near_realEntropyKernel_on_Icc`,
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right`,
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right`,
   `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right`,
   `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial`,
   and
   `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right`
   prove the finite-polynomial identity for \(p(L_XR_A^{-1})R_A\) and record
   the Weierstrass approximation source for \(\log\), \(x\log x\), and
   \(x\log x-(x-1)\).  The analytic transfer from a supplied uniform
   polynomial approximation through CFC, right multiplication, and
   vectorized-identity trace pairing is now closed by
   `tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul` and
   `tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx`.
   The concrete approximating sequence on positive-definite spectra is now
   closed by `matrix_posDef_spectrum_real_pos`,
   `matrix_posDef_spectrum_real_subset_Icc`,
   `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc`,
   `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef`,
   and `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef`.
   The next source step is the full source-faithful Effros/Umegaki perspective
   trace formula that identifies this entropy-kernel superoperator trace term
   with the repository's \(D(X;A)\).  This target is now named directly as
   `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`.  The
   ordinary source-matrix perspective theorem is not used to close the Umegaki
   representation, because the source theorem is the superoperator perspective
   for \(L_XR_A^{-1}\).
   The compact relative-entropy trace side is now closed locally by
   `matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`, which expands
   \(\operatorname{Re}\operatorname{tr}(X\log X-X\log A-(X-A))\) into the
   scalar relative-entropy overlap sum.  The remaining source step is the
   matching overlap expansion for the superoperator CFC term itself, now named
   `matrixSuperoperatorEntropyKernelOverlapExpansion`.  The adapter
   `matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap` proves
   that this theorem would identify the finite superoperator trace with the
   compact relative-entropy trace.  The finite-polynomial part of that
   overlap route is now closed by `matrixTrace_pow_mul_inv_pow_re_eq_sum` and
   `matrixPolynomialTraceRatio_re_eq_sum`, which identify
   \(\operatorname{tr}(X^kA(A^{-1})^k)\) and real-polynomial sums with the
   same eigenbasis-overlap weights.  The limiting entropy-kernel CFC overlap
   expansion is now closed in row 6.
4. Closed: prove the one-step trace-MGF theorem using the already formalized
   finite Jensen adapter (`FiniteProbability.expectationReal_trace_normed_exp_add_le`).
5. Active: iterate the one-step theorem over independent self-adjoint increments and
   instantiate the Algorithm 1 truncated dilation Bernstein route.

6. The source-faithful Umegaki trace-representation proof route is now closed
   locally.  The relevant Lean names are
   `matrixSuperoperatorEntropyKernelOverlapExpansion_all` and
   `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`, with
   `realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv` supplying the scalar
   \(D(a\|b)=b f(a/b)\) identity and
   `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef`
   supplying the common polynomial-limit route.
7. Closed: the finite-dimensional Lindblad/Effros joint-convexity step for
   matrix relative entropy is formalized as
   `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`.
8. Front-loaded source check for the now-closed relative-entropy bottleneck:
   Tropp's matrix
   concentration monograph points to the matrix perspective transformation
   (Theorem 8.6.2) and the relative-entropy convexity proof in Section 8.8;
   Effros's "A matrix convexity approach to some celebrated quantum
   inequalities" (PNAS 2009, Theorem 2.1; arXiv:0802.1234) gives the commuting
   positive-operator perspective route; and the PNAS note "Perspectives of
   matrix convex functions" records the perspective/joint-convexity theorem
   and its noncommutative extension as Theorems 2.1 and 2.2.  These references
   are advisory proof-source entries only.  The local Lean route uses the
   product-index lift substrate and closes the finite superoperator perspective
   bridge before deriving
   `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`.
9. The product-index ordinary perspective part of the Effros route is now
   formalized locally as `cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`.
   The remaining source-derived equality target is no longer the convexity of
   \(v_I^*P_f(L_X,R_A)v_I\); it is the identification of that ordinary
   perspective trace with the already formalized source-faithful relative
   modular expression.  This is closed by
   `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`; the adapter
   `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation`
   records why this equality bridge is sufficient for the
   finite-dimensional relative-entropy joint-convexity theorem.
10. The first local dependency for the equality bridge is closed:
    `cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder` proves the
    normalized-argument commutation step used by the Effros perspective source
    route.  The later right-lift square-root and outer CFC transport layers are
    now also closed.
11. The product-index right-lift inverse-square-root identity is now closed via
    the generic local theorem `cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv`
    and the specialization
    `cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv`.
    The subsequent outer perspective trace commutation/CFC transport is also
    closed:
    \(R_A^{1/2} f(L_XR_A^{-1})R_A^{1/2}\) is converted to
    \(f(L_XR_A^{-1})R_A\) in the vectorized-identity quadratic form and then
    matched with `matrixSuperoperatorEntropyKernelTrace`.
12. The ratio/square-root commutation part of that outer bridge is now closed:
    `cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift`
    proves \(L_XR_A^{-1}\) commutes with \(R_A^{1/2}\).  The CFC transport,
    product-index quadratic-form equality, relative-entropy joint convexity,
    Lieb trace concavity, and one-step trace-MGF layers are now closed.  At
    that checkpoint the active source obligation moved to Tropp's iterated
    independent-sum trace-MGF theorem; rows 13--15 below record its
    product-law specialization, iteration, and finite-real adapter closures.
13. Closed local product-law adapter for the active Tropp iteration route:
    `ElementwiseTraceMGF.lean` defines `sqMagSampleProbability` and proves
    `sqMagTraceProbability_expectationComplex_step_eq`,
    `sqMagTraceProbability_expectationCStarMatrix_step_eq`,
    `sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation`,
    and `sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le`.
    These results specialize the no-hidden-Lieb one-step trace-MGF inequality
    to a fixed coordinate of Algorithm 1's canonical squared-magnitude product
    trace law.  They do not yet perform Tropp's independent-sum iteration.
14. Closed local independent-sum iteration for the active Tropp route:
    `sqMagTraceProbMass_snoc` and
    `sqMagTraceProbability_expectationReal_succ_last_eq` formalize the product
    law conditioning step, and
    `sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le`
    formalizes the iid trace-MGF domination theorem for Algorithm 1's
    squared-magnitude product trace law.  This source obligation is now local;
    the next source obligation is the matrix Bernstein/Khintchine tail
    conversion from this trace-MGF theorem to the CACM equation (2)
    high-probability spectral event.
15. Closed local finite-real trace-exponential adapter for the active Tropp
    route: `finiteComplexCStarMatrix_zero`,
    `finiteComplexCStarMatrix_add`, and `finiteComplexCStarMatrix_finset_sum`
    prove that the finite real-to-complex C-star embedding preserves the
    algebra used by the trace-MGF statement; `finiteComplexCStarMatrixRingHom`,
    `finiteComplexCStarMatrixRingHom_continuous`,
    `finiteComplexCStarMatrix_finiteMatrixExp`, and
    `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re` prove that
    finite real matrix exponentials and finite real traces agree with the
    embedded C-star trace-exponential.  The algorithm-facing adapter
    `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`
    now transfers the iid C-star trace-MGF domination theorem back to the
    finite-real trace expression.  The remaining source obligation is not the
    trace-MGF iteration; it is the scalar matrix-CGF/log-MGF bound and the final
    Bernstein/Khintchine largest-eigenvalue tail conversion.
16. Closed local Algorithm 1 dilation instantiation for the active Tropp route:
    `sqMagTraceProbabilityFiniteRealTraceMGFLogBound` names the finite-real
    logarithmic trace-MGF upper-bound expression,
    `rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric`
    proves that the one-sample dilation increments \(\theta D(Z)\) satisfy the
    finite-real symmetry side condition, and
    `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`
    rewrites the trace-MGF statement as a bound on
    \(\mathbb E\,\operatorname{tr}\exp(\theta D(A-\widetilde A))\).
    The remaining source obligation is precisely the scalar matrix-CGF/log-MGF
    estimate for \(\log \mathbb E \exp(\theta D(Z))\), followed by the
    Bernstein/Khintchine eigenvalue tail constants.
17. Closed local trace-exponential Markov/eigenvalue specialization for the
    active Tropp route: the generic finite-matrix concentration interfaces in
    `MatrixConcentration.lean` are now applied to the actual scaled Algorithm
    1 dilation residual.  The theorem
    `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
    gives the one-sided largest-eigenvalue Markov bound from the proved
    residual trace-MGF expression, and
    `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`
    gives the two-sided absolute-eigenvalue event using the trace-MGF
    expressions at \(\theta\) and \(-\theta\).  The remaining source
    obligation is now only the scalar matrix-CGF/log-MGF estimate and the
    explicit Bernstein/Khintchine constants for CACM equation (2).
18. Closed local CFC scalar-to-operator Bernstein-parabola lift for the active
    Tropp/Bernstein route: `cstarMatrix_cfc_quadratic_eq` rewrites the CFC
    quadratic as \(I+\theta X+\beta X^2\), and
    `cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum` lifts any scalar
    spectrum inequality \(e^{\theta x}\le 1+\theta x+\beta x^2\) to Loewner
    order.
19. Closed the scalar Bernstein parabola constants and the explicit scaled CFC
    lift: `real_exp_mul_le_quadratic_of_nonneg_of_le_one` proves
    \(e^{a x}\le 1+a x+(e^a-a-1)x^2\) for \(a\ge0\), \(x\le1\),
    `real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le` proves the
    \(R>0\) scaled version, and
    `cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le`
    applies it under a real-spectrum upper bound.
20. Closed the generic one-sample matrix-CGF/log-MGF variance proxy:
    `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`
    proves \(\log\mathbb E\exp(\theta X)\preceq
    g(\theta,R)\mathbb E[X^2]\) for centered self-adjoint finite C-star
    samples with real spectrum bounded above by \(R>0\).  The remaining source
    obligation is the Algorithm 1 dilation-increment instantiation and the
    final Bernstein/Khintchine constants.
21. Closed the Algorithm 1 parameterized Bernstein tail skeleton: the
    truncated dilation second-moment proxy, the negative support bound, the
    positive and negative scalar trace-MGF bounds, and the upper/two-sided
    trace-exponential Markov tails are formalized locally in
    `ElementwiseSpectral.lean`.  The main theorem names are
    `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
    `sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
    `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
    `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`,
    `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
    and
    `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`.
    The remaining source obligation is no longer a missing lower-tail
    concentration theorem; it is the optimization of \(\theta\), conversion to
    the final CACM equation (2) constants, and downstream floating-point
    transfer.
22. Closed the explicit failure-probability specialization of the parameterized
    tail skeleton: `real_exp_neg_log_two_mul_div_mul_self_add` formalizes the
    standard choice \(T=\log(2B/\delta)\) for a two-sided trace-exponential
    bound, and
    `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`
    applies it to the truncated Algorithm 1 self-adjoint dilation.  This is a
    local proof, not a citation-only closure.
23. Closed the deterministic spectral conversion from the scaled dilation event:
    `finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le` is proved from
    the local mathlib-backed Hermitian spectral theorem, and
    `finiteLoewnerLe_of_smul_left_le_smul_id` is a local scalar-cancellation
    lemma for Loewner upper bounds.  These feed
    `algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent` and
    the high-probability corollary
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`.
    The remaining source obligation is the Drineas--Zouzias/CACM
    theta-optimization and final constant simplification, followed by
    floating-point transfer.
24. Closed the scalar theta-optimization subdependency for the truncated exact
    route: `real_bernstein_exact_radius_le_of_log_le` formalizes the exact
    Bennett optimizer \(\theta=\log(1+Lr/W)/L\), and
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius`
    applies it to the already proved Algorithm 1 spectral event.  The
    remaining source obligation is no longer an unoptimized free-\(\theta\)
    theorem; it is the source sample-complexity/final-constant simplification,
    truncation transfer at those constants, and downstream floating-point
    transfer.
25. Closed the source-sharp square variance subdependency for the
    Drineas--Zouzias route.  The local Lean route now proves the one-step
    vector and transpose-vector second moments directly, packages them into
    the self-adjoint dilation Loewner/C-star variance proxy at
    \(V=n\|\widehat A\|_F^2/s^2\), and threads that proxy through the sharp
    positive/negative truncated trace-MGF and explicit \(1-\delta\) two-sided
    eigenvalue skeleton.  The main theorem names are
    `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`,
    `sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`,
    `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square`,
    `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
    `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`, and
    `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square`.
    The remaining source obligation is now the source sample-complexity and
    final-constant simplification, followed by truncation and floating-point
    transfer.
26. Closed the source-sharp square spectral conversion and Bennett optimizer
    subdependency.  The local Lean route now proves
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square`
    and
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square`.
    These are still local formalizations of the proof-source route, not
    citation closures: they compose the already formalized two-sided
    trace-MGF tail, eigenvalue-to-Loewner bridge, rectangular dilation bridge,
    and scalar Bennett optimizer.  The remaining source obligation is the
    algebraic simplification from the explicit Bennett budget to the
    Drineas--Zouzias/CACM sample-complexity constants, plus truncation and
    floating-point transfer at those constants.
27. Closed a conservative fallback denominator simplification from the explicit
    Bennett budget.  The local Lean theorem
    `real_bennett_transform_lower_bound_two_add` proves
    \(x^2/(2+x)\le(1+x)\log(1+x)-x\) from mathlib's logarithm lower-bound
    infrastructure, and
    `real_bennett_budget_of_quadratic_denominator_two_add` rewrites this as
    \(q\le r^2/(2W+Lr)\Rightarrow q\) satisfies the Bennett budget.  The
    Algorithm 1 corollary
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square`
    composes that scalar bridge with the source-sharp square Bennett theorem.
    This proof source item is explicitly weaker than the
    Drineas--Zouzias/CACM final-constant route, which needs the sharper
    \(2W+\frac23Lr\) denominator and remains open.
28. Closed the source denominator and source sample-budget route for Algorithm
    1.  The local Lean theorem
    `real_bennett_transform_lower_bound_two_add_two_thirds` proves the
    source-sharp scalar inequality
    \(x^2/(2+\frac23x)\le(1+x)\log(1+x)-x\) using the first two positive terms
    of the logarithm series lower bound.  The theorem
    `real_bennett_budget_of_quadratic_denominator_two_add_two_thirds` turns
    this into the \(2W+\frac23Lr\) Bennett-budget denominator.  The local
    theorem `elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos`
    supplies the truncation fact needed to bound the linear
    \(\varepsilon\|\widehat A\|_F\) term.  These feed
    `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square`,
    which proves the truncated exact event from the source budget
    \(14n\|A\|_F^2\log(2(2n)/\delta)\le s\varepsilon^2\).  The deterministic
    truncation transfer is composed in
    `sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`.
    The FP transfer theorem is also present under an explicit entrywise
    perturbation budget.
29. Closed the remaining FP proof-source item for the square source-aligned
    Algorithm 1 theorem.  No external source was needed: the route reuses the
    local Higham-style gamma library and the canonical sampler support theorem.
    The new support theorem
    `fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb`
    proves the entrywise budget on traces that only sample positive-probability
    entries; zero-probability traces are avoided by
    `sqMagTraceProbability_eventProb_elementwiseTracePositiveProb`.  The final
    theorem
    `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square`
    derives the rounded source-budget event under `gammaValid fp s` and
    `gammaValid fp (s+1)`, without assuming a hidden perturbation event.
30. Closed the concrete normal-equations/Cholesky solver proof-source route for
    the literal rounded sampled-row equation (8) theorem.  This route needed no
    new external theorem: it reuses the repository's local
    `ls_normal_equations_backward` and `ls_normal_equations_forward_error`.
    The new theorem
    `normal_equations_cholesky_forward_error_certificate` packages the local
    Gram-product, Gram-vector, Cholesky, and triangular-solve error models into
    the componentwise certificate required by the rounded sampled-row RandNLA
    objective theorem, and
    `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver`
    composes it with the existing high-probability row-sampling theorem.
31. External proof-source acquisition for the still-open rectangular
    QR/preconditioner equation (8) solver route found the relevant source
    family but no local Lean foundation that can close it immediately.  The
    local file `LSQRSolve.lean` explicitly stores `LSQRSolveBackwardError` as a
    specification because rectangular QR is not represented by the current
    square-matrix framework.  The proof-source route should be based on
    Higham, *Accuracy and Stability of Numerical Algorithms*, chapter 19
    (QR factorization, DOI `10.1137/1.9780898718027.ch19`) and chapter 20
    (least squares, DOI `10.1137/1.9780898718027.ch20`), together with
    Cox--Higham, "Stability of Householder QR Factorization for Weighted Least
    Squares Problems" (1997/1998), Theorem 1.1 and Section 2.  The SIAM chapter
    20 source states the rectangular LS setting and Wedin perturbation route;
    chapter 19 gives the QR/Householder stability background; Cox--Higham gives
    a modern rectangular Householder QR backward-error theorem, including
    normwise and rowwise variants.  These citations identify the mathematical
    route only: the needed rectangular QR objects, Householder update model,
    and concrete backward-error theorem must still be formalized locally before
    the paper-level QR/preconditioner theorem can be closed.
32. Closed the deterministic adapter from the external rectangular QR proof
    route to the local repository specification.  The new local theorem
    `rectLSNormalEquations_perturbed_to_gram_system` proves that exact
    rectangular normal equations for perturbed data induce a perturbed Gram
    system for the unperturbed data, and
    `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations` packages
    this as `LSQRSolveBackwardError` when the induced Gram/RHS perturbations
    have the stated radii.  The source acquisition item is therefore narrowed:
    the remaining source-backed Lean target is the concrete rectangular
    Householder QR/preconditioner theorem that produces the perturbed data and
    radii, not the RandNLA solver transfer.
33. Closed small route-A algebra foundations for the still-open rectangular
    QR/preconditioner route.  The local matrix algebra file now defines
    `matMulRectLeft` and `matMulRectRight` and proves
    `frobNormSqRect_orthogonal_left`, `frobNormRect_orthogonal_left`,
    `frobNormSqRect_orthogonal_right`, and
    `frobNormRect_orthogonal_right`: left multiplication of an `m × n`
    rectangular matrix by an orthogonal `m × m` matrix, and right multiplication
    by an orthogonal `n × n` matrix, preserve the rectangular Frobenius norm.
    These are reusable norm identities needed by a Higham/Cox--Higham-style
    rectangular Householder QR proof.  They do not close the source theorem
    itself; the remaining source-backed Lean target is still the concrete
    rectangular QR/preconditioner theorem producing perturbed data and
    rectangular perturbation bounds.
34. Closed the companion rectangular norm-growth foundation for the same
    route.  The local matrix algebra file now proves
    `frobNormRect_eq_frobNormFn`, `frobNormRect_matMulRectLeft_le`, and
    `frobNormRect_matMulRectRight_le`, reusing Mathlib's Frobenius
    submultiplicativity through the repository's compatibility wrapper.  This
    is the exact norm inequality used in a rectangular one-step perturbation
    accumulation proof; it still does not close the rectangular QR source
    theorem by itself.
35. Closed the rectangular left-action algebra foundation needed by the same
    one-step route.  The local matrix algebra file now proves
    `matMulRectLeft_id`, `matMulRectLeft_assoc`,
    `matMulRectLeft_add_left`, and `matMulRectLeft_add_right`, so the
    rectangular one-step perturbation proof can reuse exact identity,
    associativity, and additivity rather than expanding all sums inline.
36. Closed the rectangular one-step accumulation theorem for the same
    source route.  `rect_orthogonal_sequence_one_step` in
    `Algorithms/QR/HouseholderQR.lean` proves that if a current `m × n`
    matrix has representation `Qᵀ(A+ΔA)` and the next computed transformation
    is `(P+ΔP)`, then it has a new representation `Q'ᵀ(A+ΔA')` with
    rectangular Frobenius growth bounded by
    `‖ΔA‖_F + c_step ‖A+ΔA‖_F` when `‖ΔP‖_F ≤ c_step`.  This is the
    rectangular analogue of the repository's square one-step theorem; the
    remaining source target is the multi-step rectangular Householder
    factorization/preconditioner theorem and its least-squares solve handoff.
37. Closed the rectangular multi-step accumulation theorem for supplied
    perturbed transformations.  `rect_orthogonal_sequence_geometric` iterates
    the one-step theorem for `r` steps and proves a rigorous geometric bound
    `((1+c)^r-1)||A||_F`.  This deliberately avoids presenting the informal
    first-order `r c ||A||_F` bound as exact.  The remaining source-backed
    target is now a concrete rectangular Householder/preconditioner
    implementation theorem that instantiates the supplied transformations and
    feeds the rectangular normal-equations bridge.
38. Closed the deterministic least-squares handoff after an orthogonal row
    transformation.  `rectLSGram_matMulRectLeft_orthogonal`,
    `rectLSRhs_matMulRectLeft_orthogonal`, and
    `RectLSNormalEquations.of_orthogonal_left` prove that if `A_hat = U A` and
    `b_hat = U b` with `U` orthogonal, then exact normal equations for the
    transformed problem imply exact normal equations for the original problem.
    This is the handoff needed after a rectangular QR theorem supplies
    transformed data; it still does not instantiate a concrete floating-point
    Householder implementation.
39. Closed the right-hand-side perturbation accumulation companion for the
    same rectangular QR source route.  `orthogonal_vector_sequence_one_step`
    and `orthogonal_vector_sequence_geometric` prove that a supplied sequence
    of perturbed square orthogonal transformations applied to `b` preserves a
    source-style `Qᵀ(b+Δb)` representation and satisfies the rigorous
    Euclidean radius `((1+c)^r-1)||b||₂`.  This is the vector/RHS analogue of
    `rect_orthogonal_sequence_geometric`; the remaining source-backed target
    is still a concrete rectangular Householder/preconditioner implementation
    theorem that instantiates the supplied transformations, computes the
    transformed RHS, proves triangular/solver exactness, and feeds the
    rectangular normal-equation handoff.
40. Closed the exact top-block solve handoff for the same source route.
    `RectLSNormalEquations.of_rowwise_normal` proves that a rowwise
    normal-equation identity implies rectangular normal equations, and
    `RectLSNormalEquations.of_top_solve_zero_bottom` proves the QR-shaped
    specialization: if transformed data has top block `R`, zero lower matrix
    block, and the computed vector solves `R x = c`, then it satisfies the
    normal equations for the full transformed rectangular problem.  The lower
    transformed right-hand side is unrestricted, matching the usual
    least-squares QR residual block.  This closes an exact solver handoff
    dependency; the source-backed open target remains the concrete
    floating-point rectangular Householder/preconditioner implementation and
    rounded triangular solve theorem.
41. Closed the rounded top-block solve handoff by reusing the local triangular
    solve theorem.  `RectLSNormalEquations.exists_topBlock_of_fl_backSub`
    applies `backSub_backward_error` to obtain a perturbation `ΔR` satisfying
    `|ΔR_ij| ≤ gamma fp n * |R_ij|` and an exact solve
    `(R+ΔR) fl_backSub(R,c) = c`; the theorem then embeds `R+ΔR` as a
    zero-lower rectangular top block and proves the rectangular normal
    equations for that perturbed transformed problem.  This removes the
    triangular-solve part of the QR source route from the open foundation list.
    The remaining source-backed target is the concrete rectangular
    Householder/preconditioner implementation that produces the transformed
    `[R;0]` shape, transformed RHS/top `c`, and data-perturbation bounds.
42. Closed the common-orthogonal-factor accumulation substrate for the same
    source route.  The separate matrix and vector accumulation theorems were
    not strong enough for the final QR handoff because they exposed unrelated
    existential orthogonal factors.  The new
    `rect_orthogonal_matrix_vector_sequence_one_step` and
    `rect_orthogonal_matrix_vector_sequence_geometric` theorems prove a shared
    `Q` representation for a supplied sequence applied simultaneously to
    `A` and `b`, with geometric perturbation radii for both data blocks.  This
    is still source-route infrastructure: it does not by itself instantiate
    concrete Householder reflectors, the `[R;0]` top-block shape, or the
    pullback of the triangular-solve perturbation to the original data.
43. Closed the pullback of the rounded top-block triangular-solve perturbation
    through the shared QR orthogonal factor.  The new
    `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub`
    theorem combines the common-`Q` representation, top-block shape, local
    `fl_backSub` theorem, and orthogonal normal-equation handoff.  It proves
    that the computed vector satisfies rectangular normal equations for the
    original perturbed data with
    `Delta A_total = Delta A + Q [Delta R;0]` and norm budget
    `||Delta A_total||_F <= ||Delta A||_F + ||[Delta R;0]||_F`.  The remaining
    source-backed target is now the concrete rectangular
    Householder/preconditioner implementation that supplies the transformed
    `[R;0]` shape and transformed top right-hand side from actual computed
    reflectors; a smaller optional dependency is to reduce `||[Delta R;0]||_F`
    to a closed gamma/R norm bound.
44. Closed the embedded top-block norm-budget dependency for the rounded
    top-block pullback.  The shared exact norm adapters
    `frobNormSqRect_abs` and `frobNormRect_abs` prove that componentwise
    absolute value does not change rectangular Frobenius norm.  Using those
    with `frobNormRect_le_of_entry_abs_le`, the theorem
    `rectTopBlock_frobNorm_perturb_bound_of_gamma` proves
    `||[Delta R;0]||_F <= gamma fp n ||[R;0]||_F` from the local
    `backSub_backward_error` entrywise budget.  The strengthened theorem
    `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound`
    now exposes the pulled-back perturbation budget directly as
    `||Delta A_total||_F <= ||Delta A||_F + gamma fp n ||[R;0]||_F`.
    The source-backed target is narrowed to the concrete rectangular
    Householder/preconditioner implementation theorem.
45. Closed the supplied-transform route into the local QR least-squares solver
    specification.  The theorem
    `LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget`
    composes common-`Q` transformed data, top-block shape, rounded
    back-substitution, the gamma top-block norm budget, and explicit induced
    Gram/RHS norm budgets into `LSQRSolveBackwardError`.  The theorem
    `LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
    additionally composes the simultaneous supplied orthogonal-sequence
    accumulation theorem, giving data radii
    `((1+c)^r-1)||A||_F` and `((1+c)^r-1)||b||₂` before the same top-block
    solve handoff.  This closes the supplied-transform specification route;
    it does not yet formalize the concrete floating-point Householder QR
    implementation that proves the supplied recurrences, final `[R;0]` shape,
    and transformed-RHS construction.
46. Closed the first exact embedded-reflector substrate for the concrete
    rectangular Householder route.  Higham's QR/least-squares chapters and the
    Cox--Higham Householder QR stability paper both rely on Householder
    transformations acting on trailing subproblems.  The local theorem family
    `householder_row_eq_id_of_zero_prefix`,
    `householder_col_eq_id_of_zero_prefix`,
    `matMulVec_householder_eq_self_of_zero_prefix`,
    `matMul_householder_eq_self_row_of_zero_prefix`, and
    `matMulRectLeft_householder_eq_self_row_of_zero_prefix` proves the exact
    embedded-reflector algebra: if the Householder vector vanishes on a prefix,
    then the full reflector is identity on that prefix and preserves those
    vector entries and matrix rows.  External proof-source acquisition for the
    remaining route-A theorem identified Higham, Accuracy and Stability of
    Numerical Algorithms, Chapters 19--20, and Cox--Higham, Stability of
    Householder QR Factorization, as advisory route sources; the needed result
    was formalized locally rather than closed by citation.  Remaining proof
    foundations are the exact active-column zeroing theorem for the constructed
    Householder vector and a common floating-point panel/update theorem for
    applying the same rounded reflector to both `A` and `b`.
47. Closed the exact active-column zeroing substrate for the concrete
    rectangular Householder route.  The standard Householder construction
    chooses `v = x - alpha e_p` and `beta = 2/(v^T v)` with
    `alpha^2 = ||x||_2^2`; this is the algebraic step used in the Higham and
    Cox--Higham route sources before floating-point update errors are
    considered.  The local theorem family `householderActiveVector`,
    `householderBeta`, `householderActiveVector_inner_x`,
    `householderActiveVector_inner_self`,
    `householderActiveVector_inner_self_eq_two_inner_x`,
    `householderBeta_mul_activeVector_inner_x`,
    `matMulVec_householder_activeVector_eq_alpha_basis`, and
    `matMulVec_householder_activeVector_eq_zero_of_ne` proves the step
    directly: under explicit nondegeneracy `v^T v != 0`, the exact reflector
    maps `x` to `alpha e_p` and zeros the off-pivot active entries.  No
    theorem was closed by citation; the remaining source-guided dependency is
    the floating-point common panel/update recurrence for applying the same
    rounded reflector to the matrix block and right-hand side.
48. Closed the common panel/update contract adapter for the concrete
    rectangular Householder route.  The proof-source audit showed that the
    local vector-only `HouseholderAppError` is not the right final interface:
    as with the repository's matrix-matrix backward-error note, independently
    applying vector-level error theorems can choose different perturbation
    matrices for different columns/vectors.  The local statement is therefore
    corrected by adding `HouseholderPanelAppError`, which explicitly requires a
    single shared `Delta P` for the rectangular matrix-panel update and the
    right-hand-side update.  The theorem
    `householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric`
    proves that any sequence of such common panel contracts feeds the existing
    common-`Q` accumulation theorem with geometric matrix and vector radii.
    This is a locally formalized interface theorem, not a citation closure:
    the remaining source-guided dependency is a low-level proof that the
    concrete rounded Householder panel implementation satisfies
    `HouseholderPanelAppError`.
49. Corrected the active rectangular Householder QR route to the columnwise
    source theorem.  Higham's QR notes, Section 4.1, Lemmas 4.3--4.4 and
    Theorem 4.5 (also corresponding to the Householder QR material in
    *Accuracy and Stability of Numerical Algorithms*), state the standard
    backward-error result columnwise: applying a sequence of Householder
    transformations to the columns yields
    `A_hat = Q^T (A + Delta A)` with per-column bounds, and the per-step
    perturbation matrices may depend on the column.  This means the previously
    added shared-`Delta P` contract is a stronger optional interface, not the
    source-faithful active route.  The local formalization now closes the
    columnwise accumulation dependency with
    `HouseholderColumnwisePanelAppError`,
    `HouseholderColumnwisePanelAppError.of_vector_applications`,
    `HouseholderColumnwisePanelAppError.of_forward_errors`,
    `orthogonal_vector_sequence_one_step_fixedQ`,
    `rect_orthogonal_columnwise_vector_sequence_geometric`, and
    `householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric`.
    The exact adapter `HouseholderAppError.of_forward_error` now shows that a
    normwise vector forward-error theorem is enough to discharge the
    vector-level backward-error contract, and the columnwise forward-error
    constructor applies this per panel column.  The explicit-matrix route is
    closed locally: `fl_householderApplyExplicit` reuses the repository's
    `fl_matVec` theorem to prove a rounded application bound for an already
    formed reflector matrix and instantiate the same contracts.  The compact
    dot/scale/subtract route is also now closed locally by
    `fl_householderApplyCompact_componentwise_error_bound`,
    `fl_householderApplyCompact_forward_error_bound`, and the visible-budget
    adapter `fl_householderApplyCompact_HouseholderAppError_of_budget`.  The
    compact supplied-sequence adapter
    `fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
    now composes those compact panel/RHS steps with the columnwise geometric
    accumulation theorem.  The handoff to the local solver-facing interface is
    also closed locally:
    `frobNormRect_le_of_col_vecNorm2_le` converts the columnwise data
    perturbation radii to a Frobenius radius, and
    `LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
    composes the compact sequence theorem with the existing top-block
    `fl_backSub` pullback.  No theorem was closed by citation; the remaining
    source-guided dependency is the final rectangular QR/preconditioner
    assembly that proves the concrete recurrence, transformed `[R;0]` shape,
    top-RHS linkage, and triangular/nonzero-diagonal facts.  External
    source used:
    https://nhigham.com/wp-content/uploads/2023/10/high99n.pdf, pp. 19--21,
    Lemmas 4.3--4.4 and Theorem 4.5.
50. Closed the exact trailing Householder shape route for rectangular QR.  The
    source-faithful QR construction uses a Householder vector with a zero
    prefix and active entries only in the trailing pivot segment, not the
    earlier full-vector `x - alpha e_p` construction by itself.  The new local
    definitions `householderPrefixPart`, `householderTrailingPart`,
    `householderTrailingNorm2Sq`, and `householderTrailingActiveVector` encode
    this.  The theorem
    `matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero` proves
    the exact one-step shape: entries above the pivot are preserved, the pivot
    becomes `alpha`, and entries below the pivot become zero.  The theorem
    `exact_trailing_householder_sequence_lower_zero` proves the lower-zero
    loop invariant for a supplied exact trailing recurrence, and
    `rectangular_topBlock_shape_facts_of_lower_zero` converts it to the
    solver-facing `[R;0]`/`cTop`/upper-triangular facts.  This follows the
    Higham Householder QR construction in the same source chain as row 49, but
    it is proved locally.  The remaining source-guided dependency is the
    rounded stored-`R`/RHS implementation assembly and a formal nonzero
    diagonal/rank or nonbreakdown condition.
51. Closed the storage-shape part of the rounded rectangular QR route.  The
    source algorithms store completed Householder QR columns in triangular
    form rather than relying on the rounded compact update to produce exact
    zeros.  The local definitions `fl_householderStoredPanelStep` and
    `fl_householderStoredRhsStep` encode this storage convention: completed
    columns/rows are preserved, active/trailing entries are computed by the
    compact rounded Householder primitive, and entries below the active pivot
    in the completed pivot column are set to zero.  The local theorems
    `fl_householderStoredPanel_sequence_lower_zero` and
    `fl_householderStoredPanel_sequence_topBlock_shape_facts` prove the final
    `[R;0]`/`cTop`/upper-triangular shape.  This is proved locally and is
    source-consistent with Householder QR storage, but it is not a perturbation
    theorem.  The next source-guided dependency is to prove that the stored
    compact step satisfies the columnwise perturbation contract under visible
    budget assumptions, and then handle nonzero pivots from rank/nonbreakdown.
52. Closed the stored-step perturbation-contract dependency for the rounded
    rectangular QR route.  The local theorem
    `fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`
    combines the compact dot-scale-subtract forward-error budget with the QR
    storage convention: completed columns contribute zero error when the exact
    reflector preserves them, entries stored as pivot-column zeros contribute
    zero error when the exact reflector zeros them, RHS prefix entries
    contribute zero error when the reflector preserves that prefix, and all
    active/trailing entries reuse the compact budget.  The visible
    budget-domination hypotheses then feed the existing
    `HouseholderColumnwisePanelAppError.of_forward_errors` constructor.  This
    is proved locally and matches the Higham columnwise Householder QR proof
    route from row 49.  The remaining source-guided dependency is the concrete
    loop theorem that proves those preservation and zeroing hypotheses from the
    trailing Householder construction at every step, plus the nonzero
    diagonal/rank or nonbreakdown condition.
53. Closed the one-step concrete trailing-reflector discharge dependency.  The
    local theorem
    `fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget`
    proves that a QR trailing Householder vector supplies the exact hypotheses
    required by row 52 for one stored step: completed columns are preserved
    from the pre-step lower-zero invariant, the RHS prefix is preserved by the
    reflector's zero prefix, and the active pivot column is zeroed below the
    diagonal by the trailing active-vector theorem.  This is proved locally
    using the same Higham Householder QR route; no theorem is closed by
    citation.  The remaining dependency is the multi-step stored trailing loop
    theorem that feeds this one-step result through the stored lower-zero
    invariant and then handles nonzero pivots.
54. Closed the multi-step stored trailing Householder sequence dependency.  The
    local theorem
    `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
    builds the QR trailing reflector from each current stored pivot column,
    maintains the stored lower-zero invariant, invokes the one-step theorem
    from row 53 at every pivot, and then applies the source-faithful columnwise
    common-`Q` accumulation theorem.  The result provides one orthogonal factor
    and explicit geometric column/RHS perturbation radii for the final stored
    outputs.  This is proved locally; the Higham/Cox--Higham source chain is
    advisory for the route and no theorem is closed by citation.  The remaining
    dependency is the solver-spec handoff that composes this perturbation
    theorem with the stored top-block shape facts, rounded triangular solve,
    and visible nonzero diagonal/rank or nonbreakdown condition.
55. Closed the stored trailing Householder loop solver-spec handoff dependency.
    The local theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
    reads `R` and `cTop` from the final stored outputs, reuses
    `fl_householderStoredPanel_sequence_topBlock_shape_facts` for the final
    `[R;0]`/top-RHS/upper-triangular facts, reuses row 54 for the common
    orthogonal factor and column/RHS perturbation radii, converts the column
    bounds to a Frobenius data radius with
    `frobNormRect_le_of_col_vecNorm2_le`, and invokes the existing
    `LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget`.
    This is proved locally and closes the stored-loop handoff into the local
    QR solver specification.  The remaining QR dependency is a nonzero
    diagonal/rank or nonbreakdown theorem for the computed top block; until
    that is formalized, the new theorem exposes it as an explicit hypothesis.
56. Closed a local per-pivot floating-point nonbreakdown bridge.  The local
    theorems
    `fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha`,
    `fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero`,
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha`,
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha`
    prove that the stored trailing QR solver certificate no longer needs an
    opaque final diagonal hypothesis when each pivot satisfies the concrete
    inequality `budget_k < |alpha_k|`.  This is proved locally from the exact
    trailing Householder pivot algebra and the stored-step componentwise error
    bound; no theorem is closed by citation.  The remaining proof-source item is
    a rank/conditioning/nonbreakdown route that implies these per-pivot budget
    inequalities for the computed loop.
57. Closed a local pivot-value denominator nonbreakdown bridge.  The theorem
    `householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha`
    proves that the trailing Householder denominator \(v^Tv\) is nonzero
    whenever the active pivot entry differs from the chosen sign parameter
    \(\alpha_k\).  The stored QR theorem
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha`
    and the solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha`
    use this generated denominator proof together with the existing pivot
    budget inequality.  This is a statement correction for the active QR
    bottleneck: the denominator is no longer an unexplained sum-of-squares
    hypothesis, but the scalar nonbreakdown condition
    \(A_k(k,k)\ne\alpha_k\) and the budget inequality
    \(B_k<|\alpha_k|\) still need a rank/conditioning route.
58. Closed a local sign-choice denominator nonbreakdown bridge.  The theorem
    `householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos`
    proves that the scalar nonbreakdown condition
    \(A_k(k,k)\ne\alpha_k\) follows from the standard Householder sign-choice
    hypotheses \(\alpha_k^2=\|A_k(k{:}m,k)\|_2^2\),
    \(\|A_k(k{:}m,k)\|_2^2>0\), and
    \(\alpha_k A_k(k,k)\le0\).  The theorem
    `householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`
    converts this to \(v^Tv\ne0\).  The stored QR theorem
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos`
    and the solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`
    use the generated denominator proof together with the existing pivot
    budget inequality.  This is a local algebraic dependency closure, not a
    rank theorem.  The remaining proof-source item is now sharper: prove the
    positive active trailing-column norm and the budget inequality
    \(B_k<|\alpha_k|\) from a formal rank, nonbreakdown, or conditioning
    assumption for the computed loop.
59. Closed local scalar lower-bound bridges for the remaining QR
    nonbreakdown route.  The theorem
    `householderTrailingNorm2Sq_pos_of_exists_ne` proves that the positive
    active trailing-column norm follows from a concrete nonzero active
    trailing entry; `householderTrailingNorm2Sq_pos_of_pivot_ne_zero` records
    the pivot-entry special case.  The theorem
    `abs_alpha_eq_sqrt_trailingNorm2Sq` rewrites
    \(|\alpha_k|\) as \(\sqrt{\|A_k(k{:}m,k)\|_2^2}\) under the standard
    Householder choice
    \(\alpha_k^2=\|A_k(k{:}m,k)\|_2^2\), and
    `budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq` converts a square-root
    trailing-norm budget into the existing per-pivot condition
    \(B_k<|\alpha_k|\).  This does not close the rank/conditioning theorem;
    it narrows the external/source-proof search to deriving a nonzero active
    trailing entry and a usable square-root lower bound from a formal full-rank,
    nonbreakdown, or conditioning assumption.  External source notes already
    identify Higham, Accuracy and Stability of Numerical Algorithms, Chapter 19
    (DOI `10.1137/1.9780898718027.ch19`) as the QR stability source, while the
    local QR nonzero-diagonal route still requires formal rank infrastructure.
60. Closed the first local prefix-span nonbreakdown bridge for the remaining
    QR rank route.  The new predicates `qrColumnNotInPreviousSpan` and
    `qrPrefixSupportSpannedByPreviousColumns` express the source QR fact that
    the pivot column is not generated by previous columns while the already
    completed triangular block spans the prefix-supported vectors.  The theorem
    `exists_active_trailing_entry_ne_of_column_notInPreviousSpan` proves that
    these two invariants imply a nonzero active trailing entry, and
    `householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan` converts it
    to the positive trailing norm.  The wrapper
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`
    combines this bridge with the prior sign-choice and square-root-budget
    bridges to prove final nonzero stored diagonal entries.  This is a local
    formalization step guided by the standard Householder QR proof route in
    Higham, Accuracy and Stability of Numerical Algorithms, Chapter 19 (DOI
    `10.1137/1.9780898718027.ch19`); it does not close the full-rank theorem.
    The next source-proof target is deriving `qrColumnNotInPreviousSpan` and
    `qrPrefixSupportSpannedByPreviousColumns` from a formal invertible leading
    triangular block or equivalent full-rank/nonbreakdown invariant.
61. Closed a local prefix-span coefficient dependency for the same QR rank
    route.  The new definition `qrPrefixBasisCoefficientMatrix` records the
    concrete leading-block coefficient witness
    \(\sum_{j<k} C_{rj} A_k(s,j)=\delta_{sr}\), and
    `qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`
    proves that this witness, together with the already-formalized QR
    lower-zero shape for previous columns below row \(k\), gives
    `qrPrefixSupportSpannedByPreviousColumns`.  This is the finite-coordinate
    algebra inside the standard nonsingular leading triangular block argument;
    it is not yet the determinant/right-inverse theorem that produces the
    coefficient matrix.  The remaining source-proof target is now narrower:
    produce the coefficient witness from a concrete nonsingular/invertible
    leading block or equivalent full-rank invariant, prove the current-column
    independence invariant, and prove a usable square-root trailing-norm
    budget lower bound.
62. Closed the matching current-column independence adapter for the QR rank
    route.  The definition `qrLeadingColumnLeftInverse` records a concrete
    dual coefficient family selecting the first \(k+1\) columns, and
    `qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse` proves that such a
    witness forbids expressing column \(k\) as a combination of columns
    \(0,\ldots,k-1\).  The proof is the standard finite-coordinate left-inverse
    argument: apply the \(k\)-th dual row to a hypothetical dependence to get
    \(1=0\).  This does not yet produce the left inverse from determinant,
    triangular, or rank assumptions; it narrows the remaining route to proving
    the leading-block basis/left-inverse witnesses and the square-root
    trailing-norm budget lower bound from a formal nonsingular/full-rank or
    conditioning invariant.
63. Closed the local composition step that consumes the concrete leading-block
    witnesses in the stored QR nonbreakdown route.  The theorems
    `exists_active_trailing_entry_ne_of_leading_witnesses` and
    `householderTrailingNorm2Sq_pos_of_leading_witnesses` combine the
    coefficient-matrix prefix-span witness, the leading-column left-inverse
    witness, and the QR lower-zero shape to produce a nonzero active trailing
    entry and a positive trailing norm.  The wrapper
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget`
    feeds those concrete witnesses into the stored-loop nonzero-diagonal
    theorem together with sign choice and the explicit square-root budget
    lower bound.  This closes a listed dependency of the QR bottleneck, not
    the determinant/full-rank or conditioning theorem that produces the
    witnesses and the quantitative budget lower bound.
64. Closed an orientation adapter from the repository's existing inverse
    vocabulary to the QR prefix coefficient witness.  The definition
    `qrPreviousLeadingBlockTranspose` packages the transpose of the leading
    `k × k` block, and
    `qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose`
    proves that `IsLeftInverse` for this transposed block supplies
    `qrPrefixBasisCoefficientMatrix`.  This uses the local
    `IsLeftInverse` predicate from `MatrixAlgebra.lean`; it does not prove
    that such an inverse exists from determinant, triangular, or rank
    assumptions.
65. Closed the matching padding/reindexing adapter from the repository's
    existing inverse vocabulary to the QR leading-column dual witness.  The
    definition `qrLeadingBlock` names the actual leading `(k+1) × (k+1)`
    block, and
    `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` proves that a
    local `IsLeftInverse` for this block, padded by zeros outside the first
    `k+1` rows, supplies `qrLeadingColumnLeftInverse`.  This closes the
    finite ambient-row bookkeeping needed by the nonbreakdown route.  It still
    does not prove existence of that inverse from determinant, triangular, or
    rank assumptions.
66. Closed the direct local-inverse composition for the stored QR
    nonbreakdown route.  The theorems
    `exists_active_trailing_entry_ne_of_leading_block_leftInverses` and
    `householderTrailingNorm2Sq_pos_of_leading_block_leftInverses` compose the
    prefix-block and leading-block `IsLeftInverse` adapters into a nonzero
    active trailing entry and positive trailing norm.  The stored-loop wrapper
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget`
    then consumes those local inverse witnesses, sign choice, and the explicit
    square-root budget.  This is still not a determinant/full-rank theorem:
    existence of the local left inverses and the quantitative budget lower
    bound remain open bottleneck dependencies.
67. Closed the determinant/rank bridge for the local inverse witnesses in the
    stored QR nonbreakdown route.  The MatrixAlgebra foundation
    `exists_isLeftInverse_of_det_ne_zero` wraps Mathlib's nonsingular inverse
    and proves that \(\det T\ne0\) supplies the repository's
    `IsLeftInverse` predicate.  The QR adapters
    `qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose`
    and `qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock` generate the
    two local witnesses from nonzero determinants of the transposed previous
    leading block and actual leading block.  The theorems
    `exists_active_trailing_entry_ne_of_leading_block_det_ne_zero`,
    `householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget`
    feed these determinant hypotheses into the same stored-loop diagonal
    nonbreakdown route.  This is still not a proof that the computed leading
    blocks are nonsingular, and it still keeps the square-root trailing-norm
    budget lower bound explicit.  Two weak-component passes have validated the
    Lean statements, axiom footprint, lookup/PDF synchronization, and rendered
    theorem pages.
68. Added the triangular determinant route for the same QR nonbreakdown
    bottleneck.  The shared algebra lemmas
    `det_ne_zero_of_upper_triangular_diag_ne_zero` and
    `det_ne_zero_of_lower_triangular_diag_ne_zero` use Mathlib's triangular
    determinant formula to prove that triangular finite real matrices with
    nonzero diagonal have nonzero determinant.  The QR adapters
    `qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
    and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero`
    instantiate this on the local previous and current leading blocks.  This
    is a principal-minor route, not a proof that ordinary full column rank
    implies those leading principal minors are nonzero.  Two weak-component
    passes validated the Lean statements, axiom footprint, lookup/PDF
    synchronization, and rendered theorem pages.
69. Added the solver-facing nonsingular-leading-block QR certificate route.
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget`
    composes the determinant/rank nonbreakdown bridge, sign-choice
    denominator bridge, square-root pivot-budget bridge, stored-loop QR
    perturbation theorem, and rounded top-block triangular-solve handoff into
    the local least-squares QR backward-error certificate.  This is a local
    formal composition of already-proved repository facts; it still leaves the
    source-level determinant/rank facts for the computed leading blocks and
    the usable square-root trailing-norm budget lower bound as open proof
    obligations.  Two weak-component passes validated the Lean statement,
    standard axiom footprint, lookup/PDF synchronization, and rendered theorem
    pages.
70. Added the solver-facing triangular-leading-block QR certificate route and
    validated it with two weak-component passes.
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget`
    composes the triangular determinant adapters with the nonsingular-leading
    block solver wrapper.  It is a local Lean proof under visible
    upper-triangular shape, nonzero previous/current leading diagonals, sign
    choice, square-root pivot budgets, compact update budgets, and final
    Gram/RHS budgets.  This documents the triangular-principal-minor route as
    a domain theorem; the source-faithful route from ordinary full rank or a
    conditioning invariant remains open, as does deriving a usable
    square-root budget lower bound.  The second pass used a full `lake build`,
    repeated lookup and axiom audits, placeholder and whitespace scans, and a
    Ghostscript-repaired exact-path PDF text/render inspection because the raw
    pdfTeX output triggered Poppler page-tree warnings.
71. Added and two-pass validated the active-entry square-root budget bridge.
    `abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le` proves the
    coordinate inequality \(|x_i| \le \sqrt{\|x_{\mathrm{tail}}\|_2^2}\) for
    every active trailing index \(i\ge k\), and
    `budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry` turns a
    concrete entry lower bound `budget < |x i|` into the square-root trailing
    norm budget consumed by the stored QR diagonal and solver wrappers.  This
    is a real listed dependency for the QR red bottleneck, but it is not a
    source-faithful rank or conditioning theorem; the next source route must
    derive such an active-entry lower bound from a formal invariant or keep it
    visible as a domain assumption.
72. Added and two-pass validated the stored-loop active-entry-budget
    nonbreakdown wrapper.  The theorem
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget`
    composes the prefix-span nonbreakdown bridge with the active-entry scalar
    budget bridge: if every pivot column has an active row \(i\ge k\) whose
    magnitude dominates the compact diagonal update budget, then the previous
    square-root trailing-norm budget follows and the final stored triangular
    diagonal is nonzero.  This closes a listed wrapper dependency, not the
    source-faithful derivation of the active-entry lower bound from rank,
    nonbreakdown, or conditioning.
73. Added and two-pass validated the solver-facing active-entry-budget QR
    certificate wrapper.  The theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget`
    composes prefix-span nonbreakdown, sign choice, Householder normalization,
    compact panel/RHS budget domination, and a visible active-entry lower bound
    into the local `LSQRSolveBackwardError` certificate for the stored trailing
    QR loop.  This removes the square-root budget from this solver-facing route,
    but it still does not derive the active-entry lower bound from rank,
    nonbreakdown, or conditioning.  The two passes used the targeted
    `LSQRSolve` build followed by full `lake build`, executable lookup,
    placeholder and whitespace scans, fully qualified axiom audit, PDF compile,
    and exact-path repaired-PDF text/render inspection.
74. Added and two-pass validated the dimensioned norm-square-budget bridge for
    the same QR red bottleneck.  The finite lemma
    `exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
    proves that the margin
    \(m B^2 < \|x(p:m)\|_2^2\) forces some active trailing entry to satisfy
    \(B < |x_i|\).  The stored-loop wrapper
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
    and solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget`
    compose this margin with the active-entry route.  This is a real listed
    dependency closure and a cleaner target for a future conditioning argument,
    but it is still not itself a conditioning theorem: the source-faithful
    route must next derive the displayed norm-square margin from an invariant
    of the computed QR loop, or keep it as an explicit domain assumption.
75. Added and two-pass validated the leading-dual norm lower-bound route for
    the same QR red bottleneck.  The lemma
    `householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget` proves that a
    leading dual row for the current pivot column, together with prefix-span and
    `||L_last||_2^2 <= K`, gives
    \(1/K \le \|A_k(k:m,k)\|_2^2\).  The corollary
    `dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget` turns
    `m * budget^2 < 1 / K` into the dimensioned norm-square margin, and the
    stored-loop and solver wrappers
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget`
    lift that route into QR diagonal nonbreakdown and
    `LSQRSolveBackwardError`.  This is a listed dependency closure because it
    derives a quantitative trailing-norm lower bound from an explicit dual
    certificate, but it is not yet a construction of that dual from SVD,
    determinant margins, or condition-number hypotheses.  The two passes used
    a targeted `LSQRSolve` build followed by full `lake build`, executable
    lookup, placeholder and whitespace scans, fully qualified axiom audits,
    PDF compile, and exact-path repaired-PDF text/render inspection.
76. Added and two-pass validated the local leading-block inverse row-norm route.
    The padding lemmas
    `vecNorm2Sq_qrLeadingRow_padded_eq` and
    `qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` show that the last row of
    a local left inverse for `qrLeadingBlock` can be padded to the ambient
    leading dual without changing its squared Euclidean norm.  The quantitative
    theorem
    `householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget`
    then reuses the leading-dual argument with the visible local row budget
    `||C_k(k,:)||_2^2 <= K_k`, and the stored-loop/solver wrappers lift the
    route into QR diagonal nonbreakdown and `LSQRSolveBackwardError`.  This is a
    genuine listed dependency closure because it constructs the dual from a
    concrete local inverse; it is still not a theorem deriving the row-norm
    budget from determinant margins, SVD, or a condition number.  The two passes
    used targeted QR/LS builds followed by full `lake build`, executable
    lookup, placeholder and whitespace scans, fully qualified axiom audits, PDF
    compile, and exact-path repaired-PDF text/render inspection.
77. Added and two-pass validated the local leading-block inverse
    Frobenius-norm route.  The shared matrix algebra lemmas
    `vecNorm2Sq_row_le_frobNormSq` and `vecNorm2Sq_row_le_frobNorm_sq` prove
    that any row squared norm is bounded by the Frobenius norm square.  The QR
    theorem
    `householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_frobNorm_budget`
    uses this to replace the local inverse row budget by a local inverse
    Frobenius budget, and the stored-loop/solver wrappers
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
    lift the route into QR diagonal nonbreakdown and `LSQRSolveBackwardError`.
    This is a listed dependency closure because it derives the row budget from
    an inverse norm budget already attached to the local inverse witness; it is
    not yet a source theorem deriving that Frobenius inverse budget from
    determinant margins, singular values, or condition numbers.  The two passes
    used a targeted `LSQRSolve` build followed by full `lake build`,
    executable lookup, placeholder and whitespace scans, fully qualified axiom
    audits, PDF compile, and exact-path repaired-PDF text/render inspection.
78. Added and two-pass validated the local leading-block inverse infinity-norm
    route.  The shared matrix algebra lemmas
    `abs_coord_le_sum_abs`, `vecNorm2Sq_le_sum_abs_sq`,
    `frobNormSq_le_nat_mul_infNorm_sq`, and
    `frobNorm_sq_le_nat_mul_infNorm_sq` prove
    `||C_k||_F^2 <= (k+1)||C_k||_\infty^2`.  The QR theorem
    `householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_infNorm_budget`
    and the stored-loop/solver wrappers
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
    lift the route into QR diagonal nonbreakdown and `LSQRSolveBackwardError`
    from the visible inverse infinity-norm budget
    `(k+1)||C_k||_\infty^2 <= K_k`.  This is a listed dependency closure
    route because it derives the Frobenius budget from a standard inverse norm
    already attached to the local inverse witness; it is not yet a source
    theorem deriving that infinity-norm budget from triangular inverse
    estimates, determinant margins, singular values, or condition numbers.  The
    two passes used a targeted `LSQRSolve` build followed by full `lake build`,
    executable lookup, placeholder and whitespace scans, fully qualified axiom
    audits, PDF compile, and exact-path repaired-PDF text/render inspection.
79. Added the diagonal-dominant triangular inverse route for the QR local
    inverse budget.  `Algorithms/InverseBounds.lean` now exposes Higham
    Theorem 8.13 in repository norm form via `triInv_infNorm_upperBound`, and
    its squared QR-budget form
    `triInv_infNorm_sq_budget_of_diagDominantUpper`.  The solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget`
    composes that bound with the existing local inverse infinity-norm route.
    This is source-aligned with Higham's diagonal-dominant triangular inverse
    estimate and closes a listed inverse-norm dependency under visible local
    diagonal-dominance and full-inverse hypotheses.  It does not prove that
    the computed QR leading blocks satisfy diagonal dominance; that remains a
    separate source/domain condition.  Two weak-component passes used targeted
    and full builds, executable lookup, placeholder and whitespace scans,
    fully qualified axiom audits, PDF compile, and exact-path repaired-PDF
    text/render inspection.
80. Added the determinant-facing diagonal-dominant inverse route.  The local
    matrix algebra bridge now proves `isRightInverse_nonsingInv_of_det_isUnit`,
    `isInverse_nonsingInv_of_det_isUnit`,
    `isInverse_nonsingInv_of_det_ne_zero`, and
    `exists_isInverse_of_det_ne_zero`, so nonzero determinant supplies the full
    repository `IsInverse` witness needed by Higham's triangular inverse bound.
    `Algorithms/InverseBounds.lean` now exposes
    `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero`, and
    `LSQRSolve.lean` exposes
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget`.
    This closes the explicit-inverse-witness subdependency for the
    diagonal-dominant branch under visible determinant hypotheses.  It still
    does not prove diagonal dominance, determinant nonzero, or the
    diagonal-minimum budget from a generic computed QR loop.  Two
    weak-component passes succeeded with targeted and full builds, executable
    lookup, placeholder and whitespace scans, fully qualified axiom audits, PDF
    compile, and repaired-PDF text/render inspection.
81. Added the determinant-facing inverse-norm route.  The new solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget`
    instantiates the inverse-\(\infty\) QR route with
    `C_k = nonsingInv S_k` from `det S_k != 0`, while retaining the visible
    quantitative budget `(k+1)||nonsingInv S_k||_\infty^2 <= K_k`.  This is a
    direct listed dependency for the red QR bottleneck because it removes the
    local inverse witness from the inverse-norm branch without assuming
    diagonal dominance.  It still does not prove that inverse-norm budget from
    SVD, condition numbers, determinant margins, or a computed-loop invariant.
    Targeted and full builds plus two weak-component passes succeeded with
    executable lookup, placeholder and whitespace scans, fully qualified axiom
    audit, PDF compile, and repaired-PDF text/render inspection.  This source
    row is closed as a visible-domain dependency; the inverse-norm budget route
    remains the next mathematical frontier.
82. Added the condition-number route for the local inverse-norm QR budget.  The
    perturbation layer now proves
    `infNorm_eq_sup_row_sum`, `kappaInf_eq_infNorm_mul_infNorm`,
    `infNorm_inv_le_of_kappaInf_le_and_norm_lower`, and
    `infNorm_sq_budget_of_kappaInf_le_and_norm_lower`, connecting Higham's
    explicit row-sum `kappaInf` definition to the repository `infNorm` API.
    The new solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget`
    derives the visible inverse-\(\infty\) budget from
    `0 < rho_k <= ||S_k||_\infty`,
    `kappaInf S_k (nonsingInv S_k) <= kappa_k`, and
    `(k+1)(kappa_k/rho_k)^2 <= K_k`, then applies the determinant-facing
    inverse-norm route.  Two weak-component passes succeeded: targeted and full
    builds passed with only pre-existing warnings; executable lookup,
    placeholder and whitespace scans, fully qualified axiom audit, PDF compile,
    repaired-PDF text extraction, and rendered page inspection were clean.  This
    closes the condition-number route as a visible-domain dependency.  It still
    does not derive the local norm lower bound, the local condition-number
    bound, or nonsingularity from SVD, determinant margins, or a computed-loop
    invariant.
83. Added the determinant-based self-norm specialization of the condition-number
    route.  The exact algebra lemma `infNorm_pos_of_det_ne_zero` proves
    `det S != 0 -> 0 < ||S||_infty`; the perturbation bridge
    `infNorm_inv_le_of_kappaInf_le_and_det_ne_zero` and
    `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` then specialize the
    previous `rho`-parameter theorem with `rho = ||S||_infty`.  The solver
    wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`
    removes the separate local norm-lower-bound hypothesis from the QR route.
    Two weak-component passes succeeded: targeted and full builds passed with
    only pre-existing warnings; executable lookup, placeholder and whitespace
    scans, fully qualified axiom audits, PDF compile/repair/text extraction,
    and rendered page inspections were clean.  This is a listed dependency
    closure as a visible-domain route.  It still leaves the local determinant
    and `kappaInf` assumptions visible.
84. Added the determinant-facing prefix-span bridge for the self-norm
    condition-number QR route.  The QR theorem
    `qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose`
    derives the abstract prefix-span invariant from `det T_k != 0` for the
    previous transposed leading block plus the completed-column lower-zero
    shape.  The solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`
    feeds this into the self-norm `κ∞` route.  Two weak-component passes
    passed: targeted/full builds, lookup, placeholder scan, `git diff --check`,
    fully qualified axiom audit, PDF compile/repair/text extraction, and
    rendered page inspection were clean.  This is a listed dependency closure
    under visible previous/current determinant assumptions, completed-column
    lower-zero shape, local condition-number bound, sign choice,
    compact-update budgets, and final solver budgets.
85. Added the triangular-principal-minor self-norm condition-number route.
    The solver theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget`
    derives the previous/current leading-block determinant hypotheses and the
    completed-column lower-zero shape from a visible upper-triangular local
    shape plus nonzero previous/current leading diagonals, then applies the
    determinant-facing prefix-span self-norm `κ∞` route.  Two weak-component
    passes passed: targeted and full builds, lookup, placeholder scan,
    `git diff --check`, fully qualified axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean.
    This is a listed dependency closure under visible triangular/nonzero-local
    diagonal, local condition-number, sign-choice, compact-update, and final
    solver-budget assumptions.  It still leaves the computed-loop derivation of
    those assumptions, or an explicit decision to keep them as domain
    assumptions, in the red QR bottleneck.
86. Added the computed-prefix-zero triangular self-norm condition-number route.
    The QR theorem `fl_householderStoredPanel_sequence_prefix_lower_zero`
    exposes the stored-loop induction that after `k` steps the first `k`
    completed columns have exact lower-zero shape.  The local determinant
    adapters
    `qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero`
    and
    `qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero`
    use only the displayed leading-block triangular entries.  The solver
    theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
    derives the previous/current determinant hypotheses and completed-column
    lower-zero shape from the stored recurrence itself, then applies the
    determinant-facing prefix-span self-norm `κ∞` route.  The first
    weak-component pass passed: targeted QR/LS builds, lookup, placeholder
    scan, `git diff --check`, fully qualified axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean.
    The second pass also passed: full `lake build`, lookup, placeholder scan,
    `git diff --check`, repeated axiom audit, PDF compile/repair/text
    extraction, and rendered page inspection were clean.  This is a listed
    dependency closure for the computed triangular-shape part of the red QR
    bottleneck.  It still leaves nonzero local diagonals, local
    condition-number bounds, sign choice, compact-update budgets, and final
    solver budgets visible.
87. Added the concrete signed-alpha specialization of the Householder QR
    route.  No external source beyond the already-recorded Higham/Cox--Higham
    Householder QR route was needed: this is the standard scalar sign
    convention, formalized locally by case analysis on the pivot sign.  The
    new scalar definitions and lemmas
    `signedHouseholderAlpha`, `signedHouseholderAlpha_sq`,
    `signedHouseholderAlpha_mul_pivot_nonpos`,
    `signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq`, and
    `signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos` prove that
    the signed trailing norm supplies the Householder normalization and
    sign-choice hypotheses.  The QR and solver wrappers
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`,
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget`,
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
    feed that scalar rule into the stored-loop nonbreakdown and computed
    prefix-zero self-norm QR certificate.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.  This closes the sign-choice dependency of the red
    QR bottleneck.
88. Added a prefix-local stored-loop diagonal preservation route for the
    Householder QR bottleneck.  No new external source was needed: this is a
    direct consequence of the stored panel update, which preserves completed
    columns.  The new generic theorem
    `fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero`
    and signed-alpha specialization
    `fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`
    prove that previous pivots remain nonzero at every intermediate prefix.
    The LSQRSolve wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
    consumes those facts and leaves only the current pivot nonzero condition
    visible.  Two weak-component passes passed: targeted/full builds,
    executable lookup, placeholder scan, whitespace check, axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean,
    with one lookup rerun after a transient concurrent-build race.  This closes
    the previous-diagonal part of the red QR nonbreakdown dependency.
89. Added explicit final Gram/RHS radii for the prefix-local stored QR
    certificate.  No new external source was needed: this is a direct
    instantiation of the repository's existing rectangular perturbation budget
    definitions.  The new definitions
    `qrSolveFinalDataPerturbationBudget`, `qrSolveFinalRhsPerturbationBudget`,
    `qrSolveFinalGramBudget`, and `qrSolveFinalRhsBudget` package the final
    solver radii, while
    `rectLSRhsPerturbationNormBudget_le_sum` supplies the scalar RHS
    domination bound.  The wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
    consumes those facts.  Two weak-component passes passed: targeted/full
    builds, executable lookup, placeholder scan, whitespace check, axiom audit,
    PDF compile/repair/text extraction, and rendered page inspection were
    clean.  This closes the final Gram/RHS solver-budget dependency of the red
    QR bottleneck.
90. Added explicit compact-update budgets for the prefix-local stored QR
    certificate.  No new external source was needed: this is a direct
    repository budget construction from the already-formalized compact
    Householder vector and panel update contracts.  The new one-vector and
    one-panel definitions
    `householderCompactRelativeBudget` and
    `householderCompactPanelRelativeBudget` are summed by
    `storedQRCompactStepRelativeBudget` and
    `storedQRCompactSequenceRelativeBudget`, with column/RHS domination
    theorems feeding the solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
    Two weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean.
    This closes the compact-update-domination dependency of the red QR
    bottleneck without adding a literature assumption.
91. Added the positive-trailing-norm-from-square-root-budget bridge for the
    prefix-local stored QR certificate.  No new external source was needed:
    this is a direct scalar consequence of nonnegativity, strict comparison
    with a real square root, and the repository's trailing-norm-square
    definition.  The theorem
    `householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt` proves that a
    nonnegative budget below
    `sqrt (householderTrailingNorm2Sq n p x)` forces
    `0 < householderTrailingNorm2Sq n p x`.  The explicit final-budget and
    explicit compact-budget LSQRSolve wrappers now derive positive trailing
    norms internally from their square-root budget hypotheses.  Two
    weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean.
    This closes the separate positive-trailing-norm side condition without
    adding a literature assumption.
92. Added the direct norm-square-to-square-root pivot-budget bridge for the
    stored QR bottleneck.  No new external source was needed: this is a local
    finite-dimensional scalar consequence of the repository's dimensioned
    norm-margin lemma and trailing-norm-square definition.  The theorem
    `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
    proves that a nonnegative budget with
    `m * budget^2 < householderTrailingNorm2Sq m p x` directly satisfies the
    square-root pivot-budget hypothesis.  The stored QR theorem
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
    now feeds this bridge directly into the square-root route instead of first
    constructing an active-entry witness.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.  This closes the scalar conversion part of the
    compact pivot-budget dependency without adding a literature assumption.
93. Added the solver-facing norm-square pivot-margin route for the explicit
    compact QR certificate.  No new external source was needed: this wrapper
    composes the local scalar bridge from item 92 with the already formalized
    explicit compact-update/final-radius LSQRSolve certificate.  The theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget`
    replaces the visible square-root pivot budget by the dimensioned margin
    `m * budget_k^2 < ||A_k(k:m,k)||_2^2` in the latest solver-facing route.
    Two weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
    extraction, and rendered page inspection were clean.  This closes the
    square-root-expression side of the explicit compact QR certificate without
    adding a literature assumption; current-pivot nonzero/nonbreakdown, local
    condition-number assumptions, and the derivation of the norm-square margin
    from conditioning remain open bottleneck dependencies.
94. Added a local route-elimination counterexample for the rectangular QR
    bottleneck.  No external source was needed: the real `2 x 2` column-swap
    matrix has nonzero determinant and zero first unpivoted pivot.  The Lean
    facts `qrPivotCounterexample2_first_pivot_zero`,
    `qrPivotCounterexample2_det_ne_zero`, and
    `not_forall_det_ne_zero_implies_first_pivot_ne_zero` formalize that
    ordinary nonsingularity/full rank alone cannot replace the current-pivot
    nonzero hypothesis in an unpivoted Householder QR route.  Two
    weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection.  This is a
    route elimination, not a positive nonbreakdown theorem; the remaining proof
    route must use pivoting, an explicit no-breakdown condition, or a stronger
    structured invariant.
95. Added the structured current-pivot route for the rectangular QR bottleneck.
    No external source was needed: this is a local consequence of the finite
    triangular determinant formula and the already formalized stored-loop
    lower-zero shape.  The shared theorem
    `diag_ne_zero_of_upper_triangular_det_ne_zero` proves that a finite real
    upper-triangular matrix with nonzero determinant has every diagonal entry
    nonzero.  The QR theorem
    `qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero`
    applies this to the displayed local leading block, and
    `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`
    supplies the upper-triangular shape from the stored recurrence.  The solver
    wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`
    consumes nonsingular local leading blocks instead of a bare current-pivot
    nonzero hypothesis.  Two weak-component passes passed: targeted/full
    builds, executable lookup, placeholder scan, whitespace check, axiom audit,
    PDF compile/repair/text extraction, and rendered page inspection were
    clean.  This is a structured no-pivot local-leading-minor route, not a
    generic full-rank theorem; local `kappaInf` assumptions and the
    conditioning-to-norm-square/dual compact pivot-budget derivations remain
    open.
96. Added the structured norm-square margin route from local leading blocks and
    `kappaInf`/dual budgets.  No external source was needed: this is a local
    composition of the stored-loop lower-zero shape, the triangular determinant
    current-pivot route, the determinant-facing `kappaInf` inverse bridge, and
    the leading-dual norm theorem.  The QR theorem
    `qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero`
    derives the prefix-span invariant from local upper-triangular leading
    blocks with nonzero determinant.  The solver wrapper
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
    then removes the separate dimensioned norm-square compact pivot-margin
    hypothesis by deriving it from the visible local `kappaInf` budget and the
    dual compact-budget inequality.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.  The red QR bottleneck is now narrowed to deriving
    or justifying local `kappaInf`, `K_k`, and dual compact-budget assumptions
    from conditioning or a computed-loop invariant.
97. Added the structured direct inverse-∞ budget route for the latest explicit
    compact QR certificate.  No external source was needed: this is a local
    composition of the stored lower-zero prefix-span bridge, the
    determinant-facing inverse-∞ solver route, and the explicit compact/final
    QR budget wrappers.  The solver theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget`
    removes the local `kappaInf` and self-norm hypotheses when the direct
    budget `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` is visible, while still
    keeping local leading-block determinants and the dual compact-budget
    inequality explicit.  Two weak-component passes passed: targeted/full
    builds, executable lookup, placeholder scan, whitespace check, axiom audit,
    PDF compile/repair/text extraction, and rendered page inspection were
    clean.  The red QR bottleneck is now narrowed to deriving the direct
    inverse-∞ and dual compact-budget assumptions from diagonal dominance,
    conditioning, or a computed-loop invariant, or keeping them as visible
    source/domain assumptions.
98. Added the diagonal-dominant structured direct inverse-∞ route for the
    latest explicit compact QR certificate.  No external source was needed:
    this is a local composition of the already formalized Higham triangular
    inverse estimate
    `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero` with the
    structured direct inverse-budget QR certificate.  The solver theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget`
    derives `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` from local diagonal
    dominance, `det S_k != 0`, and Higham's diagonal-minimum budget, then
    applies the direct inverse-budget route.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.  The red QR bottleneck is now narrowed to deriving
    local diagonal dominance and the dual compact-budget inequality from
    conditioning or a computed-loop invariant, or keeping them as visible
    source/domain assumptions.
99. Added the diagonal-dominance route-elimination theorem for the rectangular
    QR bottleneck.  No external source was needed: the local counterexample is
    the concrete `2 x 2` matrix `[[1,2],[0,1]]`.  The Lean theorems
    `diagDominanceCounterexample2_upper`,
    `diagDominanceCounterexample2_diag_nonzero`,
    `diagDominanceCounterexample2_not_diagDominant`, and
    `not_forall_upper_tri_diag_nonzero_implies_diagDominant` prove that
    upper-triangular shape plus nonzero diagonal entries alone cannot imply
    `IsDiagDominantUpper`.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.  This is a route elimination, not a positive
    diagonal-dominance theorem; the remaining route must derive diagonal
    dominance from a stronger computed-loop/conditioning invariant or keep it
    visibly as a domain assumption.
100. Added the concrete-dual diagonal-dominant QR route.  No new external
    source was needed: this is a local algebraic composition of the already
    formalized Higham triangular inverse estimate with the latest
    diagonal-dominant compact QR certificate.  The new local definition
    `diagDominantUpperInvBudgetExpr` names the displayed budget `D_k`, the
    theorem `diagDominantUpperInvBudgetExpr_pos` proves `D_k > 0`, and
    `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget`
    validates the concrete choice `K_k = 2D_k`.  The LSQRSolve theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget`
    replaces the separate `D_k <= K_k` and `m * budget_k^2 < 1/K_k`
    hypotheses by the direct condition `m * budget_k^2 < 1/(2D_k)`.
    Two weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
    extraction, and rendered page inspection were clean.
101. Front-loaded proof-source acquisition for the remaining source-faithful
    rectangular QR route inspected Higham's *Accuracy and Stability of
    Numerical Algorithms*, second edition, Chapter 19, especially Lemma 19.3
    and Theorems 19.4--19.6, at
    `https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf`.  This source is
    advisory for route selection only; it did not close any Lean theorem by
    citation.  Any standard Householder QR least-squares backward-error theorem
    from this route must still be formalized locally before it can close a
    paper-level QR/preconditioner row.
102. Added the product-form concrete-dual diagonal-dominant QR route.  No new
    external source was needed: this is a local scalar-algebra composition on
    top of item 100.  The theorem
    `mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one` proves that
    `2D * (m * B^2) < 1` and `0 < D` imply
    `m * B^2 < 1/(2D)`.  The LSQRSolve theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget`
    uses `diagDominantUpperInvBudgetExpr_pos` for the required positivity and
    reuses the concrete-dual certificate from item 100.  Two weak-component
    passes passed: targeted/full builds, executable lookup, placeholder scan,
    whitespace check, axiom audit, PDF compile/repair/text extraction, and
    rendered page inspection were clean.
103. Added the positivity-only route-elimination theorem for the product-form
    compact QR bottleneck.  No new external source was needed: this is a local
    scalar counterexample in `InverseBounds.lean`.  The theorem
    `not_forall_pos_implies_two_mul_mul_sq_lt_one` proves that the implication
    `D > 0 -> 2D * (1 * B^2) < 1` is false in general, using the concrete
    values `D = 1` and `B = 1`.  This rules out closing the product compact
    smallness condition from denominator positivity alone; a future positive
    theorem must derive a genuine compact-update budget bound from a
    computed-loop/conditioning invariant or keep that bound visible.  Two
    weak-component passes passed: targeted/full builds, executable lookup,
    placeholder scan, whitespace check, axiom audit, PDF
    compile/repair/text extraction, and rendered page inspection were clean.
104. Strengthened the diagonal-dominance route elimination to the
    determinant-facing triangular nonsingularity route.  No new external source
    was needed: this uses the same local counterexample `[[1,2],[0,1]]` in
    `TriangularForwardBound.lean`.  The theorem
    `diagDominanceCounterexample2_det_ne_zero` proves its determinant is
    nonzero, and
    `not_forall_upper_tri_det_ne_zero_implies_diagDominant` proves that upper
    triangular shape plus determinant nonzeroness still does not imply
    `IsDiagDominantUpper`.  This closes the false determinant/nonsingularity
    route for the diagonal-dominant QR branch; a future positive theorem must
    derive diagonal dominance from a stronger computed-loop/conditioning
    invariant or keep it visible.  Two weak-component passes passed:
    targeted/full builds, executable lookup, placeholder scan, whitespace
    check, axiom audit, PDF compile/repair/text extraction, and rendered page
    inspection were clean.
105. Added the conditioning-facing diagonal-dominance route elimination for the
    rectangular QR bottleneck.  No new external source was needed: this is a
    local counterexample check against a proposed route.  The theorem
    `exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant` uses the
    same triangular matrix `[[1,2],[0,1]]`, takes the budget to be its own
    local `kappaInf` value, and proves that upper-triangular shape,
    determinant nonzeroness, and a finite `κ∞` certificate do not imply
    `IsDiagDominantUpper`.  The universal companion
    `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant`
    packages the failed route in implication form.  This does not close the
    positive QR theorem; it rules out using a generic finite condition-number
    bound as the missing diagonal-dominance invariant.  Two weak-component
    passes passed: targeted/full builds, executable lookup, placeholder scan,
    whitespace check, axiom audit, PDF compile/text extraction, and rendered
    page inspection were clean.
106. Added source-faithful leading-dual budget instantiation wrappers for the
    rectangular QR bottleneck.  No new external source was needed: this is a
    local composition of the existing prefix-span leading-dual certificate with
    the repository final perturbation budgets and stored compact-update
    sequence budget.  The theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget`
    chooses `qrSolveFinalGramBudget` and `qrSolveFinalRhsBudget`; the theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget`
    also chooses `storedQRCompactSequenceRelativeBudget` and reuses the local
    column/RHS compact-budget domination lemmas.  This closes a listed
    source-faithful budget-instantiation dependency while keeping the real
    remaining proof obligations visible: construct the leading dual, prove
    prefix-span, and derive the dual compact-smallness inequality from a
    computed-loop/conditioning invariant or classify them as explicit domain
    assumptions.  Two weak-component passes passed: targeted/full builds,
    executable lookup, touched-file placeholder scan, whitespace check, axiom
    audit, PDF compile/text extraction, and rendered page inspection were
    clean, with only pre-existing QR-family warnings in the full build.
107. Added source-faithful local inverse row-budget wrappers with repository
    final and compact budgets.  No new external source was needed: this reuses
    the local padding theorem
    `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock`, the padded-row
    norm identity, and the explicit leading-dual budget wrappers from row 106.
    The theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
    constructs the ambient leading dual from a local leading-block left
    inverse and chooses `qrSolveFinalGramBudget`/`qrSolveFinalRhsBudget`; the
    theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
    also chooses `storedQRCompactSequenceRelativeBudget`.  This closes the
    local-dual-construction plus budget-instantiation dependency under visible
    prefix-span, local left-inverse row-norm, sign-choice, and compact
    smallness hypotheses.  Two weak-component passes passed: targeted/full
    builds, lookup, touched-file placeholder scan, whitespace check, axiom
    audit, PDF compile/text extraction, and rendered page inspection.
108. Added source-faithful local inverse Frobenius/infinity wrappers with
    repository final and compact budgets.  No new external source was needed:
    this reuses the local row-versus-Frobenius bridge
    `vecNorm2Sq_row_le_frobNorm_sq`, the finite-matrix infinity/Frobenius
    bridge `frobNorm_sq_le_nat_mul_infNorm_sq`, and the repository-budget
    local inverse row wrappers from item 107.  The new Lean theorem names are
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`,
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`,
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`, and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`.
    This closes the visible Frobenius/infinity norm-budget instantiation
    branch under prefix-span, local left-inverse, sign-choice, and compact
    smallness hypotheses.  Two weak-component passes passed: targeted/full
    builds, lookup, touched-file placeholder scan, whitespace check, axiom
    audit, PDF compile/text extraction, and rendered page inspection.
109. Added the source-faithful stored-prefix-span local-inverse row wrapper.
    No new external source was needed: this is a local composition of the
    stored panel lower-zero theorem
    `fl_householderStoredPanel_sequence_prefix_lower_zero`, the local
    left-inverse prefix-span adapter
    `qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose`,
    and the row-budget compact LSQRSolve wrapper from item 107.  The QR
    sequence theorem
    `fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose`
    derives `qrPrefixSupportSpannedByPreviousColumns` for every pivot from the
    stored recurrence and previous-block local left inverses.  The solver
    theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`
    consumes that derived prefix-span fact in the row-norm compact-budget
    certificate.  This closes the separate prefix-span assumption for the
    row branch under visible previous/current local left inverses.  Two
    weak-component passes passed: targeted/full builds, lookup, touched-file
    placeholder scans, whitespace checks, repeated axiom audit, PDF
    compile/text extraction, and rendered page inspection.
110. Added the source-faithful stored-prefix-span Frobenius/infinity inverse
    budget wrappers.  No new external source was needed: these are local
    compositions of item 109's stored-prefix-span derivation with the existing
    repository-budgeted Frobenius and infinity inverse-norm LSQRSolve
    wrappers.  The new Lean names are
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`.
    They close the separate prefix-span assumption for the Frobenius/infinity
    compact-budget route under visible previous/current local left inverses.
    Two weak-component passes passed: targeted/full builds, lookup, touched-file
    placeholder scans, whitespace checks, repeated axiom audit, PDF
    compile/text extraction, and rendered page inspection.
111. Added the source-faithful signed-alpha stored-prefix-span row wrapper.
    No new external source was needed: this reuses the local
    `signedHouseholderAlpha` lemmas
    `signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq` and
    `signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos`, together
    with item 109's stored-prefix-span row certificate.  The Lean theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`
    replaces the separate squared-alpha and sign-choice hypotheses by the
    source Householder definition of `alpha`.  Two weak-component passes
    passed: targeted/full builds, lookup, touched-file placeholder scans,
    whitespace checks, repeated axiom audit, PDF compile/text extraction, and
    rendered page inspection.
112. Added the source-faithful signed-alpha stored-prefix-span Frobenius and
    infinity inverse-norm wrappers.  No new external source was needed: these
    reuse the same local `signedHouseholderAlpha` lemmas from item 111 and the
    stored-prefix-span inverse-norm wrappers from item 110.  The Lean theorem
    names are
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`.
    They replace the separate squared-alpha and sign-choice hypotheses by the
    source Householder definition of `alpha` for the Frobenius/infinity
    branches.  Two weak-component passes passed: targeted/full builds, lookup,
    touched-file placeholder scans, whitespace checks, repeated axiom audit,
    PDF compile/text extraction, and rendered page inspection.
113. Added the source-faithful signed-alpha determinant local-inverse wrappers.
    No new external source was needed: these reuse the repository exact algebra
    theorem `isInverse_nonsingInv_of_det_ne_zero` from
    `Analysis/MatrixAlgebra.lean`, together with the signed-alpha
    stored-prefix-span row/Frobenius/infinity certificates from items 111--112.
    The Lean theorem names are
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget`,
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_frobNorm_budget`,
    and
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget`.
    They replace the explicit previous/current local left-inverse witnesses by
    nonzero determinant hypotheses and `nonsingInv`, while keeping the
    row/Frobenius/infinity inverse-budget and compact-smallness assumptions
    visible.  Two weak-component passes passed: targeted/full builds, lookup,
    touched-file placeholder scans, whitespace checks, repeated axiom audit,
    PDF compile/page-local text extraction, and rendered page inspection.
114. Added the source-faithful signed-alpha determinant `κ∞` self-norm wrapper.
    No new external source was needed: this reuses the local perturbation
    theorem `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` and the direct
    inverse-∞ determinant wrapper from item 113.  The Lean theorem
    `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`
    derives the inverse-∞ budget from visible determinant, local `κ∞`, and
    self-norm squared-budget hypotheses.  Two weak-component passes passed:
    targeted/full builds, lookup, touched-file placeholder scans, whitespace
    checks, repeated axiom audit, PDF compile/page-local text extraction, and
    rendered page inspection.
115. Added the source-faithful signed-alpha triangular leading-block wrapper.
     No new external source was needed: this reuses the QR determinant bridges
     `qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
     and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero`, together
     with item 114.  The Lean theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget`
     derives the previous/current determinant facts from visible upper-triangular
     leading-block shape and nonzero displayed leading diagonal entries before
     applying the signed-alpha determinant `κ∞` route.  Two weak-component
     passes passed: targeted/full builds, lookup, touched-file placeholder
     scans, whitespace checks, repeated axiom audit, PDF compile/page-local text
     extraction, and rendered page inspection.
116. Added a local counterexample for the failed route "positive trailing norm
     implies current unpivoted pivot nonzero."  No external source was needed:
     this is the concrete two-entry active column `x = (0, 1)` at pivot `0`.
     The Lean names
     `householderTrailingPivotCounterexample2`,
     `householderTrailingPivotCounterexample2_pivot_zero`,
     `householderTrailingPivotCounterexample2_trailingNorm2Sq_pos`, and
     `not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero` prove that the
     active trailing squared norm is positive while the current pivot is zero.
     Two weak-component passes passed: targeted/full builds, lookup,
     touched-file placeholder scans, whitespace checks, repeated axiom audit,
     PDF compile/page-local text extraction, and rendered page inspection.
117. Added a local counterexample for the failed route "diagonal dominance and
     the displayed Higham inverse budget imply product compact smallness."  No
     external source was needed: this is the scalar `1 x 1` identity block with
     compact budget `B = 1` and row count `m = 1`.  The Lean theorem
     `not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one`
     proves that `IsDiagDominantUpper 1 U` holds while the product condition
     `2D * (m * B^2) < 1` is false.  Two weak-component passes passed:
     targeted/full builds, lookup, touched-file placeholder scans, whitespace
     checks, repeated axiom audit, PDF compile/page-local text extraction, and
     rendered page inspection.
118. Re-audited the external rectangular QR proof route after the product
     compact-smallness shortcut failed.  The existing source route remains
     Higham's QR notes, Section 4.1, Lemmas 4.3--4.4 and Theorem 4.5
     (`https://nhigham.com/wp-content/uploads/2023/10/high99n.pdf`), together
     with Cox--Higham, "Stability of Householder QR Factorization for Weighted
     Least Squares Problems", Theorem 1.1 and Section 2
     (`https://nhigham.com/wp-content/uploads/2023/08/cohi98.pdf`).  The
     source distinction is now explicit: Higham's standard theorem is
     columnwise/normwise and permits column-dependent perturbation matrices;
     Cox--Higham explains that row-wise weighted-LS stability for Householder
     QR is not generic without pivoting/sorting/sign-choice hypotheses.  This
     is a route-choice checkpoint, not a Lean theorem closure.  The next
     positive Lean target must either continue the columnwise Higham Theorem
     4.5 assembly, switch to the row-wise pivoted/sorted Cox--Higham theorem
     family, or keep the remaining hypotheses visibly as domain assumptions.
119. Chose the Higham columnwise route from item 118 and closed the final
     stored QR factorization assembly locally.  No new external source was
     needed beyond the item 118 route sources: the Lean theorem
     `fl_householderStoredTrailingPanel_higham_columnwise_factorization` reuses
     the local stored trailing sequence theorem
     `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
     together with the local stored top-block shape theorem
     `fl_householderStoredPanel_sequence_topBlock_shape_facts`.  The theorem
     proves the common orthogonal factor, columnwise/RHS perturbation bounds,
     final `[R;0]` shape, top transformed RHS, and upper-triangular `R`.  It is
     a factorization theorem only; it does not use external literature as a
     hidden hypothesis and it does not close the separate triangular-solve
     nonbreakdown, conditioning, or product-smallness obligations.
120. Strengthened the local route elimination for the no-pivot rectangular QR
     bottleneck.  No external source was needed: the same real `2 x 2`
     column-swap matrix used in item 100 has nonzero determinant, zero first
     unpivoted pivot, and zero determinant for its first `1 x 1` unpivoted
     leading QR block.  The new Lean facts
     `qrPivotCounterexample2_first_leadingBlock_det_zero` and
     `not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero` show that
     whole-matrix nonsingularity/full rank alone cannot replace the family of
     per-pivot leading-block determinant hypotheses in the unpivoted QR route.
     This is a route-elimination/theorem-statement-correction item, not a
     positive nonbreakdown theorem.  Two weak-component passes validated the
     Lean facts, lookup references, axiom audit, and PDF statement.
121. Ruled out collapsing the remaining diagonal-dominance and product
     compact-smallness assumptions into one another.  No external source was
     needed: the local counterexample `diagDominanceCounterexample2 =
     [[1,2],[0,1]]` is upper triangular and nonsingular but not diagonally
     dominant, and the new Lean theorem
     `not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant`
     chooses a small compact budget `B = 1/8` so the displayed product
     compact-smallness inequality holds anyway.  This is a route-elimination
     item: it does not prove diagonal dominance or product smallness from a
     computed-loop or conditioning invariant.  Two weak-component passes
     validated the Lean fact, lookup reference, axiom audit, PDF text
     extraction, and rendered PDF pages 124--125.
122. Added a computed-loop compact-budget bridge for the diagonal-dominant
     concrete-dual route.  No external source was needed.  The local QR theorem
     `storedQRCompactPivotBudget_le_sequence_column_norm` bounds the raw pivot
     compact component by the stored sequence budget times the current
     pivot-column norm.  The scalar theorem
     `two_mul_mul_sq_lt_one_of_nonneg_le` transfers product smallness along
     that nonnegative bound, and the LSQRSolve wrapper
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`
     replaces the raw-component product hypothesis by a visible
     sequence-column product hypothesis.  This advances the compact-smallness
     side of the red QR bottleneck, but it does not prove local diagonal
     dominance or the sequence-column product inequality from conditioning.
     Two weak-component passes validated the Lean facts, lookup references,
     axiom audit, PDF text extraction, and rendered PDF page 124.
123. Added a conditioning-facing product-smallness route elimination for the
     rectangular QR bottleneck.  No external source was needed.  The theorem
     `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one`
     shows that upper-triangular nonsingularity plus a finite local `κ∞`
     certificate does not imply the product compact-smallness inequality: the
     block `[[1,2],[0,1]]` has nonzero determinant and a finite formal
     conditioning value, but compact budget `B = 1` makes the product
     inequality false.  Two weak-component passes validated the Lean fact,
     lookup reference, axiom audit, PDF text extraction, and rendered PDF
     pages 125--126.
124. Recorded the route-choice checkpoint for the still-open rectangular
     QR/preconditioner solver handoff.  The external source chain remains
     unchanged: Higham's QR notes, Section 4.1, Lemmas 4.3--4.4 and
     Theorem 4.5, are the source for the columnwise/normwise Householder QR
     route, while Cox--Higham, "Stability of Householder QR Factorization for
     Weighted Least Squares Problems", Theorem 1.1 and Section 2, are the
     source for the stronger row-wise weighted least-squares route with
     pivoting/sorting/sign-choice hypotheses.  The new status is that no
     further adjacent Lean adapters count as progress until a route is chosen:
     stronger computed-loop/off-diagonal-control invariant, Cox--Higham
     pivoted/sorted theorem family, or visible domain assumptions for the
     remaining nonbreakdown/conditioning/product-smallness hypotheses.
125. Refined the Cox--Higham route as a source-backed scope correction rather
     than a proof closure.  Higham's QR notes, Section 4.1, Theorem 4.5, give
     the standard columnwise Householder result for the unpivoted QR route;
     the same section then treats the row-wise weighted-LS question separately
     and states that the row-wise answer is generally negative unless column
     pivoting is combined with row pivoting or row sorting and the recommended
     sign convention.  Cox--Higham, Theorem 1.1 and Sections 2--4, make the
     pivoting/sorting/sign-choice structure explicit.  Thus Cox--Higham is a
     valid future theorem family only after changing the algorithmic object; it
     cannot close the current unpivoted stored-QR equation (8) theorem by
     citation or by a small adapter.
126. Added an internal exact-QR-shape route elimination; no new external source
     was needed.  The local theorem
     `not_forall_orthogonal_upper_factorization_implies_diagDominant` uses the
     existing `[[1,2],[0,1]]` triangular counterexample with `Q = I`.  It
     proves that even an exact orthogonal-times-upper factorization with
     nonzero triangular diagonal cannot justify the repository's diagonal
     dominance hypothesis.  Therefore any remaining positive unpivoted route
     must formalize an actual computed-loop/off-diagonal-control invariant,
     not merely the final QR shape.
127. Added an internal exact-no-pivot-Householder route elimination; no new
     external source was needed.  The local theorem
     `not_forall_exact_trailing_householder_sequence_implies_diagDominant`
     uses the repository's exact trailing Householder recurrence, with
     explicit signed squared-norm scalars and nonzero denominators.  The
     two-step witness starts from `[[1,2],[0,1]]` and reaches
     `[[-1,-2],[0,-1]]`, which is upper triangular but violates
     `IsDiagDominantUpper`.  This rules out treating diagonal dominance as a
     generic consequence of the unpivoted Householder loop itself.  A positive
     route must add a genuine off-diagonal-control invariant, pivoting/sorting
     theorem family, or keep diagonal dominance visible.
128. After the user chose the stronger off-diagonal-control route, added the
     local route wrapper `StoredQROffDiagonalControlInvariant` and the solver
     theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl`.
     No new external source was needed for this packaging step: it explicitly
     bundles the remaining determinant, diagonal-dominance, and stored-sequence
     product-smallness obligations and feeds them into the already formalized
     diagonal-dominant stored-sequence certificate.  The next source-backed
     target is not another adapter; it is a theorem proving this invariant
     from source-specific off-diagonal-control, pivoting, or ordering
     assumptions, or else keeping the invariant visible as a domain condition.
129. Refined the off-diagonal-control route one layer closer to a source
     theorem.  `StoredQRSourceOffDiagonalControl` exposes local
     upper-triangular leading-block shape, nonzero local leading diagonals,
     row-wise off-diagonal domination, and the stored-sequence compact-product
     condition.  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl`
     proves the packaged invariant from these primitive fields using the
     already formalized triangular determinant lemma
     `det_ne_zero_of_upper_triangular_diag_ne_zero`, and the solver theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl`
     feeds those fields to the QR certificate.  No new external source was
     used; this is a local statement-shape correction.  The next proof-source
     target is now a genuine theorem deriving `StoredQRSourceOffDiagonalControl`
     from a pivoted/sorted/off-diagonal-growth assumption, or documenting that
     assumption as a domain hypothesis.
130. Reduced item 129 using an already formalized local source fact:
     `fl_householderStoredPanel_sequence_prefix_lower_zero` proves the
     triangular leading-block shape for the stored recurrence.  The new wrapper
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product`
     therefore removes upper-triangular shape from the remaining source
     obligations, and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diag_offdiag_product`
     exposes only nonzero diagonals, row-wise off-diagonal domination, and the
     compact-product bound.  No external source was used; this is a local
     library-reuse step.  The next proof-source target is now narrowed to
     sources or assumptions that imply those three quantitative/local fields.
131. Reduced item 130 using another already formalized local source fact:
     `fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`
     proves that previously written stored QR diagonal entries remain nonzero
     under the signed-alpha rule and the square-root nonbreakdown budget.  The
     new wrapper
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product`
     therefore removes the wholesale displayed-diagonal hypothesis from the
     source-shaped route, leaving current pivot nonzero, the square-root
     nonbreakdown budget, row-wise off-diagonal domination, and compact-product
     smallness visible.  The solver theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_pivot_sqrtBudget_offdiag_product`
     consumes this reduced source data.  No external source was used; this is
     a local library-reuse step.  Two weak-component passes validated the
     reduction; the next proof-source target is now a source, assumption, or
     route decision that supplies current pivot nonzero, the square-root
     nonbreakdown budget, row-wise off-diagonal domination, and compact-product
     smallness.
132. Route-choice checkpoint after item 131.  The local repository already
     contains the relevant route eliminations: nonsingularity/full rank does
     not imply current unpivoted pivot or all leading minors; positive trailing
     norm does not imply current pivot nonzero; exact QR shape, finite local
     conditioning, and the exact no-pivot recurrence do not imply the needed
     diagonal/off-diagonal-control fields; and diagonal dominance/product
     smallness do not imply one another.  No external source was used in this
     checkpoint.  The next proof-source step needs a source or user choice for
     one of three theorem families: explicit visible source assumptions,
     pivoted/sorted QR, or an application-specific off-diagonal-growth theorem.
133. Scoped item 132 for the current unpivoted theorem family by choosing the
     explicit visible source-assumption branch.  This reflects the current
     Algorithm 3/equation (8) object in the repository: it is an unpivoted
     stored QR loop, so the four residual source fields stay visible rather
     than being hidden or claimed as generic consequences.  The proof-source
     ledger should be reopened for this row only if the theorem family changes
     to pivoted/sorted QR or a concrete source/application class is supplied.
134. Closed a deterministic Algorithm 3 leverage-basis prerequisite with no
     external source.  The new theorems
     `preconditionRows_hasOrthonormalColumns_of_orthogonal`,
     `preconditionColumns_hasOrthonormalColumns_of_orthogonal`, and
     `preconditionElements_hasOrthonormalColumns_of_orthogonal` show that
     square orthogonal row/column/two-sided preprocessing preserves
     `HasOrthonormalColumns U`, while the three
     `rowSqNormProbDen_precondition*_eq_nat_of_orthogonal` corollaries reuse
     the local equation (6) denominator theorem to keep the denominator equal
     to `n`.  This reduces A3.4's local deterministic prerequisites but does
     not formalize any FJLT/Gaussian/Rademacher/input-sparsity concentration
     theorem or maximum-leverage uniformization bound.
135. Ran proof-source acquisition for the next A3.4 route and chose the SRHT
     Hadamard-sign path as the first concrete distribution family.  Primary
     source: Joel A. Tropp, "Improved analysis of the subsampled randomized
     Hadamard transform," Adv. Adapt. Data Anal. 3(1--2), 115--126, 2011,
     arXiv:1011.1595.  The route target is Lemma 3.3 (row norms), which says
     that for an orthonormal-column \(V\), the randomized sign/Hadamard product
     \(HDV\) remains orthonormal and has all row norms bounded by
     \(\sqrt{k/n}+\sqrt{8\log(\beta n)/n}\) with failure probability at most
     \(1/\beta\); Theorem 3.1 then composes this with uniform row sampling for
     the SRHT geometry theorem.  The repository now closes the deterministic
     orthogonality part locally with `IsOrthogonal.diagMatrix_of_sq_eq_one`,
     `signedOrthogonalPreconditioner_isOrthogonal`,
     `signedOrthogonalPreconditionRows_hasOrthonormalColumns`, and
     `rowSqNormProbDen_signedOrthogonalPreconditionRows_eq_nat`.  The
     Rademacher sign-law/support part is now also closed by item 136.  The next
     formal target is the concentration part of Lemma 3.3: Hadamard flatness
     \(|H_{ij}|^2=1/n\), convex/Lipschitz or scalar Hoeffding tail for each row,
     and a finite union bound for maximum row leverage.
136. Closed the finite Rademacher sign-law/support dependency for the SRHT
     route.  `RademacherTrace`, `rademacherSign`, `rademacherSignVector`, and
     `rademacherTraceProbability` define the uniform finite sign-vector law;
     `rademacherSignVector_sq` proves every realized sign has square one; and
     `rademacherTraceProbability_eventProb_signedOrthogonalPreconditionRows_eq_one`
     proves with probability one that the signed orthogonal preprocessor is
     orthogonal, preserves the orthonormal-column leverage basis, and keeps the
     equation (6) denominator equal to \(n\).  This does not use or prove
     Hadamard flatness, Rademacher/Hadamard row-norm concentration, or the
     maximum-leverage union bound from Tropp Lemma 3.3.
137. Closed the finite Rademacher moment and flat-Hadamard expectation
     dependency for the SRHT route.  The moment identities
     `rademacherTraceProbability_expectationReal_sign_eq_zero`,
     `rademacherTraceProbability_expectationReal_sign_mul_eq_ite`, and
     `rademacherTraceProbability_expectationReal_sq_sum_mul_sign_eq_sum_sq`
     prove zero mean, Kronecker-delta second moment, and signed-linear-form
     second moment for the finite sign law.  `HadamardFlat`,
     `signedHadamardPreconditionRows_entry`, and
     `rademacherTraceProbability_expectationReal_rowNormSq_signedHadamard_eq`
     prove the expectation identity
     \(\mathbb E\|(HD_\omega U)_{i,*}\|_2^2=n/m\) under flatness and
     \(U^TU=I\).  This is a local prerequisite for Tropp's Lemma 3.3 route,
     but it is not the high-probability row-norm tail or maximum-leverage
     theorem.
138. Closed the weak Markov/union tail available from item 137 without adding
     any new probability hypotheses.  The Lean theorems
     `rademacherTraceProbability_eventProb_rowNormSq_signedHadamard_le_ge_one_sub`,
     `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum`,
     `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub`,
     and
     `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_delta`
     prove that if
     \(m((n/m)/T)\le\delta\), then all flat signed-Hadamard row norms are at
     most \(T\) with probability at least \(1-\delta\).  This route uses only
     the local finite Markov inequality and finite union bound.  It is a valid
     auxiliary high-probability theorem but not Tropp Lemma 3.3, because it
     has Markov rather than subgaussian/logarithmic scaling.
139. Closed the next scalar concentration dependency for the SRHT route.  The
     Lean theorem
     `rademacherTraceProbability_expectationReal_exp_sum_mul_sign_eq_prod`
     factors
     \[
       \mathbb E \exp\left(\sum_k a_k\omega_k\right)
       =
       \prod_k \frac{e^{a_k}+e^{-a_k}}2
     \]
     directly from the finite Rademacher product law, and
     `rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_mul_prod`
     composes this with the local exponential-Markov kernel.  This does not
     yet prove Hoeffding's inequality or Tropp Lemma 3.3; the next dependency
     is a scalar bound on the product factors, followed by a two-sided tail and
     a row-norm lift.
140. Closed the scalar Hoeffding dependency and a weaker coordinate row-norm
     lift.  The Lean wrapper
     `real_rademacher_cosh_factor_le_exp_sq_div_two` reuses mathlib's
     `Real.cosh_le_exp_half_sq`; the repository then proves
     `rademacherTraceProbability_expectationReal_exp_lam_sum_mul_sign_le_exp_lam_sq_sum_sq_div_two`,
     one-sided signed-linear-form tails, and the two-sided tail
     `rademacherTraceProbability_eventProb_abs_sum_mul_sign_le_ge_one_sub_two_mul_exp_sq_bound`.
     Under `HadamardFlat` and `U^TU=I`,
     `signedHadamard_entry_coeff_sum_sq_eq_inv` identifies the coordinate
     variance proxy as `1/m`, and
     `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum_exp_sq_bound`
     proves an all-row high-probability bound via a finite union bound over
     entries.  This is a fully formalized coordinate-Hoeffding route, not
     Tropp's source-sharp SRHT Lemma 3.3.
141. Closed the scoped coordinate-Hoeffding leverage-probability lift.  The
     theorem
     `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_sum_exp_sq_bound`
     combines item 140 with the deterministic signed-orthogonal preservation
     of `HasOrthonormalColumns` and the local equation (6) denominator theorem
     to prove
     \[
       \Pr\{\forall i,\ p_i(HD_\omega U)\le B^2\}
       \ge 1-\sum_{i,j} 2e^{-\lambda B}e^{\lambda^2/(2m)}.
     \]
     The delta-budget wrapper
     `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta`
     packages the same result with a visible failure budget.  This closes a
     weaker scoped uniformization dependency, not Tropp's source-sharp SRHT
     theorem.
142. Closed the next deterministic/probabilistic dependency for the weaker
     coordinate route: uniform row sampling after the preconditioner now has
     local one-step rank-one foundations.  `UniformRowSampling.lean` defines
     `uniformRowOuterGramSample U i = m u_i u_i^T`, proves its quadratic-form
     identity, PSD property, expectation identity `E[m u_i u_i^T]=I` under
     `HasOrthonormalColumns U`, and the bound
     `m u_i u_i^T <= m n B^2 I` from `leverageScoreProb U i <= B^2`.
     `rademacherTraceProbability_eventProb_forall_uniformRowOuterGramSample_signedHadamard_finiteLoewnerLe_ge_one_sub_delta`
     composes item 141 with this Loewner bound.  Item 143 closes the next
     uniform sample-average concentration dependency; this item remains only
     the one-step Loewner foundation.
143. Closed the next concentration dependency for the weaker coordinate route.
     `UniformRowSamplingMGF.lean` defines the iid uniform row product law and
     `uniformRowSampleGram`, rewrites its centered error as an average of
     centered one-step estimators, proves the one-step variance proxy
     `uniformRowOuterGramSample_centered_square_expectationCStarMatrix_le`,
     proves positive and negative trace-MGF bounds
     `uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_centered_le` and
     `uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le`,
     and closes the exact two-sided finite-Loewner concentration theorem
     `uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`.
     This closes the deterministic-after-preconditioning iid uniform
     sample-average concentration row.  Item 144 closes the product-law
     composition with signed-Hadamard preprocessing, and item 145 closes the
     scoped floating-point uniform-sketch arithmetic transfer.
144. Closed the product-law probability composition for the weaker coordinate
     route.  `FiniteProbability.prod` and
     `FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add` provide
     the finite independent-product probability space and dependent-slice
     event combiner.  `UniformRowSamplingComposition.lean` defines the joint
     signed-Hadamard/uniform-row trace law and proves
     `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta`,
     which combines the coordinate-Hoeffding preprocessing failure budget
     `δPre` with the iid uniform row-sampling failure budget `δSample` to get
     the two-sided sample-Gram event with probability at least
     `1 - (δPre + δSample)`.  This closes the exact randomized composition
     for the scoped coordinate-Hoeffding route.  Item 145 closes the
     downstream floating-point uniform-sketch transfer.
145. Closed the floating-point uniform-sketch transfer for the weaker
     coordinate route.  `UniformRowSamplingFP.lean` defines the exact uniform
     sketch with denominator `sqrt(s / m)`, the rounded `fl_div`-based sketch,
     and the fully rounded Gram-dot matrix `fl_uniformRowSampleGramDot`.  It
     proves
     `rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram`, reuses the
     local division and dot-product stability lemmas to prove
     `fl_uniformRowSampleGramDot_perturb_bound`, and composes the exact
     product-law theorem with the generic perturbation transfer
     `finiteLoewnerLe_two_sided_add_of_frobNorm_le` to obtain
     `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
     This closes the scoped coordinate-Hoeffding Algorithm 3 route through FP
     arithmetic, with a sample-dependent explicit FP budget.  Source-sharp
     Tropp constants and any deterministic closed-form upper bound on that
     FP budget remain separate optional refinements.
146. QR/preconditioner proof-source route updated after the no-pivot
     bottleneck.  Cox and Higham, "Stability of Householder QR Factorization
     for Weighted Least Squares Problems" (1997), lines 5--10 of the abstract
     and lines 87--93 explain why ordinary unpivoted Householder QR is not
     row-wise stable for weighted least-squares data; lines 270--284 state
     that column pivoting together with row pivoting or initial row sorting,
     and the correct Householder sign convention, is the stable route.  The
     route starts from their Lemma 2.1 / equation (2.5).  The local theorem
     `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
     and its signed-alpha specialization
     `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`
     now formalize the denominator lower bound
     `2 ||x_tail||_2^2 <= v^T v`.  The follow-up local theorems
     `exists_householderTrailingColumnNorm2Sq_active_max` and
     `abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`
     formalize finite active-column pivot selection and the Cauchy--Schwarz
     comparison `|v^T y_tail| <= ||v||_2 ||x_tail||_2` from the pivot-max
     property.  The scalar endpoint of Cox--Higham Lemma 2.1 is now
     formalized by
     `abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max`,
     and the first row-growth consequence behind equation (4.3) is
     formalized by
     `abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`.
     The row-sorting stage-accumulation dependency is also now formalized by
     `scalar_growth_iterate_bound`,
     `coxHigham_rowSorting_active_entry_bound_of_prior_growth`, and
     `coxHigham_rowSorting_active_entry_bound_of_stage_growth`.  The pivot-row
     norm step in Cox--Higham equations (4.4)--(4.5) is now represented by
     `vecNorm2_le_sqrt_card_mul_of_abs_le`,
     `coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound`, and
     `coxHigham_pivot_row_entry_bound_of_stage_entry_bound`; this closes the
     ambient-`sqrt m` version while leaving the sharper `sqrt (m-k+1)`
     active-tail dimension factor as an optional refinement.  The scalar
     row-wise accumulated perturbation dependency is formalized by
     `scalarAffineGrowthBudget`, `scalar_affine_growth_iterate_bound`,
     `coxHigham_rowwise_error_accumulation_bound`, and
     `coxHigham_rowSorting_active_entry_bound_with_accumulated_error`.  The
     concrete stored rounded panel per-step FP-budget dependency is formalized
     by `fl_householderStoredPanelStep_active_entry_componentwise_error_bound`,
     `coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz`, and
     `coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`.
     The route-shape correction is also formalized by
     `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth` and
     `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth`:
     these use the exact same-reflector row-growth bound for the current stored
     panel directly and add the local compact FP component budget, rather than
     routing through a separate exact-sequence error field.  The non-pivot
     active-row exact bridge is now represented by
     `matMulVec_householder_signed_pivot_update_entry_eq` and
     `coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound`,
     which rewrite the signed Householder matrix-vector update into the
     Cox--Higham scalar row-update estimate before applying the row bound.
     The exact signed pivot-row bridge is also represented by
     `householderBeta_mul_inner_self_eq_two`,
     `abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`,
     `coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2`, and
     `coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound`, which
     turn signed-reflector denominator nonbreakdown into orthogonality, bound
     the pivot coordinate by the active-tail norm, and compose that with the
     ambient row-sorted pivot-row estimate.  The one-step active-row case split
     is represented by
     `coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds`,
     combining the non-pivot and pivot-row branches with the explicit factor
     `max (1 + sqrt 2) (sqrt m)`. The exact multi-stage propagation bridge is
     now represented by `exactSignedPivotHouseholderPanelStep`,
     `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`,
     and
     `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets`,
     which propagate visible stage budgets through a concrete exact signed-pivot
     loop. These are formalized dependencies with two weak-component passes, not
     the final row-wise QR theorem.  The stored-panel FP handoff for the honest
     active-row factor is now represented by
     `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth`,
     with two weak-component passes validating it as a scoped exact-to-FP
     handoff dependency.  The stage-budget handoff needed by the exact sequence
     shape is now represented by
     `coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds`
     and its generic budget-sequence wrappers; two weak-component passes
     validate this as a scoped dependency.  The active-block one-step wrapper
     `coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound`
     has now been added to expose the source sorting invariant in a single
     block-bound form; two weak-component passes validate it as a scoped
     one-step dependency.  The exact sequence wrappers
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets`
     and
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets`
     have also been added to replace separate row/column stage fields by one
     active-block family; two weak-component passes validate these wrappers as
     scoped dependencies.  The exact active-block propagation theorem
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`
     has now been added to derive that active-block family from an initial
     entrywise bound and monotone active windows, keeping the positive-norm and
     pivot-max fields visible; two weak-component passes validate it as a
     scoped exact propagation dependency.  The concrete
     positive-norm field has now been reduced to a source-shaped
     nonzero-active-block witness plus pivot maximality by
     `householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne`
     and the sequence wrapper
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero`.
     Two weak-component passes validate this reduction as a scoped dependency.
     The raw pivot-max inequality is now supplied by the finite active max-pivot
     selector `householderActiveMaxPivotColumn` and the exact sequence wrapper
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot`;
     this replaces the inequality by a source-shaped pivot-policy equation.
     Two weak-component passes validate the finite-selector reduction as a
     scoped dependency. The nonzero-active-block field has now also been
     reduced to the scalar positive active-block mass
     `householderActiveBlockNorm2Sq` by
     `exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos` and the
     sequence wrapper
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos`.
     Two weak-component passes validate this positive-mass-to-nonzero reduction
     as a scoped dependency.
     The concrete column-swap policy is now formalized too:
     `householderSwapColumns_activeMaxPivotColumn_pivot_max` proves that after
     swapping the selected active max column into the displayed active position,
     the displayed column satisfies the pivot-max field, and
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot`
     feeds that post-swap policy into the exact active-block sequence theorem.
     Two weak-component passes validate this swapped-policy bridge as a scoped
     dependency.
     The raw-to-swapped active-block mass bridge is now represented by
     `householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne`,
     `householderActiveBlockNorm2Sq_swapColumns_pos_of_pos`, and
     `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos`;
     this lets the displayed sorted-stage theorem assume positive active-block
     mass on the raw pre-swap stage.  Two weak-component passes validate this
     bridge as a scoped dependency.  The rounded stored active-block budget
     propagation is now represented by `signedPivotHouseholderVector`,
     `signedPivotHouseholderBeta`, and
     `coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds`;
     this theorem threads the Cox--Higham signed-pivot active-block estimate
     through the concrete compact Householder FP budget under visible
     nonbreakdown, pivot-maximality, storage, active-window monotonicity, and
     budget-recurrence fields.  Two weak-component passes validate it as a
     scoped dependency.  The raw-stage positive active-block mass field is now
     connected to local QR rank/determinant nonbreakdown by
     `householderActiveBlockNorm2Sq_pos_of_column_notInPreviousSpan`,
     `householderActiveBlockNorm2Sq_pos_of_leading_witnesses`,
     `householderActiveBlockNorm2Sq_pos_of_leading_block_leftInverses`,
     `householderActiveBlockNorm2Sq_pos_of_leading_block_det_ne_zero`, and
     `householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`.
     Two weak-component passes validate this as a scoped dependency.
     The next local route check rules out a tempting shortcut:
     `not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag`
     proves that upper-triangular nonsingular leading blocks plus positive
     active-block mass do not imply the row-wise off-diagonal domination field
     required by `StoredQRSourceOffDiagonalControl`.  The source route must
     therefore obtain off-diagonal control from a genuine pivoting, ordering,
     or growth invariant, or keep that field visible as a domain hypothesis.
     The concrete pivoted/sorted rounded Householder loop still has to supply
     the determinant/lower-zero and off-diagonal-control fields for its raw
     stages and connect the rounded sequence theorem to the final
     QR/preconditioner solve statement, or keep those source fields explicit
     in a solver-facing theorem.
     Cox--Higham, "Stability of Householder QR Factorization for Weighted
     Least Squares Problems" (1997/1998), Section 1 and Section 2, records the
     route decision used here: ordinary no-pivot Householder QR can be
     unsatisfactory for row-wise weighted least-squares stability, while row
     sorting or row/column pivoting with the standard sign convention is the
     source-backed route; see especially the abstract, the Section 1 discussion
     of row sorting, equations (2.1)--(2.3), Lemma 2.1, and Theorem 2.3 in the
     acquired source.  The row-sorting invariance layer is now formalized
     locally by `rectPermuteRows`, `vecPermute`, `rectLSGram_permuteRows`,
     `rectLSRhs_permuteRows`, and `lsObjective_permuteRows`.  These Lean
     theorems formalize the exact row-permutation/objective bookkeeping only.
     The column-pivoting relabeling layer is now formalized locally by
     `rectMatMulVec_permuteCols`, `rectLSGram_permuteCols`,
     `rectLSRhs_permuteCols`, `RectLSNormalEquations.of_permuteCols`,
     `lsObjective_permuteCols`, and `IsLeastSquaresMinimizer.of_permuteCols`.
     These source-route bookkeeping theorems are formalized locally, but the
     unpivoted source-controlled solve handoff is now formalized locally by
     `storedQRFinalR`, `storedQRFinalTopRhs`, `storedQRBackSubSolution`, and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`.
     The row-wise off-diagonal source-control field is now decomposed locally
     by `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
     and its solver wrapper into the two Cox--Higham-style obligations:
     row-growth upper budgets and diagonal lower bounds.  Two weak-component
     passes validate that local decomposition.  The row-growth propagation
     half is now represented locally by `qrLeadingOffdiagStop`,
     `fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ`, and
     `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`,
     which turn Cox--Higham stage budgets into the displayed upper
     off-diagonal row-budget field; two weak-component passes validate that
     bridge.  The source-control handoff is now formalized by
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`,
     which compose those stage budgets with explicit diagonal lower bounds into
     the local QR solve certificate.  Two weak-component passes validate this
     handoff as a scoped dependency.  The remaining source-route issue is
     proving the concrete stage-budget/pivot-zeroing fields and the visible
     diagonal lower-bound source-control field for a concrete pivoted/sorted
     QR backward-error theorem before the paper-level QR/preconditioner row can
     close.  The displayed off-diagonal row-growth bridge is now specialized to
     the actual signed stored-QR stage family by `storedQRSignedStageVector`,
     `storedQRSignedStageBeta`, and
     `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor`;
     focused build and two weak-component passes validate this specialization.
     The least-squares layer now also has the signed-stage source-control and
     solver handoff theorems
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`;
     focused build and two weak-component passes validate this handoff.  The
     exact pivot-column zeroing field is now formalized by
     `storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos` and
     `storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos`; focused
     build and two weak-component passes validate this field.
     The norm-square-budget adapter
     `storedQRSignedStage_pivot_zeroing_field_of_normSqBudget`, together with
     the least-squares handoffs
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`,
     removes the independent pivot-zeroing hypothesis from the signed-stage
     solver-facing route; focused build and two weak-component passes validate
     this adapter.
     The uniform-stage-budget handoff is now represented by
     `qrLeadingOffdiagStop_le`,
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`,
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`;
     focused build and two weak-component passes validate that monotone stage
     budgets remove the terminal row-budget-domination field.
     The local exact same-reflector row split is now represented by
     `one_le_coxHighamActiveRowGrowthFactor` and
     `storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds`;
     focused build validates the prefix-row zero-prefix identity branch and the
     active-row Cox--Higham branch for one concrete signed stored-QR stage.
     Two weak-component passes now validate this scoped prefix/active
     dependency.
     The least-squares layer now also exposes
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`;
     focused build validates that these wrappers derive the uniform handoff's
     exact-reflector field from concrete stage row/column bounds, pivot
     maximality, and norm-square nonbreakdown.  Two weak-component passes now
     validate this scoped exact-field handoff.
     The local row-budget handoff has also been sharpened by
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`:
     only rows `i.val < k` need the row-budget-to-diagonal comparison in the
     `k`th leading block.  Focused build and two weak-component passes validate
     this statement correction.  It is a local Lean refinement of the
     row-budget handoff; it does not by itself supply the remaining
     Cox--Higham diagonal lower-bound/nonbreakdown proof.
     The stage-budget proof route now propagates this refinement through the
     generic stage-budget, signed-stage, norm-square-derived pivot-zeroing,
     uniform-stage-budget, and stage-entry-bound source-control/solver
     handoffs.  The new `_offdiag_rows` variants keep the source condition
     aligned with the displayed strict upper entries: diagonal lower bounds are
     required only for rows `i.val < k`.  Focused LSQRSolve build passes; two
     weak-component passes now validate this propagated statement correction.
     The active/prefix stage-entry refinement has now been added in the
     least-squares layer:
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`.
     These wrappers match the local proof route from the exact-reflector split:
     active rows and columns are supplied by an active-suffix block invariant,
     while prefix displayed rows remain a separate source-specific row-growth
     target.  Focused LSQRSolve build passes, and two weak-component passes
     now validate this statement-correction dependency.
     The active-suffix block invariant has now been derived from the local
     Cox--Higham active-block recurrence for the signed stored-QR pivot map:
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`.
     This proof-source row now treats the active block as locally sourced from
     the existing Cox--Higham theorem, under visible initial-block,
     active-budget-recurrence, completed-column, pivot-maximality, and
     norm-square nonbreakdown inputs.  Focused LSQRSolve build passes, and two
     weak-component passes now validate this dependency closure.
     The same source route now includes a prefix-row recurrence closure:
     `storedQRSignedStage_active_block_bound_of_signed_stage_budget` exposes
     the active-block recurrence as a named reusable theorem, and
     `storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget`
     proves prefix displayed-row bounds by induction from the active-block
     theorem, the exact same-reflector prefix/active split, and the one-step
     prefix compact-update budget.  The composed source-control and solver
     wrappers with suffix
     `_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows`
     no longer assume a raw prefix-row bound.  Focused LSQRSolve build passes,
     and two weak-component passes now validate this dependency closure.
     The same source route now packages the remaining one-step budget fields
     with a finite global compact-step budget:
     `storedQRSignedStageGlobalCompactBudget` is the finite maximum over matrix
     entries at a stage,
     `storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget` derives
     active and prefix budget fields from the scalar recurrence, and the
     `_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`
     wrappers use the same recurrence for the displayed off-diagonal field.
     Focused LSQRSolve build passes; two weak-component passes now validate
     this source-route dependency closure.
     The same source route now derives completed-column preservation locally:
     `storedQRSignedStage_completed_column_preservation` applies the stored
     prefix-lower-zero invariant and zero-prefix Householder support lemma, and
     the `_activePrefix_activeBlockRecurrence_globalCompactBudget_completedColumns_offdiag_rows`
     wrappers remove the explicit completed-column hypothesis.  Focused build,
     lookup, axiom audit, placeholder scan, PDF compile, text extraction, and
     rendered-page inspection now give two weak-component passes for this
     newest closure.
     The same route now packages per-pivot compact-product smallness with the
     finite maximum `storedQRCompactSequenceProductBudget`; the
     `_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`
     source-control and solver wrappers consume the single scalar condition
     `storedQRCompactSequenceProductBudget < 1`.  Focused build, lookup, axiom
     audit, placeholder scan, PDF compile, text extraction, and rendered-page
     inspection give two weak-component passes for this closure.
     The same route now has the RandNLA equation (8) assembly theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`,
     which composes the active/prefix global-product QR source-control handoff
     into the high-probability rounded sampled-row least-squares objective
     theorem.  This is an assembly closure under visible source/domain fields,
     not a proof that a concrete pivoted/sorted loop supplies local
     nonsingularity, norm-square nonbreakdown, diagonal lower bounds, or global
     compact-product smallness.  Focused build, lookup, axiom audit, marker
     scan, PDF compile, text extraction, and rendered-page inspection give two
     clean weak-component passes for the assembly theorem.
     The finite global-product bookkeeping has also been closed in the reverse
     direction by
     `storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt` and
     `storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product`.
     These use the finite strict-supremum lemma to show that proving every
     per-pivot product expression below `1` is enough to prove
     `storedQRCompactSequenceProductBudget < 1`.  This reduces the remaining
     product-smallness route to the source-faithful per-pivot inequalities;
     it does not close those inequalities from conditioning, pivoting, or
     machine-precision assumptions.  Two weak-component passes are clean.
     The active/prefix route now reuses the earlier leading-block inverse
     proof source for nonbreakdown:
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
     packages the local `κ∞`/self-norm and dual compact-budget route as a
     reusable norm-square-margin theorem, and the
     `kappaInf_dualBudget` source-control/solver/equation (8) wrappers compose
     it into the global-product branch.  This is a local-library reuse closure,
     not a new external proof source.  It leaves the concrete-loop proof of the
     local determinant, `κ∞`/dual-budget, diagonal lower-bound, and product
     smallness fields open.  Focused build, lookup, marker scan, qualified
     axiom audit, PDF compile, text extraction, and rendered-page inspection
     now give two weak-component passes for this reuse closure.

124. Added a diagonal-dominant global-product reuse branch for equation (8).
     No new external proof source is used.  The branch reuses the repository's
     local `IsDiagDominantUpper` infrastructure, the finite global-product
     budget, and
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`.
     The resulting source-control, solver, and RandNLA objective theorems are
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_globalProduct`,
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`.
     This closes the offdiag-row diagonal lower-bound field only under explicit
     local diagonal-dominance assumptions; it leaves the source-level proof of
     diagonal dominance, determinant/conditioning budgets, and product
     smallness from a concrete QR loop open.  Focused build, lookup, marker
     scan, qualified axiom audit, PDF compile, text extraction, and rendered
     page inspection now give two weak-component passes for this reuse branch.

125. Added the scalar global-bound product-smallness adapter
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`.
     No external source is used.  It is finite-order and monotonicity
     bookkeeping over the existing product expression: local diagonal
     dominance supplies positivity of the diagonal-dominant inverse-budget
     factor, `storedQRCompactSequenceRelativeBudget_nonneg` supplies
     nonnegativity of the compact sequence factor, and `vecNorm2_nonneg`
     supplies nonnegativity of the displayed column norm.  It reduces the
     product-smallness dependency to proving global factor/norm bounds and one
     scalar inequality from a concrete loop.  Focused build, lookup, marker
     scan, qualified axiom audit, PDF compile, text extraction, and rendered
     page inspection now give two weak-component passes for this local-library
     reuse closure.

126. Added the canonical finite-max product-smallness adapter
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`
     and the supporting finite maximum budgets
     `storedQRDiagDominantInvFactorBudget` and
     `storedQRPivotColumnNormBudget`.  No external source is used.  This is
     finite-order maximum bookkeeping using `Finset.sup'`: each displayed
     factor or norm is below its finite maximum, and the maxima are
     nonnegative under local diagonal dominance and vector-norm
     nonnegativity.  Focused build, lookup, marker scan, qualified axiom audit,
     PDF compile, text extraction, and rendered page inspection now give two
     weak-component passes for this local-library reuse closure.

127. Threaded the canonical finite-max product-smallness condition through the
     diagonal-dominant equation (8) QR handoff.  No external source is used.
     The new source-control and solver theorems reuse item 126 and the local
     diagonal-dominant/`κ∞`/dual-budget infrastructure, ending in
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`.
     This is a local theorem-surface narrowing: it replaces the raw
     `storedQRCompactSequenceProductBudget < 1` field by the scalar inequality
     for `storedQRDiagDominantInvFactorBudget` and
     `storedQRPivotColumnNormBudget`.  It does not prove local diagonal
     dominance, determinant/conditioning budgets, dual compact-budget fields,
     or that scalar inequality from a concrete QR loop.  Focused build,
     executable lookup, marker scan, qualified axiom audit, PDF compile, text
     extraction, and rendered page inspection now give two weak-component
     passes for this local theorem-surface narrowing.

128. Added the concrete-dual finite-max diagonal-dominant equation (8) handoff.
     No external source is used.  The solver wrapper reuses the previously
     formalized concrete diagonal-dominant product-sequence certificate
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`
     together with the finite-max product-smallness theorem from item 126.
     The resulting theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`
     removes the auxiliary `κ`, `K`, and dual compact-budget fields from the
     finite-max diagonal-dominant branch.  The RandNLA equation (8) objective
     theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver`
     consumes this solver certificate samplewise.  This is a local
     theorem-surface narrowing only: local diagonal dominance, local
     leading-block determinant nonzeroness, and the finite-max scalar
     smallness inequality remain visible.  First weak-component validation is
     clean: focused build, executable lookup, marker scan, qualified axiom
     audit, PDF compile, text extraction, and rendered-page inspection all
     passed, and the axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  The repeated pass is also clean,
     and the temporary axiom-audit file was deleted.  This checkpoint now has
     two consecutive clean passes.

129. Added the determinant-free concrete-dual finite-max diagonal-dominant
     equation (8) handoff.  No external source is used.  The new foundational
     bridge `det_ne_zero_of_diagDominantUpper` reuses the local triangular
     determinant theorem `det_ne_zero_of_upper_triangular_diag_ne_zero` and the
     fact that `IsDiagDominantUpper` already contains upper-triangular shape
     and nonzero diagonal entries.  The solver theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual`
     calls item 128 after deriving all local determinant hypotheses from
     diagonal dominance, and the RandNLA objective theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant`
     consumes that solver certificate samplewise.  This is a local
     theorem-surface narrowing only: local diagonal dominance and the
     finite-max scalar smallness inequality remain visible.  Two
     weak-component passes for this exact surface are clean: focused build,
     executable lookup, marker scan, qualified axiom audit, PDF compile, text
     extraction, and rendered-page inspection all passed twice.  The repeated
     axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`, and the temporary axiom-audit file was deleted.

130. Added the direct packaged off-diagonal-control RandNLA equation (8)
     wrapper.  No external source is used.  This is a local-library
     composition step: the theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`
     feeds samplewise `StoredQROffDiagonalControlInvariant` into the local
     stored-QR backward-error theorem and then into the already formalized
     high-probability finite-Loewner sampled-row objective theorem.  The
     existing source-shaped objective theorem now derives the packaged
     invariant via `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl`
     and reuses the direct wrapper.  Two weak-component passes are clean:
     focused build, executable lookup, marker scan, qualified axiom audit, PDF
     compile, text extraction, and rendered-page inspection all passed twice.
     The repeated axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  This closes the solver-to-RandNLA
     handoff for the packaged off-diagonal-control invariant; it does not prove
     that a concrete arbitrary no-pivot stored QR loop satisfies that
     invariant.

131. Added the finite-max diagonal-dominant constructor for the packaged
     off-diagonal-control invariant.  No external source is used.  This is a
     local-library composition step: the theorem
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
     combines `det_ne_zero_of_diagDominantUpper` with
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`.
     It turns local `IsDiagDominantUpper` leading blocks plus the canonical
     scalar finite-max smallness inequality into the packaged invariant needed
     by the route-1 QR and RandNLA wrappers.  First weak-component validation
     is clean: focused build, executable lookup, marker scan, qualified axiom
     audit, PDF compile, text extraction, and rendered-page inspection all
     passed, and the axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  The theorem does not prove
     diagonal dominance or scalar smallness from a concrete stored QR loop.
     The repeated validation pass is also clean: focused build, executable
     lookup, marker scan, qualified axiom audit, PDF compile, text extraction,
     and rendered-page inspection passed again.  This checkpoint now has two
     consecutive clean passes.

132. Added the row-budget diagonal-lower-bound route elimination.  No external
     source is used.  This is a local counterexample theorem in
     `LSQRSolve.lean`: the theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag`
     uses the same `[[1,2],[0,1]]` witness as the off-diagonal-control
     obstruction and chooses row budget `2`.  The strict upper entry satisfies
     the budget, but the first displayed diagonal has magnitude `1`, so the
     diagonal lower-bound field would require `2 <= 1`.  Two weak-component
     passes are clean: focused LSQRSolve build, executable lookup, `git
     diff --check`, touched Lean marker scan, qualified axiom audit, PDF
     compile, text extraction, and rendered-page inspection all passed twice.
     The axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  This eliminates a false shortcut in the Cox--Higham
     row-budget route; it does not prove the positive diagonal
     lower-bound/nonbreakdown invariant.

133. Added the packaged row-budget control certificate.  No external source is
     used; this is a theorem-statement correction in `LSQRSolve.lean`.  The
     structure `StoredQRDisplayedRowBudgetControl` names exactly the residual
     Cox--Higham row-budget fields: displayed strict upper entries are bounded
     by a row budget, and that row budget is no larger than the displayed
     diagonal on rows `i.val < k`.  The source-control and solver wrappers
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
     consume this package.  Two weak-component validations are clean: focused
     build, executable lookup, `git diff --check`, touched Lean marker scan,
     qualified axiom audit, PDF compile, text extraction, and rendered-page
     inspection all passed twice; the temporary audit file was deleted after
     validation.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  This does not prove a diagonal
     lower-bound/nonbreakdown invariant; it keeps that domain field visible.

134. Added the equation (8) probability-level handoff for the packaged
     row-budget control route.  No external source is used; this is a local
     composition theorem in `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`
     derives `StoredQRSourceOffDiagonalControl` from samplewise
     `StoredQRDisplayedRowBudgetControl`, then reuses the existing rounded
     sampled-row objective theorem.  It is a scoped closure under visible
     determinant, norm-square nonbreakdown, compact-product, and row-budget
     control assumptions; it does not prove those fields from a concrete
     pivoted/sorted loop.  First weak-component validation is clean: focused
     build, executable lookup, `git diff --check`, touched Lean marker scan,
     qualified axiom audit, PDF compile, text extraction, and rendered-page
     inspection all passed.  The repeated pass is also clean, with the same
     standard axiom audit result; the temporary audit file was deleted after
     validation.

135. Added the `κ∞`/dual-budget equation (8) probability-level handoff for the
     packaged row-budget route.  No external source is used; this is a local
     composition theorem in `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`
     reuses the existing QR adapter
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
     to derive the norm-square nonbreakdown margin, then calls the
     probability-level row-budget-control theorem.  First weak-component
     validation is clean: focused build, executable lookup, `git diff --check`,
     touched Lean marker scan, qualified axiom audit, PDF compile, text
     extraction, and rendered-page inspection all passed.  The axiom audit
     reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
     The repeated pass is also clean with the same standard axiom audit result.
     This records a dependency reduction, not a source proof of
     `StoredQRDisplayedRowBudgetControl`, local determinant/conditioning
     budgets, or compact-product smallness.

136. Added the signed-stage constructor for the packaged row-budget control
     certificate.  No external source is used; this is a local composition
     theorem in `LSQRSolve.lean`.  The theorem
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget`
     reuses the existing Cox--Higham signed-stage row-growth theorem and the
     norm-square pivot-zeroing theorem to produce
     `StoredQRDisplayedRowBudgetControl` from signed-stage entry budgets plus
     the visible offdiag-row diagonal lower-bound field.  First weak-component
     validation is clean: focused build, executable lookup, `git diff --check`,
     touched Lean marker scan, qualified axiom audit, PDF compile, text
     extraction, and rendered-page inspection all passed.  The axiom audit
     reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
     The repeated pass is also clean with the same standard axiom audit result:
     focused build, executable lookup, marker scan, PDF compile, text extraction,
     and rendered pages 174--175 passed again.  This is a dependency closure for
     certificate packaging, not a proof of the diagonal lower-bound/nonbreakdown
     invariant.

137. Added the uniform-stage-budget constructor for the packaged row-budget
     control certificate.  No external source is used; this is a local
     stop-time/monotonicity adapter in `LSQRSolve.lean`.  The theorem
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget`
     specializes the signed-stage package to the single row budget
     `rowBudget k i = stageBudget k`, using `qrLeadingOffdiagStop_le` and
     monotonicity of `stageBudget` to supply terminal row-budget domination.
     First weak-component validation is clean: focused build, executable
     lookup, `git diff --check`, touched Lean marker scan, qualified axiom
     audit, PDF compile, text extraction, and rendered-page inspection all
     passed.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  This is a dependency closure for
     the stage-budget packaging route, not a proof of the diagonal
     lower-bound/nonbreakdown invariant or the concrete stage recurrence.  The
     repeated weak-component pass is also clean with the same standard axiom
     audit result: focused build, executable lookup, marker scan, PDF compile,
     text extraction, and rendered pages 174--175 passed again.

138. Added the global compact-step and `κ∞`/dual-budget constructors for the
     packaged row-budget control certificate.  No external source is used; this
     is a local composition theorem in `LSQRSolve.lean`.  The theorem
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_of_normSqBudget`
     combines the uniform-stage package with completed-column preservation,
     active-block recurrence, prefix-row recurrence, pivot maximality, and the
     finite global compact-step recurrence to produce the displayed row-budget
     certificate under a norm-square nonbreakdown budget.  The theorem
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_kappaInf_dualBudget`
     first reuses
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
     to derive that norm-square budget from leading-block determinant,
     `κ∞`/self-norm, and dual compact-budget fields.  First weak-component
     validation is clean: `git diff --check`, touched Lean marker scan,
     focused LSQRSolve build, executable lookup, qualified axiom audit, PDF
     compile, PDF text extraction, and rendered-page inspection passed.  The
     axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  This is a dependency closure for the selected
     `κ∞`/dual-budget route, not a proof of the offdiag-row diagonal
     lower-bound/nonbreakdown invariant or the concrete determinant/conditioning
     fields.  The repeated weak-component pass is also clean with the same
     standard axiom audit result: whitespace, marker, focused build, lookup,
     PDF compile/text, and rendered page 175 passed again.

139. Added the canonical finite row-max bridge from source-shaped off-diagonal
     control to the packaged row-budget certificate.  No external source is
     used; this is a local finite-maximum theorem in `LSQRSolve.lean`.  The
     definition `qrLeadingStrictUpperRowMaxBudget` takes, for each displayed
     row `i < k`, the finite maximum of the strict-upper absolute entries in
     that row.  The lemmas `qrLeadingStrictUpperRowMaxBudget_entry_le` and
     `qrLeadingStrictUpperRowMaxBudget_le_diag_of_offdiag` prove the two scalar
     sides, and
     `StoredQRDisplayedRowBudgetControl.of_sourceOffDiagonalControl_rowMaxBudget`
     packages any existing `StoredQRSourceOffDiagonalControl` field as
     `StoredQRDisplayedRowBudgetControl`.  First weak-component validation is
     clean: `git diff --check`, touched Lean marker scan, focused LSQRSolve
     build, executable lookup, qualified axiom audit, PDF compile, PDF text
     extraction, and rendered-page inspection passed.  The axiom audit reports
     only standard `propext`, `Classical.choice`, and `Quot.sound`.  This is a
     safe-direction bridge only; it is not a proof that the source off-diagonal
     domination field follows from ordinary no-pivot QR or from row-growth
     estimates.  The repeated weak-component pass is also clean: whitespace,
     marker scan, focused LSQRSolve build, executable lookup, qualified axiom
     audit, PDF compile/text extraction, and rendered page 175 all passed again
     with the same standard axiom audit result.

140. Added the direct finite-max diagonal-dominant RandNLA equation (8)
     wrapper for the packaged off-diagonal-control route.  No external source
     is used; this is a local composition theorem in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`
     first applies
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
     to the samplewise local diagonal-dominance and canonical scalar
     finite-max smallness hypotheses, then calls the direct packaged
     high-probability objective theorem.  This removes the packaged-invariant
     hypothesis on the diagonal-dominant finite-max probability surface, but it
     is not a proof of diagonal dominance or scalar smallness for a concrete
     no-pivot stored QR loop.  First weak-component validation is clean:
     focused RandNLA least-squares build, executable lookup, `git diff
     --check`, touched Lean marker scan, qualified axiom audit, PDF compile,
     text extraction, and rendered-page inspection all passed.  The axiom audit
     reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
     The repeated weak-component pass is also clean with the same standard
     axiom audit result: focused build, executable lookup, marker scan, PDF
     compile/text extraction, and rendered pages 115 and 186 passed again.
     This checkpoint now has two consecutive clean passes.

141. Added the stronger exact-no-pivot route-elimination theorem for the
     finite-max diagonal-dominant route.  No external source is used; this is a
     local counterexample theorem in `LSQRSolve.lean`, reusing the existing
     exact two-step Householder witness.  The theorem
     `not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property`
     states that no universal exact-recurrence proof can derive
     `IsDiagDominantUpper` together with an arbitrary final-block property
     `P`.  This directly covers the attempted route "diagonal dominance plus
     scalar finite-max smallness follows from the standard no-pivot recurrence":
     the first conjunct already fails for the local witness.  Focused
     LSQRSolve build passed; first weak-component validation is clean
     (`git diff --check`, marker scan, focused build, executable lookup,
     qualified axiom audit with only standard axioms, PDF compile/text
     extraction, and rendered page 168).  Repeated validation is also clean
     with the same standard axiom audit result, executable lookup exposure,
     PDF text extraction, and readable rendered page 168.  The theorem is now
     closed as a route-elimination dependency, not as a positive proof of a
     concrete-loop off-diagonal-control invariant.

142. Added the active-max-pivot packaged row-budget constructors.  No new
     external source is used in this step; this is a local composition of the
     already formalized finite active max-pivot selector route with the
     packaged global compact-step row-budget constructors in `LSQRSolve.lean`.
     The theorems
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget`
     and
     `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget`
     replace the raw pivot-max inequality in the row-budget constructor surface
     by the source-shaped policy equation that the displayed pivot column is
     `householderActiveMaxPivotColumn` for the current active block.  The raw
     inequality is recovered internally with
     `householderActiveMaxPivotColumn_pivot_max`.  Focused LSQRSolve build
     passed.  First weak-component validation is clean: `git diff --check`,
     touched Lean marker scan, focused LSQRSolve build, executable lookup,
     qualified axiom audit with only standard axioms, PDF compile/text
     extraction, and rendered pages 175--176 passed.  Repeated validation is
     also clean with the same standard axiom audit result, executable lookup
     exposure, PDF text extraction, and readable rendered pages 175--176.  This
     entry now has two consecutive clean passes.  It closes only the pivot-max
     field for this packaged certificate route; the diagonal
     lower-bound/nonbreakdown field, determinant/conditioning budgets,
     compact-product smallness, and final QR/preconditioner assembly remain
     open or visible assumptions.

143. Added the probability-level active-max-pivot equation (8) wrapper for the
     active/prefix global-product route.  No new external source is used in this
     step; this is a local composition of the finite active max-pivot selector
     theorem `householderActiveMaxPivotColumn_pivot_max` with the already
     formalized active/prefix global-product `κ∞` RandNLA theorem in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
     replaces the raw samplewise pivot-maximality hypothesis by the policy
     equation choosing `householderActiveMaxPivotColumn` as the displayed pivot
     column, and then applies the existing probability-level equation (8)
     wrapper.  First weak-component validation is clean: `git diff --check`,
     touched Lean marker scan, focused RandNLA least-squares build, executable
     lookup, qualified axiom audit with only standard axioms, PDF compile/text
     extraction, and rendered page 185 passed.  Repeated validation is also
     clean with the same standard axiom audit result, executable lookup
     exposure, PDF text extraction, and readable rendered page 185.  This entry
     now has two consecutive clean passes.  It closes only the raw pivot-max
     field on this probability theorem surface; diagonal lower bounds,
     determinant/conditioning budgets, compact-product smallness, and the final
     generic QR/preconditioner theorem remain open or visible assumptions.

144. Added the probability-level active-max-pivot row-budget global-product
     wrapper.  No new external source is used in this step; this is a local
     composition of the active-max-pivot packaged row-budget constructor in
     `LSQRSolve.lean` with the finite global-product row-budget equation (8)
     theorem in `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
     constructs the samplewise `StoredQRDisplayedRowBudgetControl` certificate
     from the finite active max-pivot policy, local `κ∞`/dual compact-budget
     data, and the global compact-step recurrence, then applies the existing
     probability theorem.  Two weak-component validation passes are clean:
     focused build, executable lookup, qualified axiom audit, PDF compile/text
     extraction, and rendered-page inspection passed twice; the axiom audit
     reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
     This closes only a packaging/assembly edge; diagonal lower bounds,
     determinant/conditioning budgets, compact-product smallness, and the final
     generic QR/preconditioner theorem remain open or visible assumptions.

145. Added the active-max-pivot row-budget diagonal route-elimination theorem.
     No new external source is used in this step; this is a local
     counterexample theorem in `LSQRSolve.lean`.  The definitions
     `activeMaxPivotRowBudgetDiagCounterexampleA0` and
     `activeMaxPivotRowBudgetDiagCounterexampleSeq` build a two-stage witness:
     the first displayed stage satisfies the active max-pivot policy, and the
     second displayed stage has the same `[[1,2],[0,1]]` row-budget diagonal
     failure as the earlier route-elimination theorem.  The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag`
     rules out deriving the row-budget diagonal lower-bound field from
     upper-triangular nonsingular leading blocks, positive active-block mass,
     active max-pivot selection, and strict-upper row-growth budgets alone.
     First weak-component validation is clean: `git diff --check`, touched
     Lean marker scan, focused LSQRSolve build, executable lookup, qualified
     axiom audit, PDF compile/text extraction, and rendered page 169 passed;
     the axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  The repeated weak-component pass is also clean with the
     same standard axiom audit result, executable lookup exposure, PDF
     compile/text extraction, and readable rendered page 169.  This entry now
     has two consecutive clean passes.  This is route elimination, not a
     positive diagonal lower-bound theorem; the final QR/preconditioner row
     still needs a genuine diagonal lower-bound invariant or visible scoped
     assumptions.

146. Added the active-block-budget strengthening of the active-max-pivot
     row-budget diagonal route-elimination theorem.  No new external source is
     used in this step; it is a local finite counterexample theorem in
     `LSQRSolve.lean`.  The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag`
     uses the same two-stage witness as entry 145, but additionally assumes
     the nonnegative row budget bounds every active trailing-block entry at
     each displayed stage.  The witness satisfies that active-block magnitude
     condition with budget `2`, while the second displayed block still has the
     strict upper entry `2` over a diagonal magnitude `1`.  This rules out
     using active-block magnitude control, active max-pivot selection, and
     strict-upper row-growth budgets as a hidden proof of the diagonal
     lower-bound/nonbreakdown field.  Two weak-component validation passes are
     clean: repeated `git diff --check`, touched Lean marker scan, focused
     `LSQRSolve` build, executable lookup, qualified axiom audit, PDF
     compile/text extraction, and rendered-page inspection passed.  The axiom
     audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  Repeated validation is also clean with the same focused
     build, executable lookup, whitespace check, touched-source marker scan,
     qualified axiom audit, PDF compile/text extraction, and rendered-page
     inspection.  This dependency now has two consecutive clean passes.

147. Added the meta-property strengthening of the active-block-budget
     row-budget diagonal route-elimination theorem.  No new external source is
     used; this is a local Lean wrapper around the entry 146 counterexample.
     The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag`
     adds an arbitrary auxiliary property `P A_hat rowBudget` to the attempted
     universal implication, then refutes it by choosing `P := fun _ _ => True`
     and applying the already formalized active-block-budget route elimination.
     This records that scalar/product side conditions unrelated to the actual
     diagonal lower-bound invariant cannot be used as hidden proof material.
     Two weak-component validation passes are clean: repeated `git diff
     --check`, touched Lean marker scan, focused `LSQRSolve` build, executable
     lookup, qualified axiom audit, PDF compile/text extraction, and
     rendered-page inspection passed.  The axiom audit reports only standard
     `propext`, `Classical.choice`, and `Quot.sound`.

148. Added the solver-facing active-max-pivot wrapper for the active/prefix
     global-product `κ∞` route.  No new external source is used; this is a
     local composition in `LSQRSolve.lean`.  The theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows`
     derives the raw pivot-maximality inequality from the finite active
     selector with `householderActiveMaxPivotColumn_pivot_max`, then applies
     the already formalized raw-pivot solver certificate.  This closes the
     solver-layer pivot-policy dependency for the selected route only:
     diagonal lower bounds/nonbreakdown, local determinant/conditioning data,
     dual compact-budget assumptions, compact-product smallness, and the final
     generic QR/preconditioner theorem remain open or visible assumptions.
     Two weak-component validation passes are clean: repeated `git diff
     --check`, touched source Lean marker scan, focused `LSQRSolve` build,
     executable lookup, qualified axiom audit, PDF compile/text extraction,
     and rendered-page inspection passed.  The axiom audit reports only
     standard `propext`, `Classical.choice`, and `Quot.sound`.

149. Added the solver-facing row-budget-control finite-global-product wrappers
     for the equation (8) rectangular QR/preconditioner route.  No new external
     source is used; this is a local-library reuse step in `LSQRSolve.lean`.
     The base theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
     composes the existing row-budget-control source certificate
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
     with the local `LSQRSolveBackwardError` handoff.  The sibling theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_rowBudgetControl_globalProduct`
     first derives the raw norm-square nonbreakdown field with
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`.
     This closes the local solver-layer per-pivot compact-product family for
     the packaged row-budget route, replacing it by the visible scalar
     condition `storedQRCompactSequenceProductBudget < 1`.  It does not prove
     `StoredQRDisplayedRowBudgetControl`, local determinant/conditioning data,
     dual compact-budget assumptions, compact-product smallness, or the final
     generic QR/preconditioner theorem.  Two weak-component validation passes
     are clean: repeated `git diff --check`, touched source Lean marker scan,
     focused LSQRSolve build, executable lookup, qualified axiom audit, PDF
     compile/text extraction, and rendered-page inspection passed.  The axiom
     audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.

150. Added the route-1 row-max contraction handoff for the rectangular
     QR/preconditioner bottleneck.  No new external source is used; this is a
     local-library reuse and theorem-shape step in `LSQRSolve.lean`.  The
     theorem `StoredQRDisplayedRowBudgetControl.of_rowMaxBudget_le_diag_factor`
     shows that a scalar contraction invariant
     `qrLeadingStrictUpperRowMaxBudget <= ρ * |diag|`, with `ρ <= 1`, supplies
     the packaged row-budget certificate.  The companion
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
     combines that certificate with the stored recurrence, local determinant,
     norm-square nonbreakdown, and scalar finite global compact-product fields.
     The solver-level wrapper
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
     exposes the same contraction invariant directly on the local QR solve
     surface.  This closes the row-budget-certificate construction under the
     route-1 invariant shape; it does not prove the contraction invariant,
     determinant facts, norm-square margin, global product smallness, or the
     final generic QR/preconditioner theorem from ordinary no-pivot QR.  Two
     weak-component validation passes are clean: repeated `git diff --check`,
     touched source Lean marker scan, focused LSQRSolve build, executable
     lookup, qualified axiom audit, PDF compile/text extraction, and rendered
     page inspection passed.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.

151. Added the scalar row-max/diagonal defect handoff for the rectangular
     QR/preconditioner bottleneck.  No new external source is used; this is a
     local finite-maximum packaging step in `LSQRSolve.lean`.  The definition
     `storedQRRowMaxDiagDefectBudget` takes the finite maximum, over displayed
     rows `i < k`, of the canonical strict-upper row maximum minus the
     corresponding displayed diagonal magnitude.  The theorem
     `StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos`
     proves that the scalar condition
     `storedQRRowMaxDiagDefectBudget hmn A_hat <= 0` supplies the packaged
     row-budget certificate.  The source-control theorem
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`
     and solver-level wrapper
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`
     expose that scalar defect condition directly on the equation (8)
     route-1 surface.  This is a scalar packaging of the row-max contraction
     dependency; it does not prove the defect is nonpositive from ordinary
     no-pivot QR, nor determinant facts, norm-square nonbreakdown, product
     smallness, or the final generic QR/preconditioner theorem.  Two
     weak-component validation passes are clean: repeated `git diff --check`,
     touched source Lean marker scan, focused LSQRSolve build, executable
     lookup, qualified axiom audit, PDF compile/text extraction, and rendered
     pages 176--178 passed.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.

152. Added the exact-no-pivot scalar-defect route elimination for the
     rectangular QR/preconditioner bottleneck.  No new external source is used;
     this is a local counterexample reuse step in `LSQRSolve.lean`.  The
     theorem
     `exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos`
     proves that the existing exact two-stage no-pivot Householder QR witness
     has positive `storedQRRowMaxDiagDefectBudget`.  The universal theorem
     `not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos`
     then rules out deriving the nonpositive scalar defect condition from only
     the exact trailing recurrence, valid signed squared-norm identities, and
     nonzero Householder denominators.  This is a route-elimination result: it
     shows that the scalar defect condition must come from a stronger
     computed-loop/off-diagonal-control invariant, pivoted/sorted route, or an
     explicit visible assumption.  It does not prove the positive invariant,
     determinant/conditioning fields, norm-square nonbreakdown, scalar
     product smallness, or the final generic QR/preconditioner theorem.  First
     weak-component validation is clean: `git diff --check`, touched source
     Lean marker scan, focused `LSQRSolve` build, executable lookup,
     qualified axiom audit, PDF compile/text extraction, and rendered-page
     inspection of pages 177--179 passed.  The axiom audit reports only
     standard `propext`, `Classical.choice`, and `Quot.sound`.  Repeated
     validation is also clean with the same standard axiom audit result,
     executable lookup exposure, PDF text extraction, and readable rendered
     pages 177--179.  This route-elimination dependency now has two
     consecutive clean passes.

153. Added the probability-level scalar row-max-defect global-product wrapper
     for the equation (8) rectangular QR/preconditioner route.  No new
     external source is used; this is a local assembly step in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver`
     builds the samplewise `StoredQRDisplayedRowBudgetControl` certificate
     from `storedQRRowMaxDiagDefectBudget <= 0`, derives the per-pivot
     compact-product family from `storedQRCompactSequenceProductBudget < 1`,
     and reuses the already formalized row-budget-control high-probability
     sampled-row objective theorem.  This closes only the probability-level
     assembly edge for the scalar-defect route; it does not prove the scalar
     defect condition, determinant facts, norm-square nonbreakdown, scalar
     product smallness, or the final generic QR/preconditioner theorem from a
     concrete loop.  First weak-component validation is clean: `git diff
     --check`, touched source Lean marker scan, focused `LeastSquaresSketch`
     build, executable lookup, qualified axiom audit, PDF compile/text
     extraction, and rendered-page inspection of pages 114--118 passed.  The
     axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  Repeated validation is also clean with the same standard
     axiom audit result, executable lookup exposure, PDF text extraction, and
     readable rendered pages 114--118.  This dependency now has two
     consecutive clean passes.

154. Added the probability-level primitive norm-square/off-diagonal-product
     wrapper for the equation (8) rectangular QR/preconditioner route.  No new
     external source is used; this is a local assembly step in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver`
     constructs `StoredQRSourceOffDiagonalControl` samplewise from leading-block
     determinant nonzeroness, the dimensioned norm-square nonbreakdown margin,
     row-wise off-diagonal domination, and per-pivot compact-product smallness,
     then reuses the already formalized source-shaped high-probability
     sampled-row objective theorem.  This closes only the probability-level
     assembly edge for those visible primitive route fields; it does not prove
     determinant/nonbreakdown, off-diagonal domination, product smallness, or
     the final generic QR/preconditioner theorem from a concrete loop.  First
     weak-component validation is clean: `git diff --check`, touched source
     Lean marker scan, focused `LeastSquaresSketch` build, executable lookup,
     qualified axiom audit, PDF compile/text extraction, and rendered-page
     inspection of pages 114--119 passed.  The axiom audit reports only
     standard `propext`, `Classical.choice`, and `Quot.sound`.  Repeated
     validation is also clean with the same standard axiom audit result,
     executable lookup exposure, PDF text extraction, and readable rendered
     pages 114--119.  This dependency now has two consecutive clean passes.

155. Added the diagonal-dominance to scalar row-max-defect bridge for the
     equation (8) rectangular QR/preconditioner route.  No new external source
     is used; this is a local finite-maximum consequence of the repository
     definition `IsDiagDominantUpper`.  The theorem
     `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant` proves that local
     diagonal dominance of all displayed leading blocks implies
     `storedQRRowMaxDiagDefectBudget <= 0`, and
     `StoredQRDisplayedRowBudgetControl.of_diagDominant` converts that scalar
     fact into the packaged row-budget certificate.  This closes only the
     bridge between two visible route surfaces; it does not prove diagonal
     dominance for a concrete no-pivot QR loop.  First weak-component
     validation is clean: `git diff --check`, touched source Lean marker scan,
     focused `LSQRSolve` build, executable lookup, qualified axiom audit, PDF
     compile/text extraction, and rendered-page inspection of pages 177--179
     passed.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  Repeated validation is also clean
     with the same standard axiom audit result, executable lookup exposure, PDF
     text extraction, and readable rendered pages 177--179.  This dependency
     now has two consecutive clean passes.

156. Added the exact/zero-compact compact-product endpoint for the equation
     (8) rectangular QR/preconditioner route.  No new external source is used;
     this is a local algebraic consequence of the repository definitions
     `storedQRCompactSequenceRelativeBudget`,
     `storedQRCompactSequenceProductExpr`, and
     `storedQRCompactSequenceProductBudget`.  The theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero`
     proves that if the stored compact sequence relative budget is exactly
     zero, then every per-pivot compact-product expression is zero and the
     finite global compact-product budget is strictly below one.  This closes
     only the exact/zero-compact endpoint of the product-smallness dependency.
     It does not prove positive floating-point compact-product smallness when
     the relative budget is positive, and it does not close the final generic
     QR/preconditioner theorem.  Two weak-component validation passes are
     clean: `git diff --check`, touched Lean marker scan, focused LSQRSolve
     build, executable lookup, qualified axiom audit, theorem PDF compile,
     targeted text extraction, and rendered-page inspection of the
     compact-product section passed.  The axiom audit reports only standard
     `propext`, `Classical.choice`, and `Quot.sound`.

157. Added the positive relative-budget cap theorem for the equation (8)
     rectangular QR/preconditioner route.  No new external source is used; this
     is a local monotonicity consequence of the repository's finite-max
     compact-product definitions and nonnegativity lemmas.  The theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le`
     proves that, under local diagonal dominance, a nonnegative cap
     `cmax` with
     `storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha <= cmax`
     lets the canonical scalar smallness inequality be checked with `cmax`
     instead of the exact stored compact relative budget.  This reduces the
     positive-budget compact-product dependency to a source-facing cap plus a
     scalar inequality; it does not prove either of those two facts from the
     concrete QR loop and does not close the final generic QR/preconditioner
     theorem.  First weak-component validation is clean: focused LSQRSolve
     build, executable lookup, whitespace check, touched Lean marker scan,
     qualified axiom audit, theorem PDF compile, targeted text extraction, and
     rendered-page inspection of the compact-product section passed.  The axiom
     audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.

158. Added the uniform per-step compact-panel cap reduction for the equation
     (8) rectangular QR/preconditioner route.  No new external source is used;
     this is a local finite-sum consequence of the repository definitions
     `storedQRCompactStepRelativeBudget` and
     `storedQRCompactSequenceRelativeBudget`, followed by the positive
     relative-budget cap theorem from item 157.  The QR theorem
     `storedQRCompactSequenceRelativeBudget_le_mul_of_step_le` proves that a
     uniform per-step cap `cStep` bounds the sequence budget by `n * cStep`.
     The least-squares theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`
     feeds this cap into the canonical finite-max compact-product smallness
     theorem.  This reduces the route to proving the one-step cap and scalar
     inequality; it does not prove either from a concrete computed loop.
     Two weak-component validation passes are clean: focused LSQRSolve build,
     executable lookup, whitespace check, touched Lean marker scan, qualified
     axiom audit, theorem PDF compile, targeted text extraction, and
     rendered-page inspection of pages 187--188 passed.  The axiom audit
     reports only standard `propext`, `Classical.choice`, and `Quot.sound`.

159. Added the vector-level compact column/RHS cap reduction for the equation
     (8) rectangular QR/preconditioner route.  No new external source is used;
     this is local finite-sum bookkeeping over the repository definition
     `householderCompactPanelRelativeBudget`, then a stored-stage wrapper over
     `storedQRCompactStepRelativeBudget`, then the per-step compact-product
     theorem from item 158.  The Householder theorem
     `householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le`
     proves the panel cap `n * cCol + cRhs` from uniform vector-level caps.
     The stored-QR theorem
     `storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le`
     specializes this to the signed stored QR reflector.  The least-squares
     theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`
     checks the product threshold with sequence cap
     `n * (n * cCol + cRhs)`.  This reduces the route to vector-level compact
     caps and scalar smallness; it does not prove either from a concrete
     computed loop.  Two weak-component validation passes are clean: focused
     LSQRSolve build, executable lookup, whitespace check, touched Lean marker
     scan, qualified axiom audit, theorem PDF compile, targeted text
     extraction, and rendered-page inspection of pages 187--189 passed.  The
     axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.

160. Added the primitive norm-budget compact column/RHS cap reduction for the
     equation (8) rectangular QR/preconditioner route.  No new external source
     is used; this is local algebra over the repository definitions
     `householderCompactNormBudget` and
     `householderCompactRelativeBudget`, followed by the panel and stored-step
     cap adapters from item 159.  The Householder theorem
     `householderCompactRelativeBudget_le_of_normBudget_le_mul` proves that a
     primitive bound
     `householderCompactNormBudget fp n v beta x <= c * vecNorm2 x` implies the
     relative cap, with the zero-vector case handled by the definition.  The
     panel theorem
     `householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`,
     the stored-QR theorem
     `storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul`, and
     the least-squares theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`
     then use the same cap chain `n * cCol + cRhs` and
     `n * (n * cCol + cRhs)`.  This reduces the route to proving primitive
     norm-budget inequalities and scalar smallness from the concrete FP loop;
     it does not prove either.  Two weak-component validations are clean:
     focused HouseholderApply, HouseholderQR, and LSQRSolve builds, executable
     lookup, whitespace checks, touched Lean marker scans, qualified axiom
     audits, theorem PDF compile, targeted text extraction, and rendered-page
     inspection of pages 187--190 passed twice.  The axiom audit reports only
     standard `propext`, `Classical.choice`, and `Quot.sound`.

161. Added the componentwise compact column/RHS cap reduction for the equation
     (8) rectangular QR/preconditioner route.  No new external source is used;
     this is local algebra over the repository definitions
     `householderCompactComponentBudget` and `householderCompactNormBudget`,
     using the existing component-budget nonnegativity theorem and the local
     Euclidean norm lemmas `vecNorm2_le_of_abs_le`, `vecNorm2_smul`, and
     `vecNorm2_abs`.  The Householder theorem
     `householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs` proves
     that entrywise bounds
     `householderCompactComponentBudget fp n v beta x i <= c * |x i|` imply the
     primitive norm-budget bound
     `householderCompactNormBudget fp n v beta x <= c * vecNorm2 x`.  The
     relative, panel, stored-QR, and least-squares theorems
     `householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs`,
     `householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`,
     `storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`,
     and
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`
     then use the same cap chain `n * cCol + cRhs` and
     `n * (n * cCol + cRhs)`.  This reduces the route to proving entrywise
     component-budget inequalities and scalar smallness from the concrete FP
     loop; it does not prove either.  Two weak-component validations are clean:
     focused LSQRSolve builds, executable lookup, whitespace checks, touched
     Lean marker scans, qualified axiom audits, theorem PDF compile/text
     extraction, and rendered-page inspection of pages 188--190 passed twice.
     The axiom audit reports only standard `propext`, `Classical.choice`, and
     `Quot.sound`.

162. Added the explicit norm-coefficient compact Householder reduction for the
     equation (8) rectangular QR/preconditioner route.  No external source is
     used; this is local algebra over the repository's compact
     dot/scale/subtract model.  The new local route first proves
     `householderAbsDotBudget_le_vecNorm2_mul`, then defines
     `householderCompactUpdateCoeff` and
     `householderCompactNormBudgetCoeff`.  The component theorem
     `householderCompactComponentBudget_le_updateCoeff_mul_norm` bounds the
     explicit budget by a nonlocal term
     `updateCoeff * ||x||_2 * |v_i|` plus the local subtraction term
     `fp.u * |x_i|`; `householderCompactNormBudget_le_normBudgetCoeff_mul`
     converts this to a normwise compact-budget cap.  The stored QR theorem
     `storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff` and the
     least-squares theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`
     use this coefficient in the finite-max compact-product route.  This
     corrects the previously tempting but too-strong entrywise-relative route.
     Two weak-component validation passes are clean: focused builds, repeated
     `git diff --check`, touched-file marker scan, executable lookup, qualified
     axiom audit, PDF compile, targeted `pdftotext`, and rendered page
     inspection all passed.  No external source is used and no citation-only
     hypothesis is hidden.

163. Added the canonical finite-maximum specialization for the norm-coefficient
     compact Householder route.  No external source is used; this is local
     finite-order bookkeeping over the stored-stage coefficients already
     formalized in item 162.  `storedQRCompactStepNormBudgetCoeff_nonneg`
     proves stage-coefficient nonnegativity, and
     `storedQRCompactStepNormBudgetCoeffBudget` is the finite maximum over
     `Fin n` (zero when `n = 0`).  The theorems
     `storedQRCompactStepNormBudgetCoeff_le_budget` and
     `storedQRCompactStepNormBudgetCoeffBudget_nonneg` justify choosing that
     maximum as the uniform coefficient in
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`.
     Two weak-component validation passes are clean: repeated `git diff
     --check`, touched-file marker scans, focused LSQRSolve build, executable
     lookup, qualified axiom audits, PDF compile/text extraction, and rendered
     pages 188--193 all passed.  No external source is used and no citation-only
     hypothesis is hidden.

164. Added the coefficient-maximum equation (8) handoff.  No external source is
     used; this is a local composition step reusing the canonical coefficient
     maximum from item 163.  `LSQRSolve.lean` proves
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
     deriving the packaged route-1 invariant from local diagonal dominance and
     the scalar inequality involving `storedQRCompactStepNormBudgetCoeffBudget`.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
     composing that invariant into the high-probability sampled least-squares
     objective theorem.  Two weak-component validation passes are clean:
     repeated `git diff --check`, touched-file marker scans, focused RandNLA
     build, executable lookup, qualified axiom audits, PDF compile/text
     extraction, and rendered pages 190--192 all passed.  No external source is
     used and no citation-only hypothesis is hidden.

165. Added the bounded scalar certificate for the coefficient-maximum route.
     No external source is used; this is local monotonicity algebra over the
     repository's canonical finite maxima.  `LSQRSolve.lean` proves
     `storedQRCompactNormBudgetCoeffSmallness_of_bounds`, which turns bounds
     \(D_*\le D_{\max}\), \(C_{\rm HH}^*\le C_{\max}\), and
     \(N_*\le N_{\max}\) plus the cleaner scalar inequality in
     \(D_{\max},C_{\max},N_{\max}\) into the exact canonical scalar inequality.
     It also proves
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_bounds`
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffBoundedSmallness`.
     Two weak-component validation passes are clean: repeated `git diff
     --check`, touched Lean marker scans, focused LSQRSolve builds, executable
     lookup, qualified axiom audits, PDF compile/text extraction, and rendered
     pages 190--193 all passed.  The axiom audit reports only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  The step does not prove the
     displayed upper bounds or the final scalar inequality from a concrete QR
     recurrence.

166. Added the pointwise route-bound certificates for the coefficient-maximum
     route.  No external source is used; this is local finite-maximum
     bookkeeping.  `LSQRSolve.lean` proves
     `storedQRDiagDominantInvFactorBudget_le_of_forall_le`,
     `storedQRPivotColumnNormBudget_le_of_forall_le`, and
     `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_le`, which bound
     the three canonical finite maxima from per-pivot route estimates.  It also
     proves `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_bounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds`.
     Two weak-component validation passes are clean: repeated focused LSQRSolve
     builds, executable lookup, touched Lean marker scans, qualified axiom
     audits, PDF compile/text extraction, and rendered pages 190--194 passed.
     The step does not prove the pointwise estimates, local diagonal dominance,
     or the final scalar inequality from a concrete QR recurrence.

167. Added the solver-facing pointwise coefficient-maximum handoff.  No external
     source is used; this is local composition of item 166 with the repository's
     concrete-dual QR solve certificate.  `LSQRSolve.lean` proves
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`,
     which uses the pointwise product-budget theorem to discharge the
     per-pivot compact-product field required by the concrete-dual solver
     theorem.  It also proves
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`,
     deriving the leading-block determinant hypotheses from local diagonal
     dominance via `det_ne_zero_of_diagDominantUpper`.  First weak-component
     validation is clean twice: repeated `git diff --check`, touched Lean marker
     scans, focused LSQRSolve builds, executable lookup, qualified axiom audits,
     PDF compile/text extraction, and rendered pages 191--195 passed.  The step
     does not prove the pointwise estimates, local diagonal dominance, or the
     scalar inequality from a concrete QR recurrence.

168. Added the per-pivot beta-norm coefficient reduction for the compact
     Householder coefficient route.  No external source is used; this is local
     algebra on the repository's explicit compact dot/scale/subtract FP budget.
     `HouseholderApply.lean` proves the exact expansion
     `householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor`,
     namely that the compact coefficient is
     `u + (|beta| * ||v||_2^2) * householderCompactNormBudgetCoeffFactor fp n`,
     and proves the factor nonnegative under `gammaValid`.  `HouseholderQR.lean`
     lifts this to stored signed stages, and `LSQRSolve.lean` threads the
     specialization through the finite maximum, scalar-smallness, product, and
     invariant surfaces.  The proof route is advisory-free and local.  It does
     not prove the signed-stage estimate `|beta_k| * ||v_k||_2^2 <= Bmax`, local
     diagonal dominance, or the final scalar inequality from a concrete QR
     recurrence.  Two weak-component validation passes are clean: repeated
     focused LSQRSolve builds, executable lookup, touched-source marker scans,
     qualified axiom audits, PDF compile/text extraction, and rendered page
     inspections passed with only pre-existing HouseholderQR unused-variable
     warnings.

169. Added the exact Householder-normalization coefficient branch.  No external
     source is used; this is local algebra reusing
     `householderBeta_mul_inner_self_eq_two`.  `HouseholderSpec.lean` proves
     `abs_householderBeta_mul_vecNorm2_sq_eq_two` and
     `abs_householderBeta_mul_vecNorm2_sq_le_two`, converting the repository's
     raw denominator identity into the coefficient-route form
     `|beta| * ||v||_2^2 = 2`.  `HouseholderQR.lean` specializes this to
     stored signed stages and to the source-shaped denominator hypothesis used
     by the QR loop.  `LSQRSolve.lean` then threads the concrete `Bmax = 2`
     value through the finite coefficient maximum, scalar-smallness, product,
     and invariant surfaces.  The proof route is advisory-free and local.  It
     does not prove scalar smallness, local diagonal dominance/off-diagonal
     control, inverse-factor or pivot-column pointwise bounds, determinant or
     conditioning fields, or the final generic equation (8) QR/preconditioner
     theorem.  Focused LSQRSolve build passed, and two weak-component passes
     are clean: repeated `git diff --check`, touched Lean marker scans,
     focused `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`,
     executable lookup, qualified axiom audit for the eleven new theorem names,
     theorem PDF compile, targeted `pdftotext`, and rendered pages 190--193
     passed.  The axiom audit reported only standard `propext`,
     `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file
     was deleted.
170.  2026-06-02, LS.2g-fi source-facing scalar-smallness normalization:
     no external source was used.  This is local scalar algebra in
     `LSQRSolve.lean`, rewriting the expanded exact-normalization coefficient
     condition with
     `Cmax = fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m`
     into `2 * Dmax * (m * ((n * (n + 1) * Cmax * Nmax)^2)) < 1`.
     The Lean targets are
     `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_simple_bounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenSimpleBounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenSimpleBounds`.
     Focused LSQRSolve build passed, and two weak-component passes are clean:
     repeated `git diff --check`, touched Lean marker scans, focused LSQRSolve
     builds, executable lookup, qualified axiom audit for the three new theorem
     names, theorem PDF compile, targeted `pdftotext`, and rendered pages
     192--193 passed.  The axiom audit reported only standard `propext`,
     `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file
     was deleted.
171.  2026-06-02, LS.2g-fj source-denominator scalar cap bridge:
     no external source was used.  This is local scalar monotonicity in
     `LSQRSolve.lean`, showing that the source-facing condition with
     `fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` follows from
     upper caps `fp.u <= Ucap` and
     `householderCompactNormBudgetCoeffFactor fp m <= Fcap` and the displayed
     scalar inequality with `Ucap + 2 * Fcap`.  The Lean targets are
     `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_cap_bounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenCapBounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenCapBounds`.
     Focused LSQRSolve build passed, and two weak-component validation passes
     are clean: repeated `git diff --check`, production Lean marker scans,
     focused LSQRSolve builds, executable lookup, qualified axiom audits,
     theorem PDF compile, targeted `pdftotext`, and rendered pages 192--195
     passed.  The axiom audit reported only standard `propext`,
     `Classical.choice`, and `Quot.sound`, and the temporary audit file was
     deleted.  The step does not prove the cap estimates, local diagonal
     dominance/off-diagonal control, inverse-factor or pivot-column pointwise
     bounds, source nonbreakdown, determinant/conditioning fields, or the final
     generic equation (8) QR/preconditioner theorem.
172.  2026-06-02, LS.2g-fk Householder coefficient-factor cap:
     no external source was used.  This is local scalar monotonicity in
     `HouseholderApply.lean`, bounding the already-defined coefficient factor
     `householderCompactNormBudgetCoeffFactor fp m` by the explicit polynomial
     in displayed caps `Ucap` and `Gcap`, under `fp.u <= Ucap`,
     `gamma fp m <= Gcap`, and nonnegative caps.  The Lean target is
     `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le`.  Two
     weak-component passes are clean: repeated `git diff --check`, production
     Lean marker scans, focused HouseholderApply and LSQRSolve builds,
     executable lookup, qualified axiom audit, theorem PDF compile, targeted
     `pdftotext`, and rendered pages 192--193 passed.  The axiom audit reported
     only standard `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, the `gamma` cap,
     scalar cap smallness, local diagonal dominance/off-diagonal control,
     inverse-factor or pivot-column pointwise bounds, source nonbreakdown,
     determinant/conditioning fields, or the final generic equation (8)
     QR/preconditioner theorem.
174.  2026-06-02, LS.2g-fm coefficient-factor cap from unit-roundoff cap:
     no external source was used.  This is a local composition of the
     Householder factor-cap theorem and the rounding gamma-cap theorem.  The
     Lean target is
     `householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap`, which
     derives the displayed factor bound directly from `fp.u <= Ucap`,
     `(m : ℝ) * Ucap < 1`, and the rational domination of `Gcap`.  Two
     weak-component passes are clean: repeated `git diff --check`, production
     marker scans, focused HouseholderApply/LSQRSolve builds, executable
     lookup, qualified axiom audit, theorem PDF compile, targeted `pdftotext`,
     and rendered pages 193--194 passed.  The axiom audit reported only
     standard `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, scalar cap
     smallness, local diagonal dominance/off-diagonal control, inverse-factor
     or pivot-column pointwise bounds, source nonbreakdown,
     determinant/conditioning fields, or the final generic equation (8)
     QR/preconditioner theorem.
175.  2026-06-02, LS.2g-fn source-denominator cap route from unit-roundoff/gamma caps:
     no external source was used.  This is a local composition of the
     least-squares source-denominator cap route with the LS.2g-fm Householder
     factor cap.  The Lean targets are
     `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uGammaCapBounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenUGammaCapBounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenUGammaCapBounds`.
     Two weak-component passes are clean: repeated `git diff --check`,
     production Lean marker scans, focused LSQRSolve builds, executable lookup,
     qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
     rendered pages 193--195 passed.  The axiom audit reported only standard
     `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, rational `Gcap`
     domination, scalar cap smallness, local diagonal dominance/off-diagonal
     control, inverse-factor or pivot-column pointwise bounds, source
     nonbreakdown, determinant/conditioning fields, or the final generic
     equation (8) QR/preconditioner theorem.
173.  2026-06-02, LS.2g-fl gamma cap from unit-roundoff cap:
     no external source was used.  This is local scalar monotonicity in
     `Rounding.lean`, proving that replacing `fp.u` by a displayed cap `Ucap`
     in Higham's `gamma` expression gives an upper bound, and that a displayed
     `Gcap` above this rational expression bounds `gamma fp m`.  The Lean
     targets are `gamma_le_of_u_le_cap` and `gamma_le_Gcap_of_u_le_cap`.
     Two weak-component passes are clean: repeated `git diff --check`,
     production marker scans, focused Rounding/HouseholderApply/LSQRSolve
     builds, executable lookup, qualified axiom audit, theorem PDF compile,
     targeted `pdftotext`, and rendered pages 193--194 passed.  The axiom audit
     reported only standard `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, scalar cap
     smallness, local diagonal dominance/off-diagonal control, inverse-factor
     or pivot-column pointwise bounds, source nonbreakdown,
     determinant/conditioning fields, or the final generic equation (8)
     QR/preconditioner theorem.
176.  2026-06-02, LS.2g-fo unit-roundoff-cap route elimination:
     no external source was used.  The local source is the `FPModel` structure
     itself, which stores only `u` and `u_nonneg`.  `Model.lean` now defines
     `FPModel.exactWithUnitRoundoff` and proves
     `FPModel.not_forall_u_le_cap`, showing that no fixed cap `fp.u <= Ucap`
     follows from the abstract model.  Two weak-component passes are clean:
     repeated `git diff --check`, production Lean marker scans, focused Model
     builds, executable lookup, qualified axiom audits, theorem PDF compile,
     targeted `pdftotext`, and rendered page 194 passed.  The axiom audit
     reported only standard `propext`, `Classical.choice`, and `Quot.sound`.
     This rules out closing the primitive cap as a hidden consequence of
     `FPModel`; it must remain a domain assumption or be derived from a future
     concrete machine model.
177.  2026-06-02, LS.2g-fp rational gamma cap specialization:
     no external source was used.  This is a local composition step in
     `LSQRSolve.lean`: the source-denominator cap route is specialized to
     `Gcap = (m * Ucap)/(1 - m * Ucap)`, so the rational-domination hypothesis
     becomes reflexivity.  The Lean targets are
     `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uRationalGammaCapBounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCapBounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCapBounds`.
     Two weak-component passes are clean: repeated `git diff --check`,
     production Lean marker scans, focused LSQRSolve builds, executable lookup,
     qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
     rendered pages 194--195 passed.  The axiom audit reported only standard
     `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, displayed scalar
     cap inequality, local diagonal dominance/off-diagonal control,
     inverse-factor or pivot-column pointwise bounds, source nonbreakdown,
     determinant/conditioning fields, or the final generic equation (8)
     QR/preconditioner theorem.
178.  2026-06-02, LS.2g-fq canonical finite-max rational gamma cap route:
     no external source was used.  This is a local repository-reuse step in
     `LSQRSolve.lean`: the rational-gamma source-denominator route chooses
     `Dcap = storedQRDiagDominantInvFactorBudget hmn A_hat` and
     `Ncap = storedQRPivotColumnNormBudget hmn A_hat`, then discharges the
     pointwise domination fields using
     `storedQRDiagDominantInvFactor_le_budget` and
     `storedQRPivotColumnNorm_le_budget`.  The Lean targets are
     `storedQRCompactNormBudgetCoeffSmallness_of_source_den_ne_zero_uRationalGammaCanonicalBounds`,
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`,
     and
     `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`.
     Two weak-component passes are clean: repeated `git diff --check`,
     production Lean marker scans, focused LSQRSolve builds, executable lookup,
     qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
     rendered pages 194--196 passed.  The axiom audit reported only standard
     `propext`, `Classical.choice`, and `Quot.sound`.
     The step does not prove the primitive unit-roundoff cap, displayed scalar
     cap inequality, local diagonal dominance/off-diagonal control, source
     nonbreakdown, determinant/conditioning fields, or the final generic
     equation (8) QR/preconditioner theorem.
179.  2026-06-02, LS.2g-fr solver/probability handoff for the canonical
     finite-max rational gamma cap route: no external source was used.  This
     is a local repository-reuse step in `LSQRSolve.lean` and
     `LeastSquaresSketch.lean`: the already proved canonical
     source-denominator invariant is composed into the solver-facing
     `LSQRSolveBackwardError` certificate and then into the existing
     high-probability rounded sampled-row objective theorem.  The Lean targets
     are
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
     Two weak-component passes are clean: repeated `git diff --check`,
     production Lean marker scans, focused LSQRSolve and LeastSquaresSketch
     builds, executable lookup, qualified axiom audits, theorem PDF compile,
     targeted `pdftotext`, and rendered pages 195--201 passed.  The axiom
     audit reported only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  The step does not prove local diagonal
     dominance/off-diagonal control, source denominator nonbreakdown, the
     primitive unit-roundoff cap, displayed canonical scalar smallness, a
     concrete machine-model cap, or the final generic equation (8)
     QR/preconditioner theorem without visible QR-domain assumptions.
180.  2026-06-02, LS.2g-fs canonical scalar-smallness route elimination:
     no external source was used.  This is a local theorem-statement
     correction in `LSQRSolve.lean`: the theorem
     `not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness`
     instantiates the canonical rational-gamma scalar-smallness route at a
     one-dimensional exact-with-unit-roundoff model, the constant matrix
     `A = [1]`, `alpha = 0`, and `Ucap = 1/2`.  The local diagonal-dominance,
     source-nonbreakdown, unit-cap, and rational-gamma-validity side
     conditions hold, but the displayed scalar inequality normalizes to a
     concrete false inequality.  Two weak-component passes are clean:
     repeated `git diff --check`, production Lean marker scans, focused
     LSQRSolve builds, executable lookup, qualified axiom audits, theorem PDF
     compile, targeted `pdftotext`, and rendered pages 198--199 passed.  The
     axiom audit reported only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  The step does not prove a positive scalar-smallness
     theorem; it proves that the scalar field is a genuine numerical/domain
     assumption unless stronger scale, conditioning, or machine-model
     hypotheses are added.
181.  2026-06-02, LS.2g-ft source nonbreakdown reduction for the canonical
     rational-gamma route: no external source was used.  This is a local
     repository-reuse step in `LSQRSolve.lean` and `LeastSquaresSketch.lean`.
     The scalar bridge
     `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`
     wraps the existing Householder lemma
     `householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`
     to derive the raw denominator `v_k^T v_k != 0` from the source facts
     `alpha_k^2 = ||A_k(k:m,k)||_2^2`, positive trailing norm square, and
     `alpha_k * A_k(k,k) <= 0`.  The canonical invariant, solver, and
     probability-level wrappers then reuse the already formalized
     rational-gamma route with that derived denominator proof.  The Lean
     targets are
     `StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`,
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`,
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
     Focused builds of LSQRSolve and LeastSquaresSketch pass; two-pass
     validation is in progress.  The step does not prove positive trailing
     norms, local diagonal dominance/off-diagonal control, scalar smallness,
     unit-roundoff caps, determinant/conditioning fields, or the final generic
     equation (8) QR/preconditioner theorem.
182.  2026-06-02, Algorithm 1 explicit floating-point scalar-radius
     correction: no external source was used.  This is a local
     repository-reuse step in `ElementwiseSpectral.lean` and
     `ElementwiseSampling.lean`.  The internal support-aware theorem already
     derives the entrywise matrix budget
     `sqMagTraceErrorBudget fp s s Ahat 0` from local gamma/hit-count
     stability on the sampler's probability-one positive-probability support.
     The new lemmas
     `sqMagTraceErrorBudget_zero_init_truncated_le_const` and
     `frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square`
     bound that matrix by the displayed scalar
     `(||Ahat||_F^2/tau)*gamma fp (s+1)` and its square Frobenius contribution
     by `n*(||Ahat||_F^2/tau)*gamma fp (s+1)`.  The corollaries
     `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square`
     and
     `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square`
     give the equation (2)-style FP residual bound with the source-only term
     `(2*n^2*||A||_F^2/eps)*gamma fp (s+1)` for `tau=eps/(2n)`.  This closes a
     PDF/readability and theorem-surface gap only; it does not alter the
     probability route or add a hidden concentration hypothesis.
183.  2026-06-03, LS.2g-gc actual-unit-roundoff scalar-validity guard:
     no external source was used.  This is a local repository-reuse step in
     `LSQRSolve.lean` and `LeastSquaresSketch.lean`.  The new wrappers
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff_no_gammaValid`
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff_no_gammaValid`
     replace the remaining `gammaValid` guard in the actual-unit-roundoff
     stored-lower branch by the displayed scalar condition
     `(m : ℝ) * fp.u < 1` or `(s : ℝ) * fp.u < 1`, deriving the validity facts
     internally via the cap-derived gamma-validity theorem with `Ucap = fp.u`.
     Two weak-component passes are clean: focused LSQRSolve and
     LeastSquaresSketch builds, executable lookup, `git diff --check`, touched
     Lean-source marker scan, qualified axiom audit, theorem PDF compile,
     targeted `pdftotext` over pages 207--210, and rendered pages 207--208
     passed.  The axiom audit reported only standard `propext`,
     `Classical.choice`, and `Quot.sound`.  This is a hypothesis-surface
     reduction only: it does not prove scalar smallness, local diagonal
     dominance/off-diagonal control, conditioning fields, or the final generic
     equation (8) QR/preconditioner theorem.
184.  2026-06-03, LS.2g-gd signed-alpha scalar-smallness route elimination
     after validity reduction: no external source was used.  This is a local
     repository-reuse step in `LSQRSolve.lean`.  The new theorem
     `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`
     reuses
     `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`
     to remove the abstract `gammaValid` premise from the failed scalar-smallness
     implication.  It shows that local diagonal dominance, the concrete
     signed-alpha equation, source denominator nonbreakdown, and
     `(m : ℝ) * fp.u < 1` do not imply the canonical finite-max rational-gamma
     scalar smallness inequality.  Two weak-component passes are clean:
     focused LSQRSolve and LeastSquaresSketch builds, executable lookup,
     `git diff --check`, touched Lean-source marker scan, qualified axiom
     audit, theorem PDF compile, targeted `pdftotext` over pages 207--209, and
     rendered page 208 passed.  The axiom audit reported only standard
     `propext`, `Classical.choice`, and `Quot.sound`.  This is a
     theorem-statement correction and route-elimination result only; it does
     not prove scalar smallness, local diagonal dominance/off-diagonal control,
     conditioning fields, or the final generic equation (8) QR/preconditioner
     theorem.
185.  2026-06-03, LS.2g-ge actual-unit-roundoff scalar-validity guard for the
     row-max-defect/global-product QR route: no external source was used.  This
     is a local repository-reuse step in `LSQRSolve.lean`,
     `LeastSquaresSketch.lean`, and the existing rounding lemmas
     `gammaValid_of_u_le_cap` and `gammaValid_mono`.  The new local and
     probability wrappers,
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct_of_actualUnitRoundoff_no_gammaValid`
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid`,
     derive the former `gammaValid` guards from `(m : ℝ) * fp.u < 1` or
     `(s : ℝ) * fp.u < 1` while leaving the scalar row-defect, determinant,
     norm-square nonbreakdown, and global compact-product hypotheses visible.
     Two weak-component passes are clean: focused LSQRSolve and
     LeastSquaresSketch builds, executable lookup, `git diff --check`, touched
     Lean-source marker scan, qualified axiom audit, theorem PDF compile,
     targeted `pdftotext` over page 182, and rendered page 182 passed.  The
     axiom audit reported only standard `propext`, `Classical.choice`, and
     `Quot.sound`.  This is a validity-surface reduction only; it does not
     prove the row-defect or off-diagonal-control condition,
     determinant/nonbreakdown fields, global compact-product smallness,
     conditioning fields, or the final generic equation (8) QR/preconditioner
     theorem.
186.  2026-06-03, LS.2g-gf finite stage-diagonal lower-bound defect packaging:
     no external source was used.  This is a local finite-maximum packaging step
     in `LSQRSolve.lean` for the already selected Cox--Higham active/prefix
     route.  The new definition `storedQRStageDiagLowerDefectBudget` is the
     finite maximum of `stageBudget k - |(S_k)_{ii}|` over displayed
     off-diagonal rows `i < k`; `storedQRStageDiagLowerDefect_le_budget` exposes
     each indexed defect below that maximum, and
     `storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos` converts
     the scalar nonpositivity condition into the pointwise diagonal lower-bound
     family.  The new source-control and solver wrappers with suffix
     `_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
     reuse the existing active/prefix global compact-step, completed-column, and
     global-product theorem family while replacing the full diagonal lower-bound
     family by this single scalar condition.  This records a listed
     red-bottleneck dependency reduction only; the scalar stage-diagonal
     condition itself remains a source/domain obligation for a concrete
     pivoted/sorted or off-diagonal-controlled loop.
187.  2026-06-03, LS.2g-gg active-max-pivot stage-diagonal reduction: no
     external source was used.  This is a local finite-selection reuse step.
     `storedQRActiveMaxPivotColumn_pivotMax` factors the already formalized
     active max-pivot selector theorem into the raw pivot-maximality field
     consumed by the active/prefix QR route.  The new source-control and solver
     wrappers with suffix
     `_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
     compose that policy reduction with the LS.2g-gf scalar stage-diagonal
     defect surface.  This closes the pivot-policy field only; the scalar
     stage-diagonal condition, determinant/nonbreakdown and conditioning
     assumptions, compact-product smallness, and final QR/preconditioner
     theorem remain local Lean obligations or visible domain assumptions.
188.  2026-06-03, LS.2g-gh exact no-pivot stage-diagonal scalar route
     elimination: no external source was used.  This is a local reuse of the
     existing two-stage exact Householder counterexample in `LSQRSolve.lean`.
     The new theorem
     `exactHouseholderQRDiagDominanceCounterexample_stageDiagLowerDefectBudget_pos`
     evaluates the constant-budget stage-diagonal scalar defect on that
     witness, and
     `not_forall_exact_trailing_householder_sequence_implies_stageDiagLowerDefectBudget_nonpos`
     wraps it as a universal-form route elimination.  The result rules out
     deriving `storedQRStageDiagLowerDefectBudget <= 0` from exact no-pivot
     recurrence, valid signed squared-norm identities, and nonzero denominators
     alone.  It leaves the positive pivoted/sorted/off-diagonal-control
     invariant, determinant/nonbreakdown and conditioning fields,
     compact-product smallness, and final QR/preconditioner theorem as local
     Lean obligations or visible domain assumptions.
189.  2026-06-03, LS.2g-gi row-max-to-stage-diagonal scalar bridge: no external
     source was used.  This is a local finite-maximum reuse step in
     `LSQRSolve.lean`.  The theorem
     `storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax`
     combines the existing row-max scalar defect extractor with the hypothesis
     that the uniform stage budget is bounded by the displayed row maximum,
     proving the stage-diagonal scalar defect nonpositive.  The theorem
     `storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageBudget_le_rowMax`
     specializes the bridge through the already proved local
     diagonal-dominance-to-row-max result.  The remaining mathematical work is
     to prove the stage-budget/row-max comparison, determinant/nonbreakdown and
     conditioning fields, compact-product smallness, and final
     QR/preconditioner theorem for a concrete loop, or to keep those fields
     visible as domain assumptions.
190.  2026-06-03, LS.2g-gj active-pivot stage-budget/row-max route
     elimination: no external source was used.  This is a local finite witness
     in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq` with the oversized uniform
     stage budget `3`.  The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
     shows that active max-pivoting, active-block budget control, displayed
     strict-upper budget control, nonsingular upper leading blocks, and positive
     active-block mass do not imply the comparison
     `stageBudget k <= qrLeadingStrictUpperRowMaxBudget ... k hk i`.  Thus the
     LS.2g-gi row-max bridge cannot close the stage-diagonal scalar condition
     without a genuinely stronger row-max/stage-budget invariant or an explicit
     domain assumption.  Determinant/nonbreakdown and conditioning fields,
     compact-product smallness, and the final QR/preconditioner theorem remain
     local Lean obligations or visible assumptions.
191.  2026-06-03, LS.2g-gk visible row-max-assumption active-pivot QR surface:
     no external source was used.  This is a local composition step in
     `LSQRSolve.lean`.  The new source-control and solver wrappers with suffix
     `_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows`
     turn visible row-max data, namely
     `storedQRRowMaxDiagDefectBudget <= 0` and the displayed comparison
     `stageBudget k <= qrLeadingStrictUpperRowMaxBudget ... k hk i`, into the
     scalar stage-diagonal condition via
     `storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax`.
     They then reuse the active-pivot stage-diagonal QR source-control/solver
     route.  The result corrects the theorem surface but does not prove the
     row-max scalar defect, the row-max comparison, determinant/nonbreakdown
     and conditioning fields, compact-product smallness, or the final
     QR/preconditioner theorem for a concrete loop.
192.  2026-06-03, LS.2g-gl active-pivot row-max scalar-defect route
     elimination: no external source was used.  This is a local finite witness
     in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `activeMaxPivotRowBudgetDiagCounterexample_rowMaxDiagDefectBudget_pos`
     computes a positive row-max scalar defect at displayed stage one, where
     the row maximum is `2` and the diagonal magnitude is `1`.  The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
     wraps this as a universal active-pivot/budget route elimination: active
     max-pivoting, active-block budget control, displayed strict-upper budget
     control, nonsingular upper leading blocks, and positive active-block mass
     do not imply `storedQRRowMaxDiagDefectBudget <= 0`.  Thus the row-max
     defect condition exposed by LS.2g-gk must come from a stronger concrete
     row-max/off-diagonal-control invariant or stay visible as a domain
     assumption.
193.  2026-06-03, LS.2g-gm probability-level visible row-max active-pivot
     equation (8) surface: no external source was used.  This is a local
     composition step in `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`
     exposes samplewise `storedQRRowMaxDiagDefectBudget <= 0` and
     `stageBudget <= qrLeadingStrictUpperRowMaxBudget` at the probability
     layer.  It derives the diagonal lower-bound family through the LS.2g-gi
     row-max bridge and then applies the existing LS.2g active-max-pivot
     probability wrapper.  This corrects the theorem surface for equation (8)
     but leaves the row-max scalar defect, stage-budget/row-max comparison,
     determinant/nonbreakdown or conditioning fields, global compact-product
     smallness, and final QR/preconditioner theorem as local Lean obligations
     or visible domain assumptions.
194.  2026-06-03, LS.2g-gn actual-unit-roundoff validity surface for the
     probability-level visible row-max active-pivot equation (8) theorem: no
     external source was used.  This is a local scalar-validity wrapper in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`
     derives the sampled and triangular validity fields from
     `(s : ℝ) * fp.u < 1` using `gammaValid_of_u_le_cap` and
     `gammaValid_mono`, then applies LS.2g-gm.  This removes only the
     `gammaValid` hypotheses; the row-max scalar defect, stage-budget/row-max
     comparison, determinant/nonbreakdown or conditioning fields, dual
     compact-budget data, global compact-product smallness, and final
     QR/preconditioner theorem remain local Lean obligations or visible domain
     assumptions.
195.  2026-06-03, LS.2g-go local actual-unit-roundoff validity surface for the
     visible row-max active-pivot solver theorem: no external source was used.
     This is a local scalar-validity wrapper in `LSQRSolve.lean`.  The theorem
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
     derives the local and triangular validity fields from
     `(m : ℝ) * fp.u < 1` using `gammaValid_of_u_le_cap` and
     `gammaValid_mono`, then applies LS.2g-gk's visible row-max active-pivot
     solver theorem.  This removes only the local `gammaValid` hypotheses; the
     row-max scalar defect, stage-budget/row-max comparison,
     determinant/nonbreakdown or conditioning fields, dual compact-budget data,
     global compact-product smallness, and final QR/preconditioner theorem
     remain local Lean obligations or visible domain assumptions.
196.  2026-06-03, LS.2g-gp source-control actual-unit-roundoff validity surface
     for the visible row-max active-pivot route: no external source was used.
     This is a local scalar-validity wrapper in `LSQRSolve.lean`.  The theorem
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
     derives the local validity field from `(m : ℝ) * fp.u < 1` using
     `gammaValid_of_u_le_cap`, then applies LS.2g-gk's visible row-max
     source-control theorem.  This removes only the source-control
     `gammaValid fp m` hypothesis; the row-max scalar defect,
     stage-budget/row-max comparison, determinant/nonbreakdown or conditioning
     fields, dual compact-budget data, global compact-product smallness, and
     final QR/preconditioner theorem remain local Lean obligations or visible
     domain assumptions.
197.  2026-06-03, LS.2g-gq product-smallness/row-max route elimination: no
     external source was used.  This is a local finite-witness theorem in
     `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos`
     chooses compact budget `B = 1/16`; the displayed leading blocks are upper
     triangular and nonsingular and satisfy the product compact-smallness
     inequality, but the same stage-one row has strict-upper row maximum `2`
     and diagonal magnitude `1`, so `storedQRRowMaxDiagDefectBudget <= 0`
     fails.  This rules out using compact-product smallness as a hidden proof
     of the row-max defect condition.  The row-max defect must come from a
     stronger concrete pivoted/sorted/off-diagonal-control invariant or remain
     visible as a domain assumption.
198.  2026-06-03, LS.2g-gr product-smallness/stage-diagonal scalar route
     elimination: no external source was used.  This is a local finite-witness
     theorem in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `activeMaxPivotRowBudgetDiagCounterexample_stageDiagLowerDefectBudget_pos`
     shows that the constant stage budget `2` gives a positive scalar
     stage-diagonal lower-bound defect on the active-pivot witness.  The
     theorem
     `not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos`
     chooses compact budget `B = 1/16`; upper-triangular nonsingular displayed
     blocks and the product compact-smallness inequality hold, but
     `storedQRStageDiagLowerDefectBudget <= 0` fails.  Thus compact-product
     smallness cannot replace the diagonal lower-bound scalar invariant in the
     active/prefix Cox--Higham route.
199.  2026-06-03, LS.2g-gs product-smallness/active-budget comparison route
     elimination: no external source was used.  This is a local finite-witness
     theorem in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
     adds compact-product smallness with `B = 1/16` to the active-pivot
     active/off-diagonal budget surface and chooses the oversized uniform
     stage budget `3`.  All strengthened hypotheses hold, but at displayed
     stage one the row maximum is `2`, so the comparison
     `stageBudget <= qrLeadingStrictUpperRowMaxBudget` fails.  Thus product
     smallness cannot rescue the stage-budget/row-max comparison left by the
     active/prefix route.
200.  2026-06-03, LS.2g-gt product-smallness/active-budget row-max route
     elimination: no external source was used.  This is a local finite-witness
     theorem in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
     adds compact-product smallness with `B = 1/16` to the active-pivot
     active/off-diagonal budget surface.  All strengthened hypotheses hold,
     but at displayed stage one the strict-upper row maximum is `2` and the
     displayed diagonal magnitude is `1`, so
     `storedQRRowMaxDiagDefectBudget <= 0` fails.  Thus product smallness
     cannot rescue the row-max scalar defect condition left by the
     active/prefix route.
201.  2026-06-03, LS.2g-gu product-smallness/active-budget stage-diagonal
     route elimination: no external source was used.  This is a local
     finite-witness theorem in `LSQRSolve.lean`, reusing
     `activeMaxPivotRowBudgetDiagCounterexampleSeq`.  The theorem
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
     adds compact-product smallness with `B = 1/16` to the active-pivot
     active/off-diagonal budget surface and uses constant stage budget `2`.
     All strengthened hypotheses hold, but at displayed stage one the
     displayed diagonal magnitude is `1`, so
     `storedQRStageDiagLowerDefectBudget <= 0` fails.  Thus product smallness
     cannot rescue the scalar stage-diagonal lower-bound condition left by the
     active/prefix route.
202.  2026-06-03, LS.2g-gv active-pivot budget stage-diagonal route
     elimination: no external source was used.  This is a local implication
     theorem in `LSQRSolve.lean`.  The theorem
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
     derives a failed active-only route from the LS.2g-gu product-plus-active
     obstruction: a universal active-only implication would also prove the
     product-plus-active implication, contradicting the checked finite witness.
     Thus active max-pivoting and active/off-diagonal budget control cannot
     discharge the scalar stage-diagonal condition.
203.  2026-06-03, LS.2g-gw finite stage-diagonal converse packaging: no
     external source was used.  This is a local finite-maximum theorem in
     `LSQRSolve.lean`.  The theorem
     `storedQRStageDiagLowerDefectBudget_nonpos_of_stageBudget_le_diag` proves
     that the displayed pointwise lower-bound family
     `stageBudget k <= |(S_k)_{ii}|` for every off-diagonal row `i < k`
     implies
     `storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget <= 0`.
     Together with the existing extractor, this closes the finite-family
     scalar packaging direction without proving the pointwise lower-bound
     invariant from a concrete QR loop.
204.  2026-06-03, LS.2g-gx finite stage-budget/row-max comparison packaging:
     no external source was used.  This is local finite-maximum reasoning in
     `LSQRSolve.lean`.  The definition
     `storedQRStageRowMaxComparisonDefectBudget` is the finite maximum of
     `stageBudget k - qrLeadingStrictUpperRowMaxBudget hmn A_hat k hk i` over
     displayed off-diagonal rows `i < k`.  The extractor
     `storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`
     and converse
     `storedQRStageRowMaxComparisonDefectBudget_nonpos_of_stageBudget_le_rowMax`
     make this scalar condition an exact finite package for the displayed
     comparison dependency.  The bridge theorem
     `storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageRowMaxComparisonDefectBudget_nonpos`
     combines the scalar comparison defect with nonpositive row-max defect to
     supply the scalar stage-diagonal condition.  This does not prove either
     scalar defect from a concrete QR loop.
205.  2026-06-03, LS.2g-gy scalar-comparison active-pivot row-max theorem
     surface: no external source was used.  This is a local theorem-surface
     reduction in `LSQRSolve.lean` and `LeastSquaresSketch.lean`.  The new
     source-control, local solver, and probability wrappers replace the
     pointwise displayed comparison
     `stageBudget <= qrLeadingStrictUpperRowMaxBudget` by the scalar finite
     condition `storedQRStageRowMaxComparisonDefectBudget <= 0`, recover the
     old comparison with
     `storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`,
     and then reuse the already-checked visible row-max active-pivot theorems.
     This does not prove the scalar row-max defect or scalar comparison defect
     from a concrete QR loop; it only makes those two scalar dependencies the
     visible interface at source-control, solver, and equation (8) levels.
206.  2026-06-03, LS.2g-gz scalar-comparison route elimination: no external
     source was used.  This is local implication reasoning in
     `LSQRSolve.lean`, reusing the already-formalized active-pivot
     oversized-budget counterexample for the displayed comparison.  The
     theorems
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
     and
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
     prove that active-pivot active/off-diagonal budget data, with or without
     compact-product smallness, cannot imply the scalar finite comparison
     defect.  The proof route is by contradiction: the scalar extractor would
     yield the displayed `stageBudget <= rowMax` comparison, contradicting the
     checked pointwise route-elimination theorem.
207.  2026-06-03, LS.2g-ha row-max-granted scalar-comparison route
     elimination: no external source was used.  This is a local
     counterexample and implication audit in `LSQRSolve.lean`.  The witness
     `activeMaxPivotRowMaxComparisonCounterexampleSeq` has nonpositive
     `storedQRRowMaxDiagDefectBudget` but positive
     `storedQRStageRowMaxComparisonDefectBudget` for the uniform stage budget
     `3`.  Therefore the theorems
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
     and
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
     rule out deriving the scalar comparison defect from the active-pivot
     active/off-diagonal budget surface even after the row-max scalar defect is
     granted, with or without product compact-smallness.
208.  2026-06-03, LS.2g-hb row-max-alone stage-diagonal route
     elimination: no external source was used.  This is a local
     counterexample and implication audit in `LSQRSolve.lean`.  The witness
     `activeMaxPivotRowMaxComparisonCounterexampleSeq` still has nonpositive
     `storedQRRowMaxDiagDefectBudget`, but with uniform stage budget `4` it has
     positive `storedQRStageDiagLowerDefectBudget`.  Therefore
     `not_forall_rowMaxDiagDefectBudget_implies_stageDiagLowerDefectBudget_nonpos`
     rules out deriving the scalar stage-diagonal defect condition from the
     scalar row-max defect alone.  The row-max-to-stage-diagonal bridge still
     needs the explicit comparison scalar, a pointwise stage-budget/row-max
     comparison, or an equivalent stronger concrete loop invariant.
209.  2026-06-03, LS.2g-hc product/active row-max-granted stage-diagonal
     route elimination: no external source was used.  This is a local
     counterexample and implication audit in `LSQRSolve.lean`.  The theorems
     `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
     and
     `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
     reuse `activeMaxPivotRowMaxComparisonCounterexampleSeq` with uniform
     stage budget `4` and compact budget `B = 1/16`.  The witness satisfies
     the active-pivot active/off-diagonal budget surface, the product
     compact-smallness inequality, and
     `storedQRRowMaxDiagDefectBudget <= 0`, but its
     `storedQRStageDiagLowerDefectBudget` remains positive.  Therefore adding
     active max-pivoting, active/off-diagonal budgets, and compact-product
     smallness cannot replace the comparison scalar in the row-max bridge.
210.  2026-06-03, LS.2g-hd diagonal-dominant scalar-comparison active-pivot
     surface: no external source was used.  This is a local composition theorem
     in `LSQRSolve.lean`.  The source-control wrapper
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`
     and the solver wrapper
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`
     derive leading-block determinant nonzeroness from
     `IsDiagDominantUpper` using `det_ne_zero_of_diagDominantUpper`, then derive
     the scalar stage-diagonal condition from diagonal dominance plus
     `storedQRStageRowMaxComparisonDefectBudget <= 0` using
     `storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageRowMaxComparisonDefectBudget_nonpos`.
     This closes only a local theorem-surface dependency on separate
     determinant and row-max-defect assumptions; it does not prove diagonal
     dominance, the scalar comparison defect, conditioning/dual compact-budget
     fields, active-pivot policy, compact-product smallness, or the final
     generic QR/preconditioner theorem from a concrete loop.
211.  2026-06-03, LS.2g-he probability-level diagonal-dominant scalar-comparison
     surface: no external source was used.  This is a local sampled theorem in
     `LeastSquaresSketch.lean`.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`
     derives, for each sampled trace, the leading-block determinant fields from
     `IsDiagDominantUpper` using `det_ne_zero_of_diagDominantUpper` and the
     row-max scalar-defect field using
     `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant`.  It then reuses
     the scalar-comparison active-pivot equation (8) theorem.  This is the
     probability-level lift of LS.2g-hd only: it does not prove diagonal
     dominance, the scalar comparison defect, conditioning/dual compact-budget
     fields, active-pivot policy, compact-product smallness, or the final
     generic QR/preconditioner theorem from a concrete loop.
212.  2026-06-03, LS.2g-hf diagonal-dominance/comparison-defect route
     elimination: no external source was used.  This is a local finite witness
     in `LSQRSolve.lean`.  The theorem
     `activeMaxPivotRowMaxComparisonCounterexample_diagDominant` proves that
     the row-max-granted witness is `IsDiagDominantUpper` at every displayed
     leading block, while
     `not_forall_diagDominant_implies_stageRowMaxComparisonDefectBudget_nonpos`
     uses the same witness with uniform stage budget `3` to refute any
     universal derivation of
     `storedQRStageRowMaxComparisonDefectBudget <= 0` from diagonal dominance
     alone.  This closes only a failed-route dependency for the scalar
     comparison defect; it does not prove that defect from the concrete
     pivoted/sorted/off-diagonal-controlled loop.
213.  2026-06-03, LS.2g-hg diagonal-dominance/product-smallness comparison
     route elimination: no external source was used.  This is a local finite
     witness in `LSQRSolve.lean`.  The theorem
     `activeMaxPivotRowMaxComparisonCounterexample_productBudget` proves that
     the LS.2g-hf diagonally dominant witness also satisfies the displayed
     compact-product-smallness inequality with `B = 1 / 16`, and
     `not_forall_diagDominant_product_budget_implies_stageRowMaxComparisonDefectBudget_nonpos`
     refutes any universal derivation of the scalar comparison defect from
     diagonal dominance plus that product-smallness surface.  This closes only
     the product-strengthened failed route; the positive scalar-comparison
     invariant remains open for a concrete pivoted/sorted/off-diagonal loop.
214.  2026-06-03, LS.2g-hi finite-max compact-product handoff for the active
     diagonal-dominant scalar-comparison branch: no external source was used.
     This is a local adapter in `LSQRSolve.lean` and `LeastSquaresSketch.lean`.
     The new source-control, solver, and probability wrappers derive
     `storedQRCompactSequenceProductBudget < 1` from the repository's existing
     canonical finite-max smallness theorem
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`,
     then reuse the LS.2g-hd/he global-product active-pivot
     scalar-comparison wrappers.  This closes the raw global-product
     theorem-surface dependency for that branch only; the finite-max scalar
     inequality, diagonal dominance, scalar comparison defect, active-pivot
     policy, conditioning/dual fields, and final generic theorem remain open or
     visible.
215.  2026-06-03, LS.2g-hj concrete-dual finite-max handoff for the active
     diagonal-dominant scalar-comparison branch: no external source was used.
     This is a local adapter in `LSQRSolve.lean` and `LeastSquaresSketch.lean`.
     The new reusable lemma
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_diagDominant_concreteDualProductSequenceBudget`
     factors the existing concrete diagonal-dominant product-sequence route:
     local diagonal dominance supplies the triangular inverse budget through
     the already-formalized `diagDominantUpperInvBudgetExpr` theorem family, and
     the finite product budget controls the actual compact pivot budget via
     `storedQRCompactPivotBudget_le_sequence_column_norm`.  The source-control,
     solver, and probability wrappers with suffix
     `finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual` then reuse
     that margin to remove the auxiliary `κ`, `K`, and dual compact-budget
     hypotheses from the active finite-max scalar-comparison branch.  This
     closes only the conditioning/dual theorem-surface dependency for that
     branch; diagonal dominance, the scalar comparison defect, active-pivot
     policy, signed-stage recurrence budgets, finite-max scalar smallness, and
     the final concrete QR/preconditioner theorem remain open or visible.
216.  2026-06-03, LS.2g-hk active-surface scalar-comparison route elimination:
     no external source was used.  This is a local counterexample inside
     `LSQRSolve.lean` for the red QR/preconditioner bottleneck.  The new theorem
     `not_forall_diagDominant_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
     strengthens the diagonal-dominance/product-smallness failed route by
     granting the current active branch's active-pivot and active/off-diagonal
     budget surface.  The same two-by-two witness is locally diagonally
     dominant, satisfies the product budget with `B = 1 / 16`, has positive
     active-block mass, satisfies active max-pivoting, and obeys the
     active/off-diagonal budget bounds, but still has positive
     `storedQRStageRowMaxComparisonDefectBudget`.  This rules out deriving the
     comparison scalar from the current active-surface assumptions; the scalar
     comparison defect remains a genuine loop invariant or visible source/domain
     field.
217.  2026-06-03, LS.2g-hl exact no-pivot comparison scalar route elimination:
     no external source was used.  This is a local counterexample inside
     `LSQRSolve.lean` for the same red QR/preconditioner bottleneck.  The new
     theorems
     `exactHouseholderQRDiagDominanceCounterexample_stageRowMaxComparisonDefectBudget_pos`
     and
     `not_forall_exact_trailing_householder_sequence_implies_stageRowMaxComparisonDefectBudget_nonpos`
     reuse the existing exact two-stage no-pivot Householder recurrence
     witness.  With constant stage budget `3`, displayed stage one has
     strict-upper row maximum `2`, so the scalar comparison defect is positive.
     Therefore exact trailing recurrence, signed squared-norm identities,
     nonzero denominators, and nonnegative stage budgets do not imply the
     comparison scalar; the proof route must use a stronger pivoted/sorted
     invariant or keep the scalar visible.
218.  2026-06-03, LS.2g-hm active scalar-comparison source-denominator
     rational-gamma compact-product handoff: no external source was used.
     This is a local adapter inside `LSQRSolve.lean` for the same red
     QR/preconditioner bottleneck.  The new source-control and local solver
     wrappers
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
     and
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
     derive the active branch's raw compact-product hypothesis from
     `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`
     and the per-pivot compact-product budget bound.  This reduces the active
     local source-control/solver surface from the assembled finite-max scalar
     involving `storedQRCompactSequenceRelativeBudget` to source-denominator
     nonbreakdown, `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and the canonical
     rational-gamma cap-smallness scalar.  It is a dependency reduction only:
     local diagonal dominance, the scalar comparison defect, active-pivot
     policy, signed-stage recurrence budgets, source-denominator and unit-cap
     obligations, the scalar cap-smallness inequality, and the final concrete
     QR/preconditioner theorem remain open or visible.
219.  2026-06-03, LS.2g-hn sampled active scalar-comparison source-denominator
     rational-gamma compact-product handoff: no external source was used.
     This is a local probability-level adapter inside `LeastSquaresSketch.lean`
     for the same red QR/preconditioner bottleneck.  The theorem
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver`
     applies the LS.2g-hm source-control certificate samplewise, then reuses
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`.
     It reduces the sampled equation (8) active branch from the assembled
     finite-max compact-product scalar to source-denominator nonbreakdown,
     `fp.u <= Ucap`, `(s : ℝ) * Ucap < 1`, and the canonical rational-gamma
     cap-smallness scalar.  This is a dependency reduction only: local diagonal
     dominance, the scalar comparison defect, active-pivot policy, signed-stage
     recurrence budgets, source-denominator and unit-cap obligations, the
     scalar cap-smallness inequality, and the final concrete QR/preconditioner
     theorem remain open or visible.
220.  2026-06-03, LS.2g-ho active source-denominator actual-unit validity
     surface: no external source was used.  This is a local validity-surface
     adapter inside `LSQRSolve.lean` and `LeastSquaresSketch.lean` for the same
     red QR/preconditioner bottleneck.  The new source-control, solver, and
     probability wrappers
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`
     specialize `Ucap = fp.u`, use `FPModel.u_nonneg` for the cap
     nonnegativity field, and derive the formerly abstract `gammaValid` fields
     from `(m : ℝ) * fp.u < 1` or `(s : ℝ) * fp.u < 1` via
     `gammaValid_of_u_le_cap` and `gammaValid_mono`.  This is a dependency
     reduction only: source-denominator nonbreakdown, actual-unit scalar
     smallness, local diagonal dominance, scalar comparison, active-pivot
     policy, signed-stage recurrence budgets, and the final concrete
     QR/preconditioner theorem remain open or visible.
221.  2026-06-03, LS.2g-hp active stored-lower source-denominator
     nonbreakdown: no external source was used.  This is a local dependency
     reduction that combines previously formalized stored Householder QR shape
     facts and signed-alpha scalar facts.  The helper
     `storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence`
     derives the raw Householder source-denominator nonbreakdown field from
     `storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence`,
     `qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock`,
     `det_ne_zero_of_diagDominantUpper`,
     `householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
     `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`.
     The active actual-unit source-control, local solver, and sampled equation
     (8) wrappers
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
     `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`, and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`
     use that helper to remove the raw denominator field.  Actual-unit scalar
     smallness, local diagonal dominance/off-diagonal control, scalar
     comparison, active-pivot and signed-stage loop invariants, and the final
     concrete QR/preconditioner theorem remain open or visible.
222.  2026-06-03, LS.2g-hq stored-recurrence actual-unit scalar-smallness
     route elimination: no external source was used.  This is a local
     theorem-statement correction for the red QR/preconditioner bottleneck.
     `LSQRSolve.lean` proves
     `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`
     by adapting the existing `1 x 1` exact-with-unit-roundoff witness to the
     post-stored-lower surface: `A_hat 0` is the unit panel, `A_hat 1` is the
     exact stored Householder panel update, and the witness satisfies the
     stored recurrence, local diagonal dominance, the signed-alpha definition,
     and `(1 : ℝ) * fp.u < 1` while violating the canonical rational-gamma
     finite-max scalar-smallness inequality.  Thus actual-unit scalar
     smallness remains a genuine numerical/domain obligation unless stronger
     scale, conditioning, or concrete machine-model hypotheses are proved.
223.  2026-06-03, LS.2g-hr stored-recurrence actual-unit
     diagonal-dominance route elimination: no external source was used.  This
     is a local theorem-statement correction for the red QR/preconditioner
     bottleneck.  `LSQRSolve.lean` proves
     `exactHouseholderQRDiagDominanceCounterexample_stored_step` and
     `exactHouseholderQRDiagDominanceCounterexample_signed_alpha_def`, lifting
     the existing `2 x 2` exact Householder diagonal-dominance counterexample
     to the stored-panel recurrence using
     `exactHouseholderQRDiagDominanceCounterexampleFP`, an exact FP model with
     `fp.u = 0`.  The universal route-elimination theorem
     `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_diagDominant`
     then shows that stored recurrence, signed-alpha choice, nonzero source
     denominators, and `(2 : ℝ) * fp.u < 1` still do not imply
     `IsDiagDominantUpper` for the final displayed triangular block.  Thus
     local diagonal dominance/off-diagonal control remains a genuine
     loop/domain invariant unless a stronger pivoted/sorted/off-diagonal
     theorem is proved.
224.  2026-06-03, LS.2g-hs stored-recurrence actual-unit
     active-pivot route elimination: no external source was used.  This is a
     local theorem-statement correction for the red QR/preconditioner
     bottleneck.  `LSQRSolve.lean` proves
     `exactHouseholderQRDiagDominanceCounterexample_not_activeMaxPivotChoice`,
     showing that the initial state of the existing `2 x 2` witness cannot
     have its displayed first pivot equal to
     `householderActiveMaxPivotColumn`, because
     `householderActiveMaxPivotColumn_pivot_max` would force the second
     column's active trailing norm square to be at most the first column's
     norm square, i.e. `5 <= 1`.  The universal theorem
     `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_activeMaxPivotChoice`
     then reuses the exact FP/stored recurrence witness to show that stored
     recurrence, signed-alpha choice, nonzero source denominators, and
     `(2 : ℝ) * fp.u < 1` still do not imply the displayed active-pivot policy.
     Thus a concrete pivoted/sorted loop must prove that policy directly, or
     the theorem surface must keep it visible.
225.  2026-06-03, LS.2g-ht stored-recurrence actual-unit
     scalar row-budget route elimination: no external source was used.  This is
     a local theorem-statement correction for the red QR/preconditioner
     bottleneck.  `LSQRSolve.lean` proves
     `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_stageDiagLowerDefectBudget_nonpos`
     and
     `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The same exact FP/stored recurrence witness with `fp.u = 0`, signed-alpha
     choices, nonzero source denominators, and `(2 : ℝ) * fp.u < 1` has
     positive scalar stage-diagonal defect for constant stage budget `2` and
     positive scalar comparison defect for constant nonnegative stage budget
     `3`.  Thus the scalar stage-diagonal lower-bound and stage-budget/row-max
     comparison fields remain genuine loop/domain invariants unless a stronger
     pivoted/sorted/off-diagonal-control theorem is proved.
226.  2026-06-03, LS.2g-hu diagonal-dominant stored-recurrence
     actual-unit scalar row-budget route elimination: no external source was
     used.  This is a local finite counterexample/theorem-statement correction
     for the red QR/preconditioner bottleneck.  `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_stored_step`,
     `storedDiagDominantComparisonCounterexample_diagDominant`,
     `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageDiagLowerDefectBudget_nonpos`,
     and
     `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The exact stored sequence starting from `[[3,2],[0,1]]` uses `fp.u = 0`,
     satisfies the stored recurrence, signed-alpha choices, nonzero source
     denominators, actual-unit validity, local diagonal dominance, and
     nonnegative stage budgets, but the scalar diagonal-lower and
     stage-budget/row-max comparison defects remain positive for constant
     stage budgets `4` and `3`.  Thus diagonal dominance still does not hide
     the remaining scalar row-budget obligations.
227.  2026-06-03, LS.2g-hv combined row-sorting/column-pivot
     least-squares bookkeeping: no new external source was used.  This is a
     local algebraic bridge for the already selected Cox--Higham
     pivoted/sorted route.  `LSQRSolve.lean` proves
     `rectLSGram_permuteRowsCols`, `rectLSRhs_permuteRowsCols`, and
     `RectLSNormalEquations.of_permuteRowsCols`; `LeastSquaresSketch.lean`
     proves `lsResidual_permuteRowsCols`, `lsObjective_permuteRowsCols`, and
     `IsLeastSquaresMinimizer.of_permuteRowsCols`.  These theorems compose the
     existing row-sorting invariance and column-pivot relabeling layers, so a
     row-sorted and column-pivoted normal-equation solution or exact minimizer
     can be pulled back to the original least-squares coordinates in one step.
     This closes bookkeeping only; the concrete pivoted/sorted Householder
     growth/sorting field, diagonal lower-bound invariant, compact smallness,
     active-pivot policy, and final QR/preconditioner theorem remain open.
228.  2026-06-03, LS.2g-hw signed-stage global-budget monotonicity bridge:
     no new external source was used.  `LSQRSolve.lean` proves
     `storedQRSignedStageGlobalCompactBudget_nonneg` from the component-budget
     nonnegativity theorem and the finite maximum definition, and proves
     `storedQRSignedStageBudget_mono_on_stages_of_globalCompactBudget` by
     induction on the upper stage index.  The result uses only the scalar
     recurrence, nonnegative stage budgets, `1 <=
     coxHighamActiveRowGrowthFactor m`, and nonnegativity of the finite
     compact-step budget, and is deliberately restricted to indices
     `a <= b <= n`.
229.  2026-06-03, LS.2g-hx horizon-clamped global-product QR budget surface:
     no new external source was used.  `LSQRSolve.lean` defines
     `qrStageHorizonBudget`, proves its on-horizon equality, nonnegativity, and
     global monotonicity from prefix monotonicity, and then proves the
     completed-column global-product source-control and solver wrappers with
     suffix `_of_horizonBudget`.  The proof clamps the stage budget after `n`
     and invokes the older global-monotone wrappers on that clamped sequence,
     while all algorithmic QR-stage hypotheses are transported by
     `qrStageHorizonBudget_eq_of_le`.

230.  2026-06-03, LS.2g-hy horizon-clamped sampled equation (8) assembly:
     no new external source was used.  `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget`.
     The proof is the probability-layer counterpart of LS.2g-hx: it calls the
     stored-QR source-control solver handoff for each sample trace, supplies
     the source certificate with the `_of_horizonBudget` wrapper, and therefore
     removes the samplewise global budget-monotonicity field from the base
     active/prefix global-product equation (8) wrapper.

231.  2026-06-03, LS.2g-hz horizon-clamped `κ∞`/dual-budget sampled
     equation (8) assembly: no new external source was used.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget`.
     The proof derives the samplewise norm-square nonbreakdown margin using
     `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`,
     then calls the LS.2g-hy horizon-clamped base probability wrapper, so the
     `κ∞`/dual-budget sampled route no longer exposes a global budget
     monotonicity field beyond the QR horizon.

232.  2026-06-03, LS.2g-ia horizon-clamped active-max-pivot `κ∞`/dual-budget
     sampled equation (8) assembly: no new external source was used.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`.
     The proof derives the raw pivot-maximality field from the finite active
     selector using `householderActiveMaxPivotColumn_pivot_max`, then calls the
     LS.2g-hz horizon-clamped `κ∞`/dual-budget probability wrapper, so the
     active-pivot sampled route no longer exposes a global budget monotonicity
     field beyond the QR horizon.

233.  2026-06-03, LS.2g-ib horizon-clamped visible row-max active-pivot
     sampled equation (8) assembly: no new external source was used.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget`.
     The proof is local composition: the row-max scalar defect plus the
     displayed stage-budget/row-max comparison are converted into the diagonal
     lower-bound family with the existing row-max bridge, and the result calls
     the LS.2g-ia horizon-clamped active-pivot probability wrapper.

234.  2026-06-03, LS.2g-ic actual-unit horizon visible row-max active-pivot
     sampled equation (8) assembly: no new external source was used.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`.
     The proof derives the sampled and triangular `gammaValid` fields from
     `(s : ℝ) * fp.u < 1` using the local gamma-validity lemmas, then calls the
     LS.2g-ib row-max horizon probability wrapper.

235.  2026-06-03, LS.2g-id actual-unit horizon scalar-comparison active-pivot
     sampled equation (8) assembly: no new external source was used.
     `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`.
     The proof derives sampled validity from `(s : ℝ) * fp.u < 1`, then calls
     the LS.2g-ie explicit-validity horizon scalar-comparison probability
     wrapper.

236.  2026-06-03, LS.2g-ie explicit-validity horizon scalar-comparison
     active-pivot sampled equation (8) assembly: no new external source was
     used. `LeastSquaresSketch.lean` proves
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget`.
     The proof extracts the displayed stage-budget/row-max comparison from
     `storedQRStageRowMaxComparisonDefectBudget <= 0` using
     `storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`,
     then calls the LS.2g-ib horizon row-max probability wrapper.

237.  2026-06-03, LS.2g-if active-pivot diagonal-dominant stored-recurrence
     scalar-comparison route elimination: no external source was used.
     `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_activeMaxPivotChoice` by
     checking the finite active max-pivot selector on the stored sequence from
     `[[3,2],[0,1]]`, then proves
     `not_forall_diagDominant_activeMaxPivot_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The latter theorem reuses the same local witness, with exact
     floating-point arithmetic and constant nonnegative stage budget `3`, to
     rule out deriving the scalar stage-budget/row-max comparison from stored
     recurrence, signed-alpha/source-denominator/actual-unit facts, local
     diagonal dominance, and active-pivot policy alone.

238.  2026-06-03, LS.2g-ig compact-product active-pivot diagonal-dominant
     stored-recurrence scalar-comparison route elimination: no external source
     was used.  `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_rhs_step`,
     `storedDiagDominantComparisonCounterexample_compactSequenceRelativeBudget_eq_zero`,
     `storedDiagDominantComparisonCounterexample_compactSequenceProductBudget_lt_one`,
     and
     `not_forall_diagDominant_activeMaxPivot_product_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof pairs the same stored matrix witness with a zero RHS trace.  In
     exact arithmetic the compact relative budget is zero, so the finite
     compact-product budget is below one, but the constant nonnegative stage
     budget `3` still leaves the scalar comparison defect positive.

239.  2026-06-03, LS.2g-ih finite-max active-pivot diagonal-dominant
     stored-recurrence scalar-comparison route elimination: no external source
     was used.  `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_finiteMaxSmallness` and
     `not_forall_diagDominant_activeMaxPivot_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS stored witness from LS.2g-ig.  Because
     the compact relative budget is zero, the canonical finite-max
     compact-product scalar reduces to `0 < 1`; the constant nonnegative stage
     budget `3` still leaves the scalar comparison defect positive.

240.  2026-06-03, LS.2g-ii signed-stage global-budget finite-max active-pivot
     diagonal-dominant stored-recurrence scalar-comparison route elimination:
     no external source was used.  `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_globalBudgetStageBudget_nonneg`,
     `storedDiagDominantComparisonCounterexample_globalCompactBudget_eq_zero`,
     `storedDiagDominantComparisonCounterexample_globalCompactBudget_recurrence`,
     `storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_globalBudgetStageBudget`,
     and
     `not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS stored witness and changes only the
     stage-budget trace to `0, 3, 10, ...`.  Exact arithmetic makes every
     signed global compact-update budget vanish, and the local bound
     `coxHighamActiveRowGrowthFactor 2 <= 3` supplies the nontrivial recurrence
     step; the stage-one comparison defect remains positive.

241.  2026-06-03, LS.2g-ij row-max-granted signed-stage global-budget
     finite-max active-pivot diagonal-dominant stored-recurrence
     scalar-comparison route elimination: no external source was used.
     `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_rowMaxDiagDefectBudget_nonpos`
     and
     `not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS signed-stage witness from LS.2g-ii.
     Local diagonal dominance packages the finite row-max/diagonal defect
     scalar through `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant`;
     the same nonconstant budget `0, 3, 10, ...` keeps the stage-one
     comparison defect positive.

242.  2026-06-03, LS.2g-ik determinant- and row-max-granted signed-stage
     global-budget finite-max active-pivot diagonal-dominant stored-recurrence
     scalar-comparison route elimination: no external source was used.
     `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_leadingBlock_det_ne_zero`
     and
     `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS signed-stage witness from LS.2g-ij.
     The displayed leading blocks are computed directly: the stage-zero
     determinant is `3`, and the stage-one stored determinant is `-3`; the
     same nonconstant budget `0, 3, 10, ...` keeps the stage-one comparison
     defect positive.

243.  2026-06-03, LS.2g-il conditioning- and row-max-granted signed-stage
     global-budget finite-max active-pivot diagonal-dominant stored-recurrence
     scalar-comparison route elimination: no external source was used.
     `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_compactComponentBudget_eq_zero`,
     `storedDiagDominantComparisonCounterexampleKappaBudget`,
     `storedDiagDominantComparisonCounterexampleKappaNormSqBudget`,
     `storedDiagDominantComparisonCounterexample_kappaBudget_le`,
     `storedDiagDominantComparisonCounterexample_kappaNormSqBudget_pos`,
     `storedDiagDominantComparisonCounterexample_kappaNormSqBudget`,
     `storedDiagDominantComparisonCounterexample_dualBudget`, and
     `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS signed-stage witness from LS.2g-ik.
     Its exact compact component budget is zero, so a noncomputable local
     `kappaInf` budget and a positive self-norm `K` budget chosen as the exact
     expression plus one satisfy the local conditioning and dual compact-budget
     branch while the stage-one comparison defect remains positive.

244.  2026-06-03, LS.2g-im final-surface initial/global-product
     conditioning-granted scalar-comparison route elimination: no external
     source was used.  `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexampleFinalSurfaceStageBudget`,
     `storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_nonneg`,
     `storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_mono`,
     `storedDiagDominantComparisonCounterexample_finalSurface_init`,
     `storedDiagDominantComparisonCounterexample_finalSurface_initBlock`,
     `storedDiagDominantComparisonCounterexample_finalSurface_globalCompactBudget_recurrence`,
     `storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_finalSurfaceStageBudget`,
     and
     `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_globalProduct_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS signed-stage witness from LS.2g-il
     but changes the stage budget to `3, 10, 30, ...`, which satisfies the
     initial full-block and displayed row-budget fields as well as
     nonnegativity, monotonicity, the signed-stage global compact-budget
     recurrence, and global compact-product smallness.  The displayed
     strict-upper row maximum at stage one is still `2`, so the comparison
     defect remains positive.

245.  2026-06-03, LS.2g-in final-surface source-denominator rational-gamma
     scalar-comparison route elimination: no external source was used.
     `LSQRSolve.lean` proves
     `storedDiagDominantComparisonCounterexample_finalSurface_sourceDenURationalGammaCanonicalSmallness`
     and
     `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_sourceDenURationalGammaCanonical_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
     The proof reuses the exact/zero-RHS final-surface witness from LS.2g-im
     and sets `Ucap = 0`; under exact arithmetic the rational-gamma and
     Householder-factor cap terms collapse to zero, so the displayed
     source-denominator scalar smallness holds while the stage-one comparison
     defect remains positive.

246.  2026-06-03, LS.2g-io horizon-clamped source-denominator
     scalar-comparison handoff: no external source was used.  `LSQRSolve.lean`
     proves `storedQRStageRowMaxComparisonDefectBudget_nonpos_of_horizonBudget`
     and
     `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget`.
     `LeastSquaresSketch.lean` proves the explicit-cap, actual-unit, and
     stored-lower sampled horizon siblings:
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget`,
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`,
     and
     `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`.
     The proof is a local bookkeeping reduction: comparison-defect
     nonpositivity is unaffected by clamping after `n`, and the signed-stage
     compact recurrence supplies the global monotonicity needed by the older
     source-denominator handoff.

247.  2026-06-04, A3.4-FHT one-stage exact output formula: no external source
     was used.  `Preconditioning.lean` proves `fhtStagePairs_nodup`,
     `fhtPairScheduleExact_apply_of_forall_not_mem`,
     `fhtPairScheduleExact_apply_pair_of_mem_stage_list`,
     `fhtStagePairs_pairScheduleExact_apply_pair_of_mem`,
     `fhtStagePairs_pairScheduleExact_apply_fst_of_mem`,
     `fhtStagePairs_pairScheduleExact_apply_snd_of_mem`, and the
     Sylvester-stage wrappers
     `fhtSylvesterStageScheduleExact_apply_pair_of_mem`,
     `fhtSylvesterStageScheduleExact_apply_fst_of_mem`, and
     `fhtSylvesterStageScheduleExact_apply_snd_of_mem`.  The proof is local
     finite-list reasoning: the generated stage list is duplicate-free, pairs
     distinct from a target pair do not touch the target coordinates, and the
     ordered stage schedule therefore returns the simultaneous butterfly values
     on every generated pair.  The remaining source item is the induction
     identifying the stage recurrence over `List.range p` with
     `sylvesterHadamardParity`.

248.  2026-06-04, A3.4-FHT one-stage coordinate formulas: no external source
     was used.  `Preconditioning.lean` proves `fhtStagePairs_mem_lower_mk`,
     `fhtSylvesterStagePairs_mem_lower_mk`,
     `fhtSylvesterStagePairs_mem_upper_mk`,
     `fhtSylvesterStageScheduleExact_apply_lower_mk`, and
     `fhtSylvesterStageScheduleExact_apply_upper_mk`.  These theorems
     instantiate the closed one-stage pair-output formula at explicit
     lower/upper coordinates, keeping the required upper-bound and block-modulus
     hypotheses visible.  The power-of-two coverage wrappers are now closed in
     the next note; the remaining source item is the parity recurrence induction
     against `sylvesterHadamardParity`.

249.  2026-06-04, A3.4-FHT power-of-two coordinate coverage wrappers: no
     external source was used.  `Preconditioning.lean` proves the reusable
     integer lemmas `nat_add_stride_lt_of_mod_lt_of_dvd` and
     `nat_sub_stride_mod_two_stride_lt_of_mod_ge`, the power-of-two
     divisibility lemma `two_mul_two_pow_dvd_two_pow_of_lt`, and the
     stage-specific coverage wrappers
     `fhtSylvesterStage_lower_partner_lt_of_mod_lt`,
     `fhtSylvesterStage_upper_value_le_of_mod_ge`, and
     `fhtSylvesterStage_upper_partner_mod_lt_of_mod_ge`.  The one-stage
     formulas `fhtSylvesterStageScheduleExact_apply_lower_of_mod_lt` and
     `fhtSylvesterStageScheduleExact_apply_upper_of_mod_ge` now discharge the
     manual bound/modulus hypotheses from the lower/upper block tests.  The
     stage-bit wrappers are closed in the next note; the remaining source item
     is the local parity recurrence induction against
     `sylvesterHadamardParity`; no probability-law or probability-construction
     source is involved.

250.  2026-06-04, A3.4-FHT block-test stage-bit bridge: no external
     source was used.  `Preconditioning.lean` proves
     `nat_testBit_eq_false_of_mod_two_mul_two_pow_lt` and
     `nat_testBit_eq_true_of_two_pow_le_mod_two_mul_two_pow`, turning the
     lower/upper residue tests in a `2^r` stride block into exact statements
     about `Nat.testBit a r`.  The wrappers
     `fhtSylvesterStage_testBit_eq_false_of_mod_lt` and
     `fhtSylvesterStage_testBit_eq_true_of_mod_ge` specialize the same facts
     to generated Sylvester-stage coordinates.  The generated-partner
     stage-bit bridge is closed in the next note.  The remaining source item is
     the local parity recurrence induction inside the definition of
     `sylvesterHadamardParity`; no probability-law or probability-construction
     source is involved.

251.  2026-06-04, A3.4-FHT generated-partner stage-bit bridge: no external
     source was used.  `Preconditioning.lean` proves
     `fhtSylvesterStage_upper_partner_testBit_eq_true_of_mod_lt` and
     `fhtSylvesterStage_lower_partner_testBit_eq_false_of_mod_ge`, turning the
     lower/upper residue tests into exact bit facts for the generated partner
     coordinates `i + 2^r` and `i - 2^r`.  These local integer lemmas will be
     used to rewrite the one-stage lower/upper coordinate formulas as the
     Sylvester/Walsh parity recurrence.  The remaining source item is the local
     parity recurrence induction inside the definition of
     `sylvesterHadamardParity`; no probability-law or probability-construction
     source is involved.

252.  2026-06-04, A3.4-FHT parity-count sign recurrence: no external source
     was used.  `Preconditioning.lean` proves
     `sylvesterHadamardSignPattern_eq_or_neg_of_parityWeight_eq_add_bool` and
     the wrappers `sylvesterHadamardSignPattern_eq_of_parityWeight_eq` and
     `sylvesterHadamardSignPattern_neg_of_parityWeight_eq_add_one`.  These
     theorems turn an exact partner-row parity-count identity into the
     corresponding same-sign or negated-sign Sylvester/Walsh table entry.  The
     generated-partner non-stage-bit agreement and concrete lower/upper
     instantiations are closed in note 254; the remaining source item is the
     stage recurrence induction inside `sylvesterHadamardParity`.  No
     probability-law or probability-construction source is involved.

253.  2026-06-04, A3.4-FHT abstract finite-sum bit-toggle recurrence: no
     external source was used.  The local Lean theorems
     `sylvesterHadamardParityWeight_partner_eq_add_stage_of_bits` and
     `sylvesterHadamardSignPattern_partner_eq_or_neg_of_stage_bit` split the
     realization bottleneck into an abstract finite-sum/sign recurrence, now
     closed; the concrete Nat-bit/generated-partner instantiation is closed in
     note 254.  Exact Rademacher and uniform-row
     laws remain unchanged by convention.

254.  2026-06-04, A3.4-FHT concrete generated-partner bit recurrences: no
     external source was used.  The local Lean theorems
     `nat_testBit_add_two_pow_eq_of_testBit_eq_false_of_ne`,
     `two_pow_le_of_testBit_eq_true`,
     `nat_testBit_sub_two_pow_eq_of_testBit_eq_true_of_ne`,
     `fhtSylvesterStage_upper_partner_testBit_eq_of_ne_of_mod_lt`,
     `fhtSylvesterStage_lower_partner_testBit_eq_of_ne_of_mod_ge`,
     `sylvesterHadamardParityWeight_upper_partner_eq_add_stage_of_mod_lt`,
     `sylvesterHadamardSignPattern_upper_partner_eq_or_neg_of_mod_lt`,
     `sylvesterHadamardParityWeight_upper_eq_lower_partner_add_stage_of_mod_ge`,
     and `sylvesterHadamardSignPattern_upper_eq_or_neg_lower_partner_of_mod_ge`
     close the generated `i + 2^stage` and `i - 2^stage` instantiation of the
     finite-sum/sign recurrence.  The stage-list append/range-succ induction
     spine is closed in note 255, and the partial recurrence/final realization
     induction are closed in notes 257 and 258.  No probability-law or
     probability-construction source is involved.

255.  2026-06-04, A3.4-FHT stage-list append/range-succ induction spine: no
     external source was used.  The local Lean theorems
     `fhtSylvesterStageScheduleListExact_append`,
     `flFhtSylvesterStageScheduleList_append`,
     `fhtSylvesterStageScheduleListPropagatedErrorBudget_append`,
     `fhtSylvesterStageScheduleListExact_range_succ`,
     `flFhtSylvesterStageScheduleList_range_succ`, and
     `fhtSylvesterStageScheduleListPropagatedErrorBudget_range_succ` prove that
     exact generated-stage schedules, rounded schedules, and propagated budgets
     compose over stage-list append and advance from `List.range stage` to
     `List.range (stage+1)` by applying the current stage.  This is pure local
     list recursion over the already defined schedule objects.  The
     partial-transform endpoints are closed in note 256, and the one-stage
     recurrence/final realization induction are closed in notes 257 and 258.
     Exact Rademacher and uniform-row laws remain mathematical inputs.

256.  2026-06-04, A3.4-FHT partial Sylvester/Walsh transform anchors: no
     external source was used.  The local Lean definitions
     `sylvesterHadamardPartialParity`, `sylvesterHadamardPartialSignPattern`,
     and `sylvesterHadamardPartialUnscaledApply` define the finite partial table
     for the first `t` generated stages: quotient-block support
     `j / 2^t = i / 2^t` and sign bits only from coordinates `< t`.
     `sylvesterHadamardPartialSignPattern_zero` and
     `sylvesterHadamardPartialUnscaledApply_zero` prove that depth zero is the
     identity transform, while `sylvesterHadamardPartialSignPattern_full` and
     `sylvesterHadamardPartialUnscaledApply_full` prove that depth `p` is the
     full concrete Sylvester/Walsh bit-parity transform.  The one-stage
     recurrence from partial depth `stage` to `stage+1` is closed in note 257
     and the final realization induction is closed in note 258; exact sampling
     laws remain mathematical inputs.

257.  2026-06-04, A3.4-FHT one-stage partial Sylvester/Walsh recurrence: no
     external source was used.  The local Lean theorems
     `nat_div_stride_eq_two_mul_block_div_add_mod_div`,
     `nat_div_stride_eq_two_mul_block_div_of_mod_lt`,
     `nat_div_stride_eq_two_mul_block_div_add_one_of_mod_ge`,
     `nat_add_stride_div_stride_eq_two_mul_block_div_add_one_of_mod_lt`,
     `nat_add_stride_div_two_stride_eq_of_mod_lt`,
     `nat_sub_stride_div_stride_eq_two_mul_block_div_of_mod_ge`,
     `nat_sub_stride_div_two_stride_eq_of_mod_ge`,
     `nat_div_two_mul_stride_eq_div_stride_div_two`, and
     `nat_div_two_stride_eq_of_div_stride_eq` split each
     `2^(stage+1)` quotient block into the two `2^stage` half-blocks used by a
     generated FHT stage.  The partial-sign and partner-sign recurrences
     `sylvesterHadamardPartialParityWeight_succ`,
     `sylvesterHadamardPartialSignPattern_succ_eq_or_neg`,
     `sylvesterHadamardPartialSignPattern_succ_eq_of_stage_bit_false`,
     `sylvesterHadamardPartialSignPattern_succ_eq_or_neg_of_stage_bit_true`,
     `sylvesterHadamardPartialParityWeight_eq_of_bits`,
     `sylvesterHadamardPartialSignPattern_eq_of_bits`,
     `sylvesterHadamardPartialSignPattern_upper_partner_eq_of_mod_lt`, and
     `sylvesterHadamardPartialSignPattern_upper_eq_lower_partner_of_mod_ge`
     identify the signs on the lower and upper half-blocks.  The split
     theorems `sylvesterHadamardPartialUnscaledApply_succ_lower` and
     `sylvesterHadamardPartialUnscaledApply_succ_upper` combine those facts
     with the closed lower/upper one-stage coordinate formulas, and
     `fhtSylvesterStageScheduleExact_partialUnscaledApply_eq_succ` proves
     `Stage_stage(partial_stage x) = partial_(stage+1) x`.  This is exact
     deterministic integer/FHT arithmetic and uses no probability-law or
     probability-construction approximation.

258.  2026-06-04, A3.4-FHT final generated Sylvester/Walsh realization: no
     external source was used.  The local Lean theorem
     `fhtSylvesterStageScheduleListExact_range_eq_partialUnscaledApply`
     inducts over `List.range t` and proves that the first `t` generated stages
     equal the depth-`t` partial transform for every `t <= p`.  At `t=p`,
     `sylvesterHadamardPartialUnscaledApply_full` gives the full concrete
     Sylvester/Walsh table, yielding
     `fhtSylvesterScheduleRealizesSignPattern_generated`.  The unconditional
     bridges
     `fhtScaledSylvesterScheduleMatrixExact_eq_sylvesterHadamardScaledMatrixApply`
     and `fhtScaledSylvesterScheduleMatrixExact_signed_eq_preconditionRows`
     remove the earlier realization hypothesis from the scaled bit-parity table
     and signed `H D U` preconditioner equalities.  Remaining source-ledger work
     after this exact realization is implementation-specific layout/storage/
     overwrite/copy certificates beyond the functional generated-FHT preconditioner path, and the non-SRHT/QR/SVD/sign-storage/denominator routine
     families already listed above.

259.  2026-06-04, A3.4-FHT fast generated-FHT preconditioner path: no external
     source was used.  The local Lean theorem
     `fhtScaledSylvesterScheduleMatrixExact_diag_eq_matMul_diag` identifies the
     exact generated scaled FHT applied to `diag(sign)` with the ideal scaled
     Sylvester/Walsh `H D_sign` matrix.  The constructor
     `ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule` packages the
     rounded generated FHT schedule applied to a computed diagonal sign matrix
     as a `ComputedPreconditioner`, with
     `ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule_entry_error_bound`
     exposing the entrywise budget.  The wrappers
     `signedHadamardSylvesterFhtSchedulePreconditioner` and
     `signedHadamardSylvesterFhtScheduleStoredSignPreconditioner`, together
     with the probability-one theorems
     `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
     and
     `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`,
     feed this fast preconditioner into the existing exact-law computed-left
     SRHT perturbation event.  The Rademacher and uniform-row laws remain
     exact; only non-probability storage/arithmetic is charged.

260.  2026-06-04, A3.4-FHT stored add-zero writeback/copy path: no external
     source was used.  The local Lean definitions
     `flFhtPairUpdateStoredAddZeroRight`,
     `flFhtPairScheduleStoredAddZeroRight`,
     `flFhtSylvesterScheduleStoredAddZeroRight`, and the scaled/matrix
     variants model the functional generated-FHT pair schedule followed by
     `fl_add(output,0)` storage at every output coordinate after each pair
     update.  The proof uses the existing pair-update propagation theorem plus
     `FPModel.model_add` for the copy/writeback radius, then composes the
     result through the rounded sqrt-inverse scale,
     `ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNatStoredAddZeroRight_entry_error_bound`,
     `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight_entry_error_bound`,
     and the exact-law computed-left event wrappers.  The remaining source
     obligation is only for concrete array-layout, aliasing, in-place
     overwrite, vectorized, or storage routines whose behavior differs from
     this modeled add-zero writeback path.

261.  2026-06-04, A3.4-FHT modified-coordinate add-zero writeback/copy path:
     no external source was used.  The local Lean definitions
     `flFhtPairUpdateModifiedStoredAddZeroRight`,
     `flFhtPairScheduleModifiedStoredAddZeroRight`,
     `flFhtSylvesterScheduleModifiedStoredAddZeroRight`, and the scaled/matrix
     variants model the same generated-FHT pair schedule, but write only the
     two modified butterfly outputs through `fl_add(output,0)` after each pair
     update.  The propagated budget adds
     `fp.u * |flFhtPairUpdate fp p q xhat i|` only under the indicator
     `i = p ∨ i = q` and adds zero copy radius on untouched coordinates.  The
     proof composes this local one-pair theorem through the rounded
     sqrt-inverse scale,
     `ComputedMatrix.flScaledFhtSylvesterScheduleColumnsSqrtInvNatModifiedStoredAddZeroRight_entry_error_bound`,
     `ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight_entry_error_bound`,
     and the exact-law computed-left event wrappers.  Remaining source work is
     restricted to concrete array-layout, aliasing, in-place overwrite,
     vectorized, or storage routines whose behavior differs from this
     modified-coordinate writeback model.

262.  2026-06-04, A3.1fp-projector-stored-basis add-zero matrix storage:
     no external source was used.  The proof is a direct local application of
     the repository `FPModel.model_add` primitive to each basis/singular-vector
     table entry, yielding `ComputedMatrix.flAddZeroRight_entry_error_bound`
     with radius `fp.u * |Q i j|`.  The projector theorem
     `ComputedPreconditioner.flBasisColumnProjectorStoredBasisAddZeroRight_entry_error_bound`
     then instantiates the previously formalized computed-projector budget
     `flBasisColumnProjectorEntryErrorBudget`; sampling probabilities and laws
     remain exact mathematical inputs.

263.  2026-06-04, A3.1fp-projector-stored-basis multiply-one and subtract-zero
     matrix storage: no external source was used.  The proofs are direct local
     applications of `FPModel.model_mul` and `FPModel.model_sub` to each
     basis/singular-vector table entry, yielding
     `ComputedMatrix.flMulOne_entry_error_bound` and
     `ComputedMatrix.flSubZeroRight_entry_error_bound` with radius
     `fp.u * |Q i j|`.  The projector theorems
     `ComputedPreconditioner.flBasisColumnProjectorStoredBasisMulOne_entry_error_bound`
     and
     `ComputedPreconditioner.flBasisColumnProjectorStoredBasisSubZeroRight_entry_error_bound`
     instantiate the existing computed-projector budget; sampling probabilities
     and laws remain exact mathematical inputs.

264.  2026-06-04, A3.1fp uniform-row split-square-root denominator: no external
     source was used.  The proof is a direct local floating-point composition:
     apply `FPModel.model_sqrt` to `s` and `m`, apply `FPModel.model_div` to the
     two rounded square-root values, use `Real.sqrt_div` for the exact reference
     \(d=\sqrt{s/m}\), and bound
     \[
       \left|\frac{(1+\delta_s)(1+\delta_d)}{1+\delta_m}-1\right|
       \le \frac{3u+u^2}{1-u}.
     \]
     This yields `ComputedUniformRowScaleDen.flSqrtDivSqrt` with denominator
     radius `uniformRowSampleScaleDen s * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u))`;
     the exact uniform row law remains an input and receives no FP
     probability-construction term.

265.  2026-06-04, A3.1fp FHT one-pair multiply-one/subtract-zero writeback:
     no external source was used.  The proof reuses the local rounded FHT pair
     update theorem `flFhtPairUpdate_propagated_error_bound`, the local copy
     certificates `ComputedVector.flMulOne_entry_error_bound` and
     `ComputedVector.flSubZeroRight_entry_error_bound`, nonnegativity of the
     existing pair-update budget, and the triangle inequality.  It yields
     `flFhtPairUpdateStoredMulOne_propagated_error_bound` and
     `flFhtPairUpdateStoredSubZeroRight_propagated_error_bound`, with added
     one-pair copy radius `fp.u * |flFhtPairUpdate fp p q xhat i|`.  The exact
     Rademacher and uniform-row laws are unchanged; schedule/scaling/matrix and
     computed-preconditioner lifting for these writeback forms remains an
     implementation-specific Lean target.

266.  2026-06-04, A3.1fp FHT ordered schedules with multiply-one/subtract-zero
     writeback: no external source was used.  The proof is the same local list
     induction pattern as `flFhtPairScheduleStoredAddZeroRight_propagated_error_bound`,
     but with the one-pair step supplied by
     `flFhtPairUpdateStoredMulOne_propagated_error_bound` or
     `flFhtPairUpdateStoredSubZeroRight_propagated_error_bound`.  The resulting
     schedule theorems are `flFhtPairScheduleStoredMulOne_propagated_error_bound`
     and `flFhtPairScheduleStoredSubZeroRight_propagated_error_bound`; their
     budget nonnegativity lemmas compose the corresponding one-pair
     nonnegativity facts.  The exact probability laws are unchanged, and
     generated-Sylvester scaling/matrix/preconditioner lifts remain separate
     implementation targets.
267.  2026-06-04, A3.1fp generated-FHT multiply-one/subtract-zero writeback
     lifts: no external source was used.  The proof reuses local scaled-FHT
     wrappers, the generated Sylvester/Walsh schedule bridge, `ComputedMatrix`
     packaging, `ComputedPreconditioner.ofComputedMatrix`-style signed-Hadamard
     constructors, and the existing
     `signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one`
     exact-law event transport.  The new names close the modeled all-coordinate
     `fl_mul(output,1)` and `fl_sub(output,0)` generated-FHT paths without
     changing the exact Rademacher or uniform-row sampling laws.
268.  2026-06-04, A3.1fp modified-coordinate generated-FHT
     multiply-one/subtract-zero writeback lifts: no external source was used.
     The proof reuses the local modified-coordinate add-zero route, the
     one-pair copy certificates `ComputedVector.flMulOne_entry_error_bound` and
     `ComputedVector.flSubZeroRight_entry_error_bound`, the ordered-schedule
     induction pattern, the local scalar final-scale helper
     `flScaleValue_error_bound`, `ComputedMatrix` packaging, the
     generated-Sylvester signed-Hadamard computed-preconditioner bridge, and the
     existing exact-law computed-left event transport.  The new names close the
     modeled routine that writes only the modified butterfly outputs through
     `fl_mul(output,1)` or `fl_sub(output,0)`; exact Rademacher and uniform-row
     sampling laws remain unchanged.

269.  2026-06-04, A3.1fp uniform-row square-root-times-reciprocal denominator:
     no external source was used.  The proof is a direct local
     floating-point composition: apply `FPModel.model_sqrt` to `s` and `m`,
     apply `FPModel.model_div` to compute the reciprocal of the rounded
     `sqrt(m)`, apply `FPModel.model_mul` for the final product with the rounded
     `sqrt(s)`, use `Real.sqrt_div` for the exact reference
     \(d=\sqrt{s/m}\), and bound
     \[
       \left|
         \frac{(1+\delta_s)(1+\delta_i)(1+\delta_p)}{1+\delta_m}-1
       \right|
       \le \frac{4u+3u^2+u^3}{1-u}.
     \]
     This yields `ComputedUniformRowScaleDen.flSqrtMulInvSqrt` with denominator
     radius
     `uniformRowSampleScaleDen s * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u))`;
     the exact uniform row law remains an input and receives no FP
     probability-construction term.

270.  2026-06-04, A3.1fp certified QR/SVD/basis projector handoff: no
     external source was used.  The proof is a local certificate transfer:
     `ComputedMatrix.ofEntrywiseBound` packages a routine-produced basis table
     `Qhat` and entrywise radius `E`; `fl_basisColumnProjector_total_error_bound`
     gives the rounded-projector and two-use basis perturbation radius; and
     `fl_preconditionElementsWithComputed_total_error_bound` plugs the resulting
     left/right `ComputedPreconditioner` objects into two-sided Algorithm 3
     preprocessing.  This yields
     `fl_basisColumnProjector_of_certifiedBasis_entry_error_bound`,
     `ComputedPreconditioner.flBasisColumnProjectorOfCertifiedBasis_entry_error_bound`,
     and `fl_preconditionElementsWithCertifiedBasisProjectors_total_error_bound`.
     The actual QR/SVD/singular-vector generation theorem that proves a
     concrete `|Qhat-Q| <= E` certificate remains a not-proved ledger
     obligation; sampling probabilities and laws remain exact mathematical
     inputs.

271.  2026-06-04, A3.1fp Frobenius-certified QR/SVD/basis projector handoff:
     no external source was used.  The proof is a local norm-to-entrywise
     certificate transfer: `ComputedMatrix.ofFrobeniusBound` uses
     `abs_entry_le_frobNorm` and `frobNormRect_eq_frobNormFn` to turn an
     upstream routine certificate `||Qhat-Q||_F <= eta` into a uniform
     entrywise radius; `fl_basisColumnProjector_total_error_bound` then gives
     the rounded-projector and two-use basis perturbation radius; and
     `fl_preconditionElementsWithComputed_total_error_bound` plugs the
     resulting left/right `ComputedPreconditioner` objects into two-sided
     Algorithm 3 preprocessing.  This yields
     `fl_basisColumnProjector_of_frobeniusCertifiedBasis_entry_error_bound`,
     `ComputedPreconditioner.flBasisColumnProjectorOfFrobeniusCertifiedBasis_entry_error_bound`,
     and
     `fl_preconditionElementsWithFrobeniusCertifiedBasisProjectors_total_error_bound`.
     The actual QR/SVD/singular-vector generation theorem that proves a
     concrete Frobenius radius remains a not-proved ledger obligation;
     sampling probabilities and laws remain exact mathematical inputs.

272.  2026-06-04, A3.1fp operator-certified QR/SVD/basis projector handoff:
     no external source was used.  The proof is a local vector-action
     certificate transfer: `ComputedMatrix.ofRectOpNorm2Bound` tests the
     `rectOpNorm2Le (Qhat-Q) eta` certificate on standard basis vectors and
     uses coordinate domination by Euclidean norm to obtain a uniform
     entrywise radius.  The existing
     `fl_basisColumnProjector_total_error_bound` then gives the
     rounded-projector and two-use basis perturbation radius, and
     `fl_preconditionElementsWithComputed_total_error_bound` plugs the
     resulting left/right `ComputedPreconditioner` objects into two-sided
     Algorithm 3 preprocessing.  This yields
     `fl_basisColumnProjector_of_opNormCertifiedBasis_entry_error_bound`,
     `ComputedPreconditioner.flBasisColumnProjectorOfOpNormCertifiedBasis_entry_error_bound`,
     and
     `fl_preconditionElementsWithOpNormCertifiedBasisProjectors_total_error_bound`.
     The actual QR/SVD/singular-vector or Davis-Kahan-style routine that
     proves a concrete operator radius remains a not-proved ledger obligation;
     sampling probabilities and laws remain exact mathematical inputs.

273.  2026-06-04, A3.1fp columnwise-certified QR/SVD/basis projector handoff:
     no external source was used.  The proof is a local column-vector
     certificate transfer: `ComputedMatrix.ofColumnVecNorm2Bound` applies
     coordinate domination by Euclidean norm to each certified column
     `||Qhat(:,a)-Q(:,a)||_2 <= eta_a`, obtaining the entrywise radius
     `eta_a` for that column.  The existing
     `fl_basisColumnProjector_total_error_bound` then gives the
     rounded-projector and two-use basis perturbation radius, and
     `fl_preconditionElementsWithComputed_total_error_bound` plugs the
     resulting left/right `ComputedPreconditioner` objects into two-sided
     Algorithm 3 preprocessing.  This yields
     `fl_basisColumnProjector_of_columnwiseCertifiedBasis_entry_error_bound`,
     `ComputedPreconditioner.flBasisColumnProjectorOfColumnwiseCertifiedBasis_entry_error_bound`,
     and
     `fl_preconditionElementsWithColumnwiseCertifiedBasisProjectors_total_error_bound`.
     The actual QR/SVD/singular-vector routine that proves concrete per-column
     vector radii remains a not-proved ledger obligation; sampling
     probabilities and laws remain exact mathematical inputs.

274.  2026-06-04, A3.1fp generated-then-stored QR/SVD/basis projector handoff:
     no external source was used.  The proof is a local certificate-composition
     transfer for implementation paths where a routine first returns `Qraw`
     with entrywise radius `E` against the exact analysis basis `Q`, and the
     algorithm then stores or copies `Qraw` as the actual table `Qstore` with
     radius `C`.  `ComputedMatrix.ofEntrywiseBoundThenStorage` uses the
     triangle inequality to build a `ComputedMatrix` for `Qstore` with combined
     radius `C + E`; `ComputedMatrix.ofEntrywiseBoundStoredMulOne`,
     `ComputedMatrix.ofEntrywiseBoundStoredAddZeroRight`, and
     `ComputedMatrix.ofEntrywiseBoundStoredSubZeroRight` instantiate `C_ij =
     fp.u * |Qraw_ij|` for the three modeled rounded-copy paths.  The existing
     `fl_basisColumnProjector_total_error_bound` then gives
     `fl_basisColumnProjector_of_certifiedStoredBasis_entry_error_bound` with
     the displayed projector radius, and
     `fl_preconditionElementsWithComputed_total_error_bound` plugs the
     resulting left/right `ComputedPreconditioner` objects into two-sided
     Algorithm 3 preprocessing through
     `fl_preconditionElementsWithCertifiedStoredBasisProjectors_total_error_bound`.
     The actual QR/SVD/singular-vector routine that proves the raw `Qraw,E`
     certificate remains a not-proved ledger obligation; sampling probabilities
     and laws remain exact mathematical inputs.

275.  2026-06-04, A3.1fp normwise generated-then-stored QR/SVD/basis projector
     handoff: no external source was used.  The proof is a local composition
     of the already formalized norm-to-entrywise certificate transfers with
     the storage/copy triangle inequality.  `ComputedMatrix.ofFrobeniusBoundThenStorage`
     uses `abs_entry_le_frobNorm` and `frobNormRect_eq_frobNormFn` through
     `ComputedMatrix.ofFrobeniusBound`, then adds the storage radius `C`.
     `ComputedMatrix.ofColumnVecNorm2BoundThenStorage` uses coordinate
     domination by each column's Euclidean norm, then adds `C`.
     `ComputedMatrix.ofRectOpNorm2BoundThenStorage` tests `rectOpNorm2Le`
     on standard basis vectors through `ComputedMatrix.ofRectOpNorm2Bound`,
     then adds `C`.  The projector theorems
     `fl_basisColumnProjector_of_frobeniusCertifiedStoredBasis_entry_error_bound`,
     `fl_basisColumnProjector_of_columnwiseCertifiedStoredBasis_entry_error_bound`,
     and `fl_basisColumnProjector_of_opNormCertifiedStoredBasis_entry_error_bound`
     are then direct applications of the existing
     `fl_basisColumnProjector_entry_error_budget_bound` with the stored-table
     combined radii `C + eta`, `C + eta_a`, and `C + eta`.  Concrete QR/SVD,
     The wrappers
     `ComputedPreconditioner.flBasisColumnProjectorOfFrobeniusCertifiedStoredBasis`,
     `ComputedPreconditioner.flBasisColumnProjectorOfColumnwiseCertifiedStoredBasis`,
     and `ComputedPreconditioner.flBasisColumnProjectorOfOpNormCertifiedStoredBasis`
     package these projectors as computed preconditioners, and
     `fl_preconditionElementsWithFrobeniusCertifiedStoredBasisProjectors_total_error_bound`,
     `fl_preconditionElementsWithColumnwiseCertifiedStoredBasisProjectors_total_error_bound`,
     and `fl_preconditionElementsWithOpNormCertifiedStoredBasisProjectors_total_error_bound`
     compose them with the existing two-sided preprocessing theorem.  Concrete
     QR/SVD, singular-vector, orthonormal-basis, or Davis-Kahan-style routines
     that produce the raw normwise certificates remain not-proved obligations;
     sampling probabilities and laws remain exact mathematical inputs.

276.  2026-06-04, A3.1fp normwise-storage QR/SVD/basis projector handoff:
     no external source was used.  The proof is a local norm-to-entrywise
     conversion layer for storage certificates.  `ComputedMatrix.ofEntrywiseBoundThenFrobeniusStorage`
     converts `||Astore-Araw||_F <= sigma` through the already formalized
     Frobenius entry bound and composes it with a raw entrywise certificate.
     `ComputedMatrix.ofFrobeniusBoundThenFrobeniusStorage`,
     `ComputedMatrix.ofColumnVecNorm2BoundThenColumnVecNorm2Storage`, and
     `ComputedMatrix.ofRectOpNorm2BoundThenRectOpNorm2Storage` do the same for
     Frobenius/Frobenius, columnwise/columnwise, and operator/operator raw-plus-storage
     certificates.  The projector theorems
     `fl_basisColumnProjector_of_frobeniusCertifiedFrobeniusStoredBasis_entry_error_bound`,
     `fl_basisColumnProjector_of_columnwiseCertifiedColumnwiseStoredBasis_entry_error_bound`,
     and `fl_basisColumnProjector_of_opNormCertifiedOpNormStoredBasis_entry_error_bound`
     are direct applications of `fl_basisColumnProjector_entry_error_budget_bound`
     with storage radii `sigma`, `sigma_a`, or `sigma`.  Concrete QR/SVD,
     singular-vector, orthonormal-basis, or Davis-Kahan-style routines that
     produce the raw generation and storage norm certificates remain not-proved
     obligations; sampling probabilities and laws remain exact mathematical inputs.

277.  2026-06-04, A3.1fp right-orthogonal QR/SVD/basis projector handoff:
     no external source was used.  The proof is local finite-dimensional
     matrix algebra: `basisColumnProjector_matMulRectRight_orthogonal` expands
     `(Q O)(Q O)^T`, reorders the finite sums, and uses the row-orthonormality
     of the exact orthogonal matrix `O` to obtain `Q Q^T`.  The generic theorem
     `fl_basisColumnProjector_entry_error_budget_bound_rightOrthogonalReference`
     then rewrites the existing computed-projector budget from the rotated
     reference `Q O` to the analysis projector `Q Q^T`.  The named handoffs
     `fl_basisColumnProjector_of_rightOrthogonalCertifiedBasis_entry_error_bound`
     and
     `fl_basisColumnProjector_of_rightOrthogonalCertifiedStoredBasis_entry_error_bound`
     package direct and generated-then-stored entrywise certificates against
     `Q O`.  Concrete QR/SVD/singular-vector, Davis-Kahan, or orthonormal-basis
     routines that produce the rotated-reference generation/storage
     certificates remain not-proved obligations; sampling probabilities and
     laws remain exact mathematical inputs.

278.  2026-06-04, LS.2g-hl active concrete-dual actual-unit validity handoff:
     no external source was used.  The proof is a local validity-surface
     adapter.  The new source-control, local solver, and sampled equation (8)
     wrappers derive the former `gammaValid fp m`, `gammaValid fp s`, and
     `gammaValid fp n` fields from `(m : Real) * fp.u < 1` or
     `(s : Real) * fp.u < 1` by `gammaValid_of_u_le_cap` and
     `gammaValid_mono`, then call the existing active concrete-dual finite-max
     theorems.  This does not use or change any probability construction:
     sampling probabilities and laws remain exact mathematical inputs.  The
     proof does not supply local diagonal dominance, scalar comparison,
     active-pivot policy, signed-stage recurrence budgets, finite-max
     smallness, or the final concrete QR/preconditioner theorem.

279.  2026-06-04, LR.1a rectangular low-rank factorization vocabulary:
     no external source was used.  The proof is local finite-dimensional
     algebra over explicit function-shaped matrices.  `LowRankApprox.lean`
     introduces `RectRankFactorization`, `RectRankAtMost`,
     `lowRankResidualFrob`, and `IsBestRankApproxFrob`, then expands the exact
     basis products `A (V V^T)` and `(U U^T) A` to prove
     `rightBasisProjectorApproxFactorization`,
     `leftBasisProjectorApproxFactorization`,
     `rightBasisProjectorApprox_rankAtMost`, and
     `leftBasisProjectorApprox_rankAtMost`.  This closes only the exact
     rank-factorization substrate for equation (9).  The external source row
     for the structural low-rank theorem itself remains open: rectangular SVD,
     pseudoinverse, best rank-`k` approximation, unitarily invariant norms, and
     concrete computed SVD/projector routine certificates still need to be
     formalized before LR.1 can close.  Sampling probabilities and laws remain
     exact mathematical inputs.

280.  2026-06-04, LR.1b exact best-rank comparison bridge:
     no external source was used.  The proof is a local certificate bridge:
     `IsBestRankApproxFrob.residual_le_of_rankAtMost` exposes the optimality
     field of the repository best-rank Frobenius certificate, and
     `IsBestRankApproxFrob.residual_le_rightBasisProjectorApprox` plus
     `IsBestRankApproxFrob.residual_le_leftBasisProjectorApprox` instantiate
     that field using the exact rank-at-most certificates proved in LR.1a.
     This does not prove Eckart--Young, construct a rectangular SVD or
     pseudoinverse, or instantiate a computed SVD/projector routine.  The
     external source row for equation (9) remains open for those foundations.

281.  2026-06-04, LR.1c equation (9) column-sketch projector rank bridge:
     the CACM source page containing equation (9) was rendered locally because
     text extraction drops the displayed formula.  The visible source statement
     bounds `||A - P_{A Z} A||` by the tail singular-value term plus the
     pseudoinverse term `Σ_{k,⊥}(V_{k,⊥}^T Z)(V_k^T Z)^+`, under the condition
     that `V_k^T Z` has full rank.  The Lean result proved in this pass uses
     only the exact algebraic part of that surface: if a supplied left
     multiplier `P_AZ` factors through the exact column sketch `A Z`, then
     `P_AZ A` has repository rank at most the sketch dimension.  The proof is
     local finite-sum algebra.  It does not prove the orthogonal projector or
     pseudoinverse construction, the full-rank condition, the unitarily
     invariant norm inequality, or any computed `Z`, `A Z`, projector, or
     pseudoinverse routine certificate.

282.  2026-06-04, LR.1d equation (9) residual-certificate surface:
     no external proof source was used for the Lean theorem-surface bridge.
     `Equation9ResidualCertificate` records the exact residual inequality with
     explicit nonnegativity hypotheses for the tail and coupling terms, while
     `equation9RankResidualSurface` and `equation9RelativeResidualSurface`
     combine that supplied certificate with the LR.1c rank bridge and a best
     rank-`k` certificate.  The source-proof work for equation (9) remains open:
     instantiate the certificate from rectangular SVD, the full-rank condition
     for `V_k^T Z`, pseudoinverse algebra, and the unitarily invariant norm
     inequality; separately instantiate FP/certificate bounds for any computed
     `Z`, `A Z`, projector, pseudoinverse, or product.

283.  2026-06-04, LR.1e explicit coefficient/pseudoinverse handoff:
     no external proof source was used.  The new Lean definitions and theorems
     are finite-sum algebra: `columnSketchLeftMultiplier A Z C` is exactly
     `(A Z) C`, so it immediately carries a `LeftFactorThrough` certificate
     with coefficient table `C`; the rank and residual-certificate surfaces
     then follow by reusing LR.1c and LR.1d.  The source-facing proof work
     remains open: construct or certify the particular coefficient table
     `C = (A Z)^+`, prove the orthogonal-projector and full-rank conditions,
     prove the equation (9) residual inequality, and separately certify any
     computed coefficient/pseudoinverse/projector/product routine.

284.  2026-06-04, LR.1f generalized-inverse projector surface:
     no external proof source was used.  The result is finite-sum algebra over
     the exact column sketch `B = A Z`: if the supplied coefficient table `C`
     satisfies the visible generalized-inverse condition `B C B = B`, then
     `P_C = B C` reproduces the sketch columns and is idempotent.  This is only
     the algebraic projector surface needed by a future pseudoinverse/full-rank
     instantiation; Moore-Penrose conditions, orthogonality, full-rank
     hypotheses, the equation (9) SVD residual inequality, and computed
     pseudoinverse/projector/product certificates remain open.

285.  2026-06-04, LR.1g symmetric-idempotent projector surface:
     no external proof source was used.  The new certificate simply combines
     the LR.1f generalized-inverse condition with symmetry of
     `P_C = (A Z) C`.  The proof reuses LR.1f to obtain reproduction and
     idempotence, and exposes symmetry as the extra field.  The remaining
     source-facing work is to prove that a concrete pseudoinverse coefficient
     table satisfies this certificate, then derive the equation (9) residual
     bound from rectangular SVD/full-rank/unitarily invariant norm infrastructure.

286.  2026-06-04, LR.1h Moore-Penrose certificate handoff:
     no external proof source was used.  This is finite-sum certificate
     packaging for the four exact Moore-Penrose equations of the column sketch
     `B = A Z`: `B C B = B`, `C B C = C`, symmetry of `B C`, and symmetry of
     `C B`.  The proof reuses LR.1f/LR.1g by projecting the first and third
     fields into the existing generalized-inverse and orthogonal-projector
     certificates; the second and fourth fields are exposed as coefficient-side
     obligations for later pseudoinverse algebra.  The remaining source-facing
     work is to construct or prove such a certificate for `C = (A Z)^+`, then
     derive the equation (9) residual bound from rectangular SVD/full-rank and
     unitarily invariant norm infrastructure.

287.  2026-06-04, LR.1i Gram-inverse Moore-Penrose instantiation:
     no external proof source was used.  The result is finite-sum algebra for
     the standard full-column-rank formula `C = (B^T B)^{-1} B^T`, but with the
     inverse and symmetry of `Ginv` supplied as explicit certificates.  The
     proof first shows `C B = I`, then derives `C B C = C`, `B C B = B`, and
     symmetry of both `B C` and `C B`, and finally reuses LR.1h/LR.1g to obtain
     the projector/rank surface.  The remaining source-facing work is to prove
     that the Gram inverse exists from full rank of the sketch and to connect
     that full-rank condition to the source `V_k^T Z` hypotheses.

288.  2026-06-04, LR.1j determinant-facing Gram-inverse route:
     no external proof source was used.  This is local exact algebra plus
     mathlib's `Matrix.transpose_nonsing_inv` and the repository
     determinant-to-`IsInverse` bridge.  The proof shows `B^T B` is symmetric,
     shows the repository `nonsingInv` table preserves symmetry for any
     symmetric square matrix, packages `det(B^T B) != 0` into
     `ColumnSketchGramInverseCertificate`, and then reuses LR.1i.  The
     remaining source-facing work is to derive the nonzero Gram determinant
     from a full-column-rank theorem for `A Z`, connect that to the source
     `V_k^T Z` hypothesis, and prove the equation (9) residual inequality.

289.  2026-06-04, LR.1k thin-factor Gram determinant bridge:
     no external proof source was used.  This is finite-sum and determinant
     algebra: from an exact factorization `B=U R`, exact orthonormality
     `U^T U=I`, and `det R != 0`, the proof rearranges finite sums to show
     `B^T B = R^T R`, uses determinant multiplicativity and transpose
     invariance to prove `det(B^T B) != 0`, and then reuses LR.1j/LR.1i.
     The remaining source-facing work is to construct such a thin factor from
     rectangular QR/SVD or the source full-rank hypotheses and then prove the
     equation (9) residual inequality.

290.  2026-06-04, LR.1l source-SVD Gram determinant bridge:
     no external proof source was used.  This is local exact finite-sum and
     determinant algebra: `A=U Sigma V^T` is unfolded to prove
     `A Z = U(Sigma V^T Z)`, determinant multiplicativity proves
     `det(Sigma(V^T Z)) != 0` from the two exact determinant hypotheses, and
     LR.1k/LR.1j/LR.1i supply the Gram determinant, `nonsingInv` certificate,
     Moore-Penrose certificate, and rank/projector surface.  The remaining
     source-facing work is to prove the residual inequality from rectangular
     SVD/pseudoinverse and unitarily invariant norm foundations, and to provide
     implementation-facing FP certificates for computed singular vectors,
     projectors, Gram/inverse products, and downstream products.

291.  2026-06-04, LR.1m source-SVD head-tail residual bridge:
     no external proof source was used.  This is local exact finite-sum and
     Frobenius-norm algebra: rectangular Frobenius subtraction is derived from
     the existing rectangular triangle inequality, sketch reproduction is
     pushed through an explicit head factorization, and the residual identity
     `A - P A = Tail - P Tail` follows from the supplied split `A=Head+Tail`
     and head reproduction.  The resulting head/tail certificate instantiates
     `Equation9ResidualCertificate`, and the source-SVD Gram-inverse projector
     theorem reuses LR.1l for the reproduction/rank/projector algebra.  The
     remaining source-facing work is still external to this local algebra:
     instantiate the head/tail certificate from rectangular SVD,
     pseudoinverse algebra for the source `V_k^T Z` condition, Eckart--Young,
     and unitarily invariant norm foundations, then add FP certificates for
     computed SVD/projector/Gram/inverse/product routines.

292.  2026-06-04, LR.1n explicit-coefficient head-tail instantiation:
     no external proof source was used.  This is local exact coefficient
     algebra: `Head=(A Z)W` is definitionally a head factorization through the
     sketch columns, `Tail=A-(A Z)W` definitionally gives `A=Head+Tail`, and
     the generic LR.1m certificate is instantiated from the two supplied
     Frobenius norm bounds.  The source-facing theorem still needs a
     mathematically chosen pseudoinverse coefficient `W`, plus external-source
     rectangular SVD/pseudoinverse and unitarily invariant norm arguments to
     prove the two bounds from the CACM equation (9) hypotheses.

293.  2026-06-04, LR.1o source-coefficient residual-tail instantiation:
     no external proof source was used for the closed algebra.  This is local
     exact finite-sum and inverse-certificate algebra: with
     `W=(V^T Z)^{-1}V^T`, the repository `nonsingInv` right-inverse theorem
     gives `(V^T Z)W=V^T`; finite-sum associativity then gives
     `Sigma(V^T Z)W=Sigma V^T` and reproduction of the source head
     `U Sigma V^T` from its own sketch.  For a source split
     `A=U Sigma V^T+Tail`, the new theorem rewrites the implemented sketch
     head as `U Sigma V^T+(Tail Z)W` and the sketch tail as
     `Tail-(Tail Z)W`, then instantiates the generic head/tail residual
     surfaces from supplied projector and norm certificates.  The remaining
     source-facing work is to prove the two Frobenius norm bounds from
     rectangular SVD/pseudoinverse and unitarily invariant norm foundations,
     construct/certify the exact orthogonal projector onto `range(A Z)` for the
     head-plus-tail sketch, prove Eckart--Young/best-rank optimality, and add
     implementation-facing FP certificates for computed cross products,
     inverses, coefficients, SVD data, projectors, and downstream products.

294.  2026-06-04, LR.1p source-coefficient Moore-Penrose projector adapter:
     no external proof source was used.  This is local exact certificate
     composition: a supplied `ColumnSketchMoorePenroseCertificate A Z C` is
     converted through the existing generalized-inverse/orthogonal-projector
     surface for `P=(A Z)C`, then composed with the LR.1o source residual tail
     theorem.  The result gives named rank/residual and relative-residual
     surfaces with symmetry, factor-through, reproduction, idempotence, and
     rank fields exposed.  The remaining source-facing work is still to
     construct or prove the Moore-Penrose certificate for a concrete
     pseudoinverse/Gram-inverse route on the head-plus-tail sketch, prove the
     two source-tail Frobenius norm bounds, formalize Eckart--Young and
     unitarily invariant norm infrastructure, and add FP certificates for every
     computed non-probability quantity.

295.  2026-06-04, LR.1q source-coefficient Gram-inverse projector
     instantiation: no external proof source was used.  This is local exact
     certificate composition: the determinant-facing theorem
     `columnSketchGramInverseCoefficient_moorePenroseCertificate_of_det_ne_zero`
     supplies the four Moore-Penrose equations for the concrete coefficient
     table `nonsingInv((A Z)^T(A Z))(A Z)^T`, and LR.1p turns that certificate
     into source-tail rank/residual and relative-residual surfaces for the
     named `columnSketchGramInverseProjector A Z`.  The remaining source-facing
     work is still to prove the Gram determinant from source/full-rank
     hypotheses for the head-plus-tail sketch, prove the two source-tail
     Frobenius norm bounds, formalize Eckart--Young and unitarily invariant
     norm infrastructure, and add FP certificates for every computed
     non-probability quantity.

296.  2026-06-04, LR.1r source head-tail sketch-Gram split:
     no external proof source was used.  This is local finite-sum algebra for
     the active LR.1 determinant route: `columnSketch_sourceSVDFactorMatrix`
     expands `(U Sigma V^T)Z` as `U(Sigma(V^T Z))`; the two cross-term
     theorems use the exact orthogonality certificate `U^T Tail = 0`; and
     `columnSketchGram_sourceHeadTail_leftOrthogonal` rewrites the full sketch
     Gram as the sum of the source-head sketch Gram and the tail sketch Gram.
     The remaining source-facing determinant work is to prove PSD of the tail
     sketch Gram, positive definiteness/nonzero determinant of the head Gram
     from `det(Sigma) != 0` and `det(V^T Z) != 0`, and preservation of nonzero
     determinant when adding the PSD tail Gram.

297.  2026-06-04, LR.1s column-sketch Gram PSD and determinant preservation:
     no external proof source was used.  This is local finite-sum algebra plus
     mathlib's positive-definite determinant API.  The theorem
     `finiteQuadraticForm_columnSketchGram_eq_sum_sq` rewrites the quadratic
     form of `(A Z)^T(A Z)` as a sum of squares, and
     `columnSketchGram_finitePSD` gives PSD for every exact sketch Gram.
     Mathlib's `Matrix.PosDef.add_posSemidef` and `Matrix.PosDef.det_pos`
     prove `matrix_det_ne_zero_of_posDef_add_posSemidef`; LR.1r's exact
     head-tail Gram split and the automatic tail-Gram PSD theorem then give
     `columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef`.  The
     remaining determinant work is to prove the source-head sketch Gram
     positive definite from the source thin factor/determinant data, then
     connect that to the full CACM source hypotheses.

298.  2026-06-05, LR.1t source-factor positive-definite sketch Gram and
     determinant closure: no external proof source was used.  The proof is local
     finite-dimensional linear algebra.  `matrix_transpose_mul_self_posDef_of_det_ne_zero`
     proves positive definiteness of `R^T R` from `det R != 0` by the real
     quadratic-form identity `x^T R^T R x = ||R x||_2^2` and the zero-kernel
     consequence of the nonzero determinant.  The thin-factor certificate then
     lifts this to `columnSketchGram_posDef_of_thinFactorCertificate`, the
     source determinant product bridge gives
     `columnSketchGram_posDef_of_sourceSVD_det_factors`, and LR.1s gives
     `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors` for
     the orthogonal source head-plus-tail split.  This closes the exact
     determinant side of D1; remaining source-tail norm and rectangular SVD
     dependencies are separate proof targets.

299.  2026-06-05, LR.1u source-tail norm reduction: no external proof source
     was used.  The proof is local finite-sum Frobenius algebra.  First,
     `frobNormSqRect_leftOrthonormalFactor` expands the squared Frobenius norm
     of `U C`, uses `U^T U=I` to collapse the cross terms, and
     `frobNormRect_leftOrthonormalFactor` takes square roots.  Then
     `sourceSketchResidualTail_leftFactor` proves that if
     `Tail=Utail TailCoord`, the exact residual
     `Tail-(Tail Z)(V^T Z)^{-1}V^T` factors through `Utail` with coordinate
     residual `TailCoord-(TailCoord Z)(V^T Z)^{-1}V^T`.  The final two
     Frobenius equalities reduce D2 to a coordinate residual bound.

300.  2026-06-05, LR.1v coordinate-tail residual factorization: no external
     proof source was used.  The proof is local algebra around the already
     formalized exact source coefficient table.  `sourceRightBasisTranspose`
     gives the exact row representation of `V_perp^T`, `rightSketchCrossGramRect`
     gives `V_perp^T Z`, and the sketch-head/residual lemmas expand the
     coefficient product `(V_perp^T Z)(V_k^T Z)^{-1}V_k^T`.  The square-left
     factor lemma reuses `sourceSketchResidualTail_leftFactor`, and the
     Frobenius bound reuses the repository rectangular submultiplicativity
     theorem `frobNormRect_matMulRectLeft_le`.

301.  2026-06-05, LR.1w right-tail residual block products: no external proof
     source was used.  The proof is local finite-sum algebra around the exact
     source coefficient table.  `sourceSketchCoefficient_mul_rightTailBasis_of_cross_zero`
     and `sourceSketchCoefficient_mul_headRightBasis_of_orthonormal` expand
     multiplication of `(V_k^T Z)^{-1}V_k^T` against the supplied exact
     right-tail/head bases.  `sourceRightResidual_mul_rightTailBasis_eq_id`
     and `sourceRightResidual_mul_headRightBasis_eq_neg_invFactor` subtract
     these products from `V_perp^T` to obtain the two right-orthogonal block
     identities.  The remaining D2 norm step requires a Frobenius/unitarily
     invariant norm bridge, not an external citation.

302.  2026-06-05, LR.1x right-tail Frobenius block identity: no external proof
     source was used.  The proof is local finite-sum Frobenius algebra.
     `finiteFrobNormSq_rectRightOrthonormal` is a generic adapter showing that
     right multiplication by a finite row-orthonormal column family preserves
     squared Frobenius norm.  The low-rank proof defines the sum-indexed basis
     block `[V_perp,V_k]`, rewrites the LR.1w residual products as `[I,-M]`,
     multiplies by `Sigma`, and splits the sum-indexed squared Frobenius norm
     into `||Sigma||_F^2 + ||Sigma M||_F^2`.  The next source-dependent step is
     the sharp bound on `Sigma M`.

303.  2026-06-05, LR.1y source cross-term residual-tail certificate: no
     external proof source was used.  The source wording of CACM equation (9)
     treats the cross-term inequality as a structural condition on the sketch
     matrix \(Z\).  The Lean theorem
     `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq` therefore
     takes the exact Frobenius cross-term certificate
     `||Sigma (V_perp^T Z)(V_k^T Z)^{-1}||_F <= eps ||Sigma||_F` as a visible
     hypothesis, combines it with LR.1x's squared Frobenius block identity, and
     applies monotonicity of the square root plus scalar square algebra to prove
     `||Sigma (V_perp^T-(V_perp^T Z)(V_k^T Z)^{-1}V_k^T)||_F <=
     sqrt(1+eps^2)||Sigma||_F`.  This closes the source-faithful Frobenius
     structural-condition handoff for supplied exact right-basis certificates;
     spectral/general unitarily invariant variants and computed-object
     certificates remain separate obligations.

304.  2026-06-05, LR.1z ambient source-tail residual certificate: no external
     proof source was used.  This is a local composition theorem.  The Lean
     proof first applies `frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor`
     to move the ambient residual tail through the supplied exact
     left-orthonormal tail factor, then rewrites the coordinate residual using
     `sourceSketchResidualTail_leftSquareFactor`, and finally invokes
     `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq`.  The
     theorem therefore closes the ambient Frobenius handoff for supplied exact
     source-tail SVD-factor data and the source cross-term certificate; it does
     not construct those factors, prove Eckart--Young, prove spectral/general
     unitarily invariant variants, or certify computed non-probability
     SVD/projector/cross-product/Gram/inverse/coefficient/product routines.

305.  2026-06-05, LR.1aa projected source-tail coupling certificate: no
     external proof source was used.  The proof is local finite-dimensional
     orthogonal-projector algebra.  `finiteVecNorm2_finiteMatVec_le_of_symmetric_idempotent`
     uses symmetry and idempotence to rewrite `||P x||_2^2` as the inner
     product `x^T P x`, applies finite Cauchy--Schwarz, and cancels the
     nonnegative `||P x||_2` factor.  The squared and rectangular Frobenius
     forms sum this columnwise, and the column-sketch theorem instantiates the
     symmetric-idempotent hypotheses from `ColumnSketchOrthogonalProjectorCertificate`.
     The final source-tail theorems compose this contraction with LR.1z for
     orthogonal-projector and Moore--Penrose certificates.  Remaining
     source-paper dependencies are spectral/general unitarily invariant
     variants, source-SVD/Eckart--Young construction, and implementation-facing
     computed-object certificates.

306.  2026-06-05, LR.1ab transpose-action spectral coupling certificate: no
     external proof source was used.  The proof is a local row-wise Frobenius
     summation.  `frobNormSqRect_matMulRectLeft_le_sq_mul_of_transpose_rectOpNorm2Le`
     applies the supplied exact operator certificate
     `rectOpNorm2Le (finiteTranspose M) eps` to each row of `Sigma`, squares
     using `eps >= 0`, and sums the resulting row bounds.  The norm-form lemma
     takes square roots, `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le`
     instantiates `M=(V_perp^T Z)(V_k^T Z)^{-1}`, and the projected
     Moore--Penrose theorem composes the resulting Frobenius cross-term
     certificate with LR.1aa.  Remaining source-paper dependencies are the
     ordinary spectral-norm/transpose equivalence for the non-transposed cross
     factor, general unitarily invariant variants, source-SVD/Eckart--Young
     construction, randomness-derived operator certificates, and
     implementation-facing computed-object certificates.

307.  2026-06-05, LR.1ac ordinary operator coupling certificate: no external
     proof source was used.  The proof is local finite-dimensional norm
     duality.  `rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le` fixes `y`,
     sets `z=M^T y`, and if `z` is nonzero tests against the normalized vector
     `x=z/||z||_2`.  The inner-product transpose identity rewrites
     `<x,M^T y>` as `<Mx,y>`, Cauchy--Schwarz bounds this by
     `||Mx||_2||y||_2`, and the original `rectOpNorm2Le M eps` certificate
     gives `||M^T y||_2 <= eps||y||_2`.  The low-rank wrappers instantiate
     `M=(V_perp^T Z)(V_k^T Z)^{-1}` and compose the resulting transpose-action
     certificate with LR.1ab/LR.1aa.  Remaining source-paper dependencies are
     general unitarily invariant variants, source-SVD/Eckart--Young
     construction, randomness-derived operator certificates, and
     implementation-facing computed-object certificates.

308.  2026-06-05, LR.1ad computed cross-factor perturbation certificate: no
     external proof source was used.  The proof is a local triangle-inequality
     and submultiplicativity transfer.  Write the exact analysis factor as
     `M = Mhat + (M - Mhat)`.  The computed ordinary operator certificate for
     `Mhat` is converted to a transpose-action certificate by LR.1ac and then
     to `||Sigma Mhat||_F <= eps||Sigma||_F` by LR.1ab's generic Frobenius
     handoff.  The perturbation term is bounded by
     `frobNormRect_matMulRectLeft_le` and the displayed Frobenius radius
     `tau`.  The CACM wrapper instantiates
     `M=(V_perp^T Z)(V_k^T Z)^{-1}` and the projected theorem composes the
     resulting `(eps+tau)` cross-term certificate through LR.1aa.  Remaining
     source-paper dependencies are concrete FP routine instantiations for
     `Mhat` and its perturbation radius, computed SVD/singular-vector and
     projector certificates, randomness-derived operator certificates, and the
     general unitarily invariant/SVD/Eckart--Young foundations.

309.  2026-06-05, LR.1ae entrywise computed cross-factor perturbation
     certificate: no external proof source was used.  The proof is local
     finite-dimensional algebra.  `frobNormRect_le_sqrt_mul_nat_of_entry_abs_le`
     squares the uniform entrywise bound, sums over the finite rectangular
     index set, rewrites the finite cardinality as `m*n`, and takes square
     roots to obtain `||E||_F <= sqrt(m*n) eta`.  The low-rank wrappers apply
     LR.1ad with `tau = sqrt(q*r) eta` for
     `E=(V_perp^T Z)(V_k^T Z)^{-1}-Mhat`, then compose the resulting
     `(eps+sqrt(q*r)eta)` cross-term certificate through LR.1aa.  Remaining
     source-paper dependencies are concrete FP routine instantiations for the
     entrywise budget and operator certificate, computed SVD/singular-vector
     and projector certificates, randomness-derived operator certificates, and
     the general unitarily invariant/SVD/Eckart--Young foundations.

310.  2026-06-05, LR.1af component-certified computed cross-factor
     certificate: no external proof source was used.  The proof is a local
     finite-dimensional product expansion and triangle-inequality argument.
     `rectMatMul_entry_abs_sub_computed_le_of_component_sums` writes
     `XY-Mhat` as `(X-Xhat)Y + Xhat(Y-Yhat) + (XhatYhat-Mhat)`, bounds the two
     sums by absolute-value row/column contractions, and adds the rounded
     product budget.  The low-rank wrapper instantiates
     `X=V_perp^T Z` and `Y=(V_k^T Z)^{-1}`, then composes the resulting
     entrywise radius `alpha+beta+rho` through LR.1ae and LR.1aa.  Remaining
     source-paper dependencies are concrete dot-product, inverse, matrix
     product, and computed-operator-certificate instantiations, computed
     SVD/singular-vector and projector certificates, randomness-derived
     operator certificates, and the general unitarily invariant/SVD/Eckart--Young
     foundations.

311.  2026-06-05, LR.1ag concrete fl-matmul cross-gram component
     certificate: no external proof source was used beyond the already
     formalized Higham dot-product/matrix-product model in
     `Algorithms/MatMul.lean`.  The new low-rank definitions set
     `Xhat = flRightSketchCrossGramRect fp Vperp Z =
     fl_matMul fp q n r (Vperp^T) Z` and expose the entry budget
     `gamma(fp,n) * sum_j |Vperp_j a| |Z_j b|`.  The proof reuses
     `matMul_error_bound` entrywise, contracts this budget against the exact
     inverse columns, and then invokes LR.1af.  The resulting equation (9)
     wrappers keep the inverse-factor budget, final rounded-product budget,
     computed-operator certificate, computed SVD/projector/Gram obligations,
     and randomness-derived operator certificate visible as remaining
     source-paper dependencies.  Sampling probabilities and laws remain exact
     mathematical inputs.

312.  2026-06-05, LR.1ah concrete square cross-Gram inverse-input
     certificate: no external proof source was used beyond the same local
     `matMul_error_bound`.  The square cross Gram is the special case
     `Vperp = V` of the rectangular cross-Gram computation:
     `flRightSketchCrossGram fp V Z = flRightSketchCrossGramRect fp V Z`.
     The entrywise theorem reuses LR.1ag's dot-product estimate, and the
     Frobenius wrapper applies the existing finite rectangular
     entrywise-to-Frobenius bound under a uniform `omega` cap on the displayed
     dot-product budgets.  This supplies an inverse-input perturbation
     certificate only; inverse stability for `(V_k^T Z)^{-1}` and the computed
     inverse-factor budget remain future D5 obligations.  Sampling
     probabilities and laws remain exact mathematical inputs.

313.  2026-06-05, LR.1ai inverse-entry computed-factor adapter: no external
     proof source was used.  The proof is finite-sum algebra: an entrywise
     inverse error certificate `|Y-Yhat| <= eta` is multiplied by the
     nonnegative computed left-factor weights `|Xhat_ab|`, summed over the
     shared index, and bounded by the supplied row absolute-sum certificate
     `sum_b |Xhat_ab| <= chi`.  The concrete specialization sets
     `Xhat = flRightSketchCrossGramRect fp Vperp Z` and composes with LR.1ag.
     This closes only the propagation from an inverse routine's entrywise
     certificate to the LR.1af `beta` term; a concrete inverse algorithm still
     has to prove the certificate.  Sampling probabilities and laws remain
     exact mathematical inputs.

314.  2026-06-05, LR.1aj concrete final rounded-product certificate: no
     external proof source was used beyond the local Higham matrix-product
     theorem `matMul_error_bound`.  The proof defines the final computed factor
     as `fl_matMul fp q r r Xhat Yhat`, applies the dot-product budget
     `gamma(fp,r) * sum_b |Xhat_ab| |Yhat_bc|`, and composes this `rho`
     certificate with LR.1ai after setting
     `Xhat = flRightSketchCrossGramRect fp Vperp Z`.  This closes the
     final-product arithmetic layer only; the inverse routine's entrywise
     `eta` proof and the computed operator certificate for the product remain
     open.  Sampling probabilities and laws remain exact mathematical inputs.

315.  2026-06-05, LR.1ak computed-product Frobenius-to-operator handoff:
     no external proof source was used.  The proof reuses the local finite
     matrix theorem `rectOpNorm2Le_of_frobNormRect_le`: a visible certificate
     `||Mhat||_F <= eps` for
     `Mhat = fl(fl((V_perp^T)Z) Yhat)` supplies the ordinary rectangular
     operator certificate consumed by LR.1aj.  The cross-term and projected
     wrappers then preserve the radius
     `eps+sqrt(q*r)(alpha+chi*eta+rho)`.  This closes a deterministic
     computed-operator adapter for the final product only; the inverse
     routine's entrywise `eta` proof, randomness-derived certificates, and
     computed SVD/projector/Gram layers remain open.  Sampling probabilities
     and laws remain exact mathematical inputs.

316.  2026-06-05, LR.1al product absolute-sum source for computed-product
     Frobenius certificate: no external proof source was used.  The proof uses
     the local `fl_matMul` entry budget from LR.1aj, the elementary triangle
     inequality for
     `|fl(Xhat Yhat)_{ac}| <= |sum_b Xhat_ab Yhat_bc| + rho`, the finite
     absolute-sum bound
     `|sum_b Xhat_ab Yhat_bc| <= sum_b |Xhat_ab| |Yhat_bc|`, and the local
     Frobenius helper `frobNormRect_le_sqrt_mul_nat_of_entry_abs_le`.  Thus
     `sum_b |Xhat_ab||Yhat_bc| <= kappa` and the product dot-budget
     `<= rho` imply `||fl(Xhat Yhat)||_F <= sqrt(q*r)(kappa+rho)`, which
     feeds LR.1ak.  Sampling probabilities and laws remain exact mathematical
     inputs.

317.  2026-06-05, LR.1am perturbed-inverse source for the equation-(9)
     inverse `eta` certificate: external paper source is Higham, Accuracy and
     Stability of Numerical Algorithms, §13.1, but the Lean proof reuses the
     repository theorem `ideal_forward_error` from `MatrixInversion.lean`.
     The adapter states the certificate form a concrete inverse routine must
     supply: `(A+DeltaA)Yhat=I`, `|DeltaA| <= epsInv |A|`, and a visible
     componentwise sensitivity bound
     `epsInv * sum |A^{-1}| |A| |Yhat| <= eta`.  Specializing
     `A=rightSketchCrossGram V Z` supplies the LR.1ai entrywise hypothesis
     `|nonsingInv(V_k^T Z)-Yhat| <= eta`; the composed wrappers also reuse
     LR.1al's product absolute-sum operator certificate.  This does not yet
     formalize the concrete inversion loop that produces `DeltaA` and `Yhat`.
     Sampling probabilities and laws remain exact mathematical inputs.

318.  2026-06-05, LR.1an Method-A LU source for the equation-(9) inverse
     `eta` certificate: external paper source is Higham, Accuracy and
     Stability of Numerical Algorithms, §13.3 Method A, especially equations
     13.15--13.17.  The Lean proof reuses the repository Method-A surface in
     `MatrixInversion.lean`: `methodA_column_backward_error`,
     `methodA_right_residual`, and `methodA_forward_error`.  The new named
     computed inverse `methodAComputedInverse` exposes the actual computed
     columns from forward and back substitution, and the RandNLA adapter
     specializes the resulting entrywise forward-error theorem to
     `A=rightSketchCrossGram V Z`.  This closes the inverse-solve adapter
     conditional on a local `LUBackwardError` certificate; it does not yet
     prove a concrete LU factor-generation routine supplies that certificate.
     Sampling probabilities and laws remain exact mathematical inputs.

319.  2026-06-05, LR.1ao computed-input Method-A LU transfer for the
     equation-(9) inverse `eta` certificate: external paper source remains
     Higham, Accuracy and Stability of Numerical Algorithms, §§9.3--9.4 for
     LU factorization/solve backward error and §13.3 for Method A.  The new
     Lean proof formalizes the coefficient bookkeeping needed when the LU
     factors are certified for a rounded input matrix rather than the exact
     analysis matrix: `LUBackwardError.of_input_abs_error_le_absLUProduct`
     transfers an LU certificate from `Ahat` to `A` with coefficient
     `eps+mu`, `lu_solve_backward_error_factor_gamma` combines a visible
     factorization coefficient with triangular-solve `gamma`, and the
     Method-A/RandNLA wrappers specialize the result to
     `Ahat=flRightSketchCrossGram fp V Z` and `A=rightSketchCrossGram V Z`.
     This source closes the computed square-cross-Gram input-transfer layer
     only; a concrete LU factor-generation loop for `flRightSketchCrossGram`
     remains open.  Sampling probabilities and laws remain exact mathematical
     inputs.
320.  2026-06-05, LR.1ap Doolittle recurrence certificate for the rounded
     square cross Gram in equation (9): external source is Higham, Accuracy and
     Stability of Numerical Algorithms, §9.2 Algorithm 9.2 for Doolittle's
     recurrence organization, §9.3 Theorem 9.3 for componentwise LU
     backward-error form, and §13.3 Method A for the inverse-column route.
     The Lean theorem `DoolittleLU.to_LUBackwardError` proves the recurrence
     contract implies `LUBackwardError n A L_hat U_hat (gamma fp n)` by
     splitting entries into the `i <= j` row-recurrence case and the `j < i`
     column-recurrence case.  The RandNLA wrappers specialize this to
     `A = flRightSketchCrossGram fp V Z` and then use LR.1ao's input transfer
     to charge the exact square cross Gram with coefficient
     `(gamma fp r + mu) + 2*gamma fp r + gamma fp r^2`.  This closes the
     certificate-level Doolittle factor-generation bridge; constructing the
     `DoolittleLU` witness from an executable dense LU loop remains open.
     Sampling probabilities and laws remain exact mathematical inputs.

321.  2026-06-05, LR.1by exact right-Gram singular-value order and
     nonnegativity: no external paper source was needed beyond mathlib's
     finite Hermitian spectral API.  The Lean proof defines
     `rectRightGram A = A^T A`, proves its quadratic form is
     `sum_i (sum_j A_ij x_j)^2`, derives symmetry and PSD, and then uses
     mathlib's ordered Hermitian eigenvalues to define
     `rectSingularValueSq A` and `rectSingularValue A`.  The closed facts are
     nonnegativity and antitonicity of the singular-value squares, inherited
     nonnegativity and antitonicity of the square-root singular values, and
     `(rectSingularValue A j)^2 = rectSingularValueSq A j`.  This closes only
     the exact right-Gram spectral adapter in D3; singular vectors, a
     rectangular SVD/source split, Eckart--Young tail optimality, randomness,
     and computed non-probability SVD/singular-vector/projector/Gram routines
     remain open.  Sampling probabilities and laws remain exact mathematical
     inputs.

322.  2026-06-05, LR.1bz exact right-Gram eigenvector/right singular-vector
     table: no external paper source was needed beyond mathlib's finite
     Hermitian eigenvector-basis API (`Matrix.IsHermitian.eigenvectorBasis`,
     `Matrix.IsHermitian.eigenvectorUnitary`, and
     `Matrix.IsHermitian.mulVec_eigenvectorBasis`).  The Lean proof defines a
     basis-indexed eigenvalue/singular-value table for the exact analysis Gram
     `A^T A`, derives an orthogonal real eigenvector matrix from the associated
     unitary matrix, proves the right-Gram eigenvector equation, and diagonalizes
     `V^T(A^T A)V`.  This closed route intentionally remains basis-indexed
     because mathlib's eigenbasis is indexed by its `eigenvalues` function,
     whereas LR.1by's monotone singular values use the ordered zero-indexed
     `eigenvalues₀` sequence.  The ordered source split, rectangular SVD
     existence, Eckart--Young tail optimality, randomness, and computed
     non-probability SVD/singular-vector/projector/Gram routines remain open.
     Sampling probabilities and laws remain exact mathematical inputs.

323.  2026-06-05, LR.1ca full-positive basis-indexed SVD reconstruction:
     no external paper source was needed beyond the exact right-Gram
     diagonalization closed in LR.1bz and elementary finite-sum algebra.  The
     Lean proof defines projected right-Gram eigenbasis columns \(A v_a\),
     defines left candidates \(u_a=A v_a/\tau_a\) under a visible
     strict-positivity hypothesis on every basis-indexed \(\tau_a\), proves
     \(u_a^T u_b=\delta_{ab}\) from `V^T(A^T A)V=diag(tau^2)`, and proves the
     exact reconstruction \(A=\sum_a u_a\tau_a v_a^T\) from row orthonormality
     of the right eigenbasis.  This closed route is full-positive and
     basis-indexed; it does not solve zero singular values, ordered head/tail
     selection, rank-deficient rectangular SVD existence, Eckart--Young tail
     optimality, randomness, or computed non-probability
     SVD/singular-vector/projector/Gram routines.  Sampling probabilities and
     laws remain exact mathematical inputs.

324.  2026-06-05, LR.1cb zero projected columns for zero basis-indexed
     singular values: no external paper source was needed.  The local proof
     route uses the exact projected-column diagonal identity from LR.1ca with
     `a=b`, the equality
     `sum_i (A v_a)_i^2 = (rectRightGramBasisSingularValue A a)^2`, and
     finite-sum nonnegativity of squares.  This closes a rank-deficient adapter
     for the basis-indexed right-Gram route only; ordered source splitting,
     rectangular SVD existence, Eckart--Young, randomness, and computed
     non-probability SVD/singular-vector/projector/Gram routines remain open.
     Sampling probabilities and laws remain exact mathematical inputs.

325.  2026-06-05, LR.1cc zero-safe basis-indexed reconstruction: no external
     paper source was needed.  The local proof route is LR.1cb's zero projected
     column theorem, the zero-safe definition \(u_a=0\) when \(\tau_a=0\) and
     \(u_a=A v_a/\tau_a\) otherwise, and row-completeness of the exact
     right-Gram eigenbasis.  This removes the full-positive hypothesis from the
     basis-indexed reconstruction only; ordered source
     splitting, rectangular SVD existence, Eckart--Young, randomness, and
     computed non-probability SVD/singular-vector/projector/Gram routines
     remain open.  Sampling probabilities and laws remain exact mathematical
     inputs.

326.  2026-06-05, LR.1cd arbitrary selected-index head/tail split from the
     zero-safe right-Gram reconstruction: no external paper source was needed.
     The local proof route was finite-sum partitioning of the basis index set
     into a selected finite set \(s\) and its complement, followed by LR.1cc's
     exact zero-safe reconstruction.  The selected head rank-card proof
     reindexed \(s\) through `s.orderEmbOfFin rfl : Fin s.card -> Fin n`.
     This closes only the exact selected-index identity
     \(A=\mathrm{Head}_s+\mathrm{Tail}_s\) and
     \(\operatorname{rank}(\mathrm{Head}_s)\le |s|\); ordered
     top-singular-direction selection, rectangular SVD existence,
     Eckart--Young, randomness-derived certificates, and computed
     non-probability SVD/singular-vector/projector/Gram routines remain open.
     Sampling probabilities and laws remain exact mathematical inputs.

327.  2026-06-05, LR.1ce selected right-Gram head in selected eigenvector
     sketch space: no external paper source was needed.  The local route
     instantiates the exact column sketch `A Z_s` with selected right-Gram
     eigenvectors, identifies those columns with the projected columns
     \(A v_a\), and uses LR.1cc's zero-safe factor identity
     \(\tau_a u_a=A v_a\) to rewrite the LR.1cd selected head as
     \((A Z_s)V_s^T\).  This closes only the exact selected-head
     column-sketch factorization; ordered top-singular-direction selection,
     rectangular SVD existence, Eckart--Young, randomness-derived
     certificates, and computed non-probability SVD/singular-vector/projector/
     Gram/sketch routines remain open.  Sampling probabilities and laws remain
     exact mathematical inputs.

328.  2026-06-05, LR.1cf selected split equation-(9) certificate adapter:
     closed locally; no external paper source was needed.  The local route
     packages LR.1cd's exact selected head/tail split and LR.1ce's
     selected-head `ColumnSketchHeadFactorization` into
     `Equation9HeadTailSketchCertificate` under explicit tail and projected-tail
     coupling bounds, then composes with the existing rank/residual equation
     (9) surface under explicit projector-through-sketch and sketch-reproduction
     hypotheses.  This is exact-object adapter algebra only; tail/coupling
     bounds, projector reproduction, ordered top-singular-direction selection,
     rectangular SVD existence, Eckart--Young, randomness certificates, and
     computed non-probability SVD/singular-vector/projector/Gram/sketch routines
     remain open.  Sampling probabilities and laws remain exact mathematical
     inputs.

329.  2026-06-05, LR.1cg selected cardinality rank handoff: closed locally;
     no external paper source was needed.  The local route is pure Lean
     rank-index transport: a `RectRankAtMost` certificate at rank `s.card` is
     transported to displayed rank `k` under the explicit equality
     `s.card = k`, and the LR.1cf equation-(9) rank/residual surface is
     restated with that displayed rank.  This closes only the cardinality
     adapter; the proof that a source-faithful ordered top-`k` selected set
     exists and has the desired singular-direction semantics remains part of
     the rectangular SVD/order foundation, and computed non-probability
     SVD/singular-vector/projector/Gram/sketch routines remain open.  Sampling
     probabilities and laws remain exact mathematical inputs.

330.  2026-06-05, LR.1ch injective selected-index embedding handoff: closed
     and fully validated locally; no external paper source was needed.  The local route defines
     the selected set as the finite image of an embedding `Fin k ↪ Fin n`,
     proves that the image cardinality is `k`, and specializes the LR.1cg
     selected-head and equation-(9) rank/residual handoffs to that embedded
     selected set.  This closes only the concrete injective-index selection
     cardinality layer; the semantic theorem that a chosen embedding enumerates
     ordered top singular directions remains part of the rectangular SVD/order
     foundation, and computed non-probability SVD/singular-vector/projector/
     Gram/sketch routines remain open.  Sampling probabilities and laws remain
     exact mathematical inputs.

331.  2026-06-05, LR.1ci semantic ordered-selection handoff: closed locally.
     No external source was needed for the local certificate handoff:
     the step only exposes the semantic certificate equating embedding-selected
     basis-indexed singular values with the ordered right-Gram singular values
     on the first `k` displayed indices, proves its immediate square/order
     consequences, and composes with LR.1ch.  Constructing that certificate
     from mathlib's arbitrary eigenbasis order, rectangular SVD existence,
     Eckart--Young tail optimality, and computed non-probability SVD/singular-
     vector/projector/Gram/sketch routines remain open.  Sampling probabilities
     and laws remain exact mathematical inputs.

332.  2026-06-05, LR.1cj constructed ordered-top embedding certificate: closed
     locally.  The source is the local mathlib spectral API, specifically
     `Mathlib/Analysis/Matrix/Spectrum.lean`: `Matrix.IsHermitian.eigenvalues`
     and `eigenvectorBasis` both use the `Fintype.equivOfCardEq` route
     instantiated in Lean as `Fintype.card_fin (Fintype.card (Fin n))` to
     reindex the ordered `eigenvalues₀` sequence.
     The proof constructs the selected embedding from that equivalence and the
     displayed top-index cast.  No external paper source was needed for
     this exact index-reindexing step.  Rectangular SVD existence, Eckart--Young,
     randomness, and computed non-probability SVD/singular-vector/projector/
     Gram/sketch routines remain open.  Sampling probabilities and laws remain
     exact mathematical inputs.  Full validation passed locally: focused Lean
     and focused build, `examples/LibraryLookup.lean`, full `lake build`,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs PDF
     byte comparison.

333.  2026-06-05, LR.1ck ordered top/complement singular-value dominance:
     closed locally.  No external proof source was needed.  The proof uses the
     same local mathlib spectral reindexing API from LR.1cj, plus the already
     formalized antitonicity of the ordered right-Gram singular-value sequence.
     It introduces the inverse ordered coordinate of a basis-indexed right-Gram
     eigenvector and proves that indices outside the constructed top-`k`
     selected set have ordered coordinate at least `k`, so every selected top
     singular value dominates every unselected basis-indexed singular value.
     This is not an Eckart--Young theorem and not a computed-SVD routine
     certificate.  Sampling probabilities and laws remain exact mathematical
     inputs.  Full validation passed locally: focused Lean and focused build,
     `examples/LibraryLookup.lean`, full `lake build`, marker scan, axiom audit,
     PDF compile/text/render checks, and root/docs PDF byte comparison.

334.  2026-06-05, LR.1cl selected-head positivity from kth ordered singular
     value: closed locally.  No external proof source was needed.  The proof
     uses the local top-index cast, elementary `Fin` order arithmetic, the
     already proved antitonicity of `rectSingularValue`, and the constructed
     ordered-top embedding certificate from LR.1cj.  It turns a visible
     source-rank-style hypothesis, positivity of the kth ordered singular value,
     into positive and nonzero selected basis-indexed head singular entries.
     This is not a rectangular SVD existence theorem, not an Eckart--Young
     theorem, and not a computed-SVD routine certificate.  Sampling probabilities
     and laws remain exact mathematical inputs.  Full validation passed locally:
     focused Lean and focused build, `examples/LibraryLookup.lean`, full
     `lake build`, marker scan, axiom audit, PDF compile/text/render checks, and
     root/docs PDF byte comparison.

335.  2026-06-05, LR.1cm selected zero-safe left-basis orthonormality for the
     constructed ordered top-`k` block: closed locally.  No external proof
     source was needed.  The proof uses the local projected-column dot product
     identity, the zero-safe left-candidate normalization theorem away from
     zero singular values, LR.1cl's selected-head positivity result, and
     injectivity of `rectRightGramOrderedTopEmbedding`.  It proves the exact
     source-SVD left-basis ingredient needed by a future ordered source split,
     but it is not a tail factor construction, not a right-basis completeness
     theorem, not an Eckart--Young theorem, and not a computed-SVD routine
     certificate.  Sampling probabilities and laws remain exact mathematical
     inputs.  Full validation passed locally: focused Lean and focused build,
     `examples/LibraryLookup.lean`, full `lake build`, marker scan, axiom audit,
     PDF compile/text/render checks, and root/docs PDF byte comparison.

336.  2026-06-05, LR.1cn ordered source-head factorization for the constructed
     top-`k` right-Gram selection: closed locally with full validation.  No
     external proof source was needed.  The proof uses the local constructed
     ordered embedding, diagonal finite-sum simplification for
     `sourceSVDFactorMatrix`, `Finset.sum_map` for the selected-set reindexing,
     LR.1cm for the left head-basis orthonormality, and the local right-Gram
     eigenbasis column-orthonormality theorem for the right head basis.  It
     proves only the exact source-head factorization and head-basis fields; it
     is not a complementary tail construction, not a right-basis row-completeness
     or source-split theorem, not an Eckart--Young theorem, and not a computed
     SVD routine certificate.  Sampling probabilities and laws remain exact
     mathematical inputs.  Full validation passed locally: focused Lean and
     focused build, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

337.  2026-06-05, LR.1co ordered complement-tail factorization and source split
     for the constructed top-`k` right-Gram selection: closed locally with full
     validation.  No external proof source was needed.  The proof uses
     the local selected-set complement, `orderIsoOfFin` enumeration of that
     complement, diagonal finite-sum simplification for `sourceSVDFactorMatrix`,
     right-Gram eigenbasis column orthonormality for the tail-right table, and
     LR.1cn plus the existing selected head/tail split for the ordered source
     reconstruction.  It proves only exact source-split algebra; it does not
     supply a nullspace-completed orthonormal tail-left basis, full right-basis
     row completeness, Eckart--Young tail optimality, randomness-derived
     certificates, or computed non-probability SVD/singular-vector/projector/
     Gram/sketch routine certificates.  Sampling probabilities and laws remain
     exact mathematical inputs.  Full validation passed locally: focused Lean
     and focused build, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

338.  2026-06-05, LR.1cp ordered right-basis block completeness for the
     constructed top-`k` right-Gram partition: closed locally with full
     validation.  No external proof source was needed.  The proof uses the
     selected-set/complement finite-sum enumeration lemmas, disjointness of a
     finite set and its complement, the local right-Gram eigenbasis column
     orthonormality theorem for head/tail cross terms, and the local right-Gram
     eigenbasis row orthonormality theorem for selected-plus-complement row
     completeness.  It proves only exact right-basis block algebra; it does not
     supply a nullspace-completed orthonormal tail-left basis, Eckart--Young
     tail optimality, randomness-derived certificates, or computed
     non-probability SVD/singular-vector/projector/Gram/sketch routine
     certificates.  Sampling probabilities and laws remain exact mathematical
     inputs.  Full validation passed locally: focused Lean and focused build,
     rerun lookup example after a stale-olean race, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

339.  2026-06-05, LR.1cq constructed ordered block source-SVD certificate:
     closed locally with full validation.  No external proof source was needed.
     The proof combines the local constructed ordered source split
     `rectRightGramOrdered_source_head_add_tail`, the constructed ordered
     right-basis block theorem
     `rectRightGramOrderedRightBasisBlock_col_row_orthonormal`, the local
     left-block component assembly lemma, and the existing kth ordered
     singular-value positivity handoff for the head nonzero/head-left fields.
     It proves only the exact certificate adapter; tail-left orthonormality,
     head-tail left cross-orthogonality/nullspace completion, Eckart--Young,
     randomness-derived certificates, and computed non-probability
     SVD/singular-vector/projector/Gram/sketch routine certificates remain
     open.  Sampling probabilities and laws remain exact mathematical inputs.
     Full validation passed locally: focused Lean and focused build,
     `examples/LibraryLookup.lean`, full `lake build`, marker scan, axiom audit,
     PDF compile/text/render checks, and root/docs PDF byte comparison.

340.  2026-06-05, LR.1cr constructed ordered head-tail left cross field:
     closed locally with full validation.  No external proof source was needed.
     The proof reuses the local positive zero-safe left-column orthonormality
     theorem and the zero-safe zero-column definition.  It proves that a
     positive zero-safe left singular candidate is orthogonal to any distinct
     zero-safe candidate, specializes the result to the constructed ordered
     top-`k` selected set and complement enumeration, and packages the
     constructed block certificate so only tail-left orthonormality remains.
     It proves only the exact-object left cross field; tail-left
     orthonormality/nullspace completion, Eckart--Young, randomness-derived
     certificates, and computed non-probability SVD/singular-vector/projector/
     Gram/sketch routine certificates remain open.  Sampling probabilities and
     laws remain exact mathematical inputs.  Full validation passed locally:
     focused Lean and focused build, `examples/LibraryLookup.lean`, full
     `lake build`, marker scan, axiom audit, PDF compile/text/render checks,
     and root/docs PDF byte comparison.

341.  2026-06-05, LR.1cs positive-complement tail-left field: closed locally
     with full validation.  No external proof source was needed.  The proof
     reuses the local positive-pair zero-safe left-column orthonormality theorem
     on the complement enumeration and transports the displayed `idMatrix`
     through the injective complement order embedding.  The ordered
     specialization plus kth head positivity instantiates the constructed
     block source-SVD certificate under the additional hypothesis that every
     complement-enumerated singular value is strictly positive.  This proves
     only the exact positive-complement branch; zero-tail nullspace completion,
     Eckart--Young, randomness-derived certificates, and computed
     non-probability SVD/singular-vector/projector/Gram/sketch routine
     certificates remain open.  Sampling probabilities and laws remain exact
     mathematical inputs.  Full validation passed locally: focused Lean and
     focused build, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

342.  2026-06-05, LR.1ct zero-tail obstruction for the raw zero-safe tail-left
     table: closed locally with full validation.  No external proof source was
     needed.  The proof unfolds the zero-safe tail-left column when the
     corresponding complement singular value is zero, proves its self-dot is
     zero, contradicts the diagonal `idMatrix` value required by tail-left
     orthonormality, and lifts the contradiction through the constructed block
     source-SVD certificate.  This is route elimination only: it proves that the
     zero-tail case genuinely needs a nullspace-completed orthonormal tail-left
     basis.  Eckart--Young, randomness-derived certificates, and computed
     non-probability SVD/singular-vector/projector/Gram/sketch routine
     certificates remain open.  Sampling probabilities and laws remain exact
     mathematical inputs.  Full validation passed locally: focused Lean and
     focused build, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

343.  2026-06-05, LR.1cu replacement tail-left adapter for the zero-tail source
     split: closed locally with full validation.  No external proof source was
     needed.  The proof is algebraic: the complement-tail diagonal singular
     block erases arbitrary replacement columns at zero complement singular
     values, while the visible nonzero-direction agreement hypothesis rewrites
     replacement columns to the zero-safe columns at nonzero complement singular
     values.  The ordered specialization then feeds the same exact source split
     into the constructed block source-SVD certificate under kth head positivity,
     replacement-tail orthonormality, and replacement head-tail cross fields.
     This is an adapter only; it does not construct the nullspace-completed
     replacement basis, prove Eckart--Young, randomness-derived certificates, or
     computed non-probability SVD/singular-vector/projector/Gram/sketch routine
     certificates.  Sampling probabilities and laws remain exact mathematical
     inputs.  Full validation passed locally: focused Lean and focused build,
     `examples/LibraryLookup.lean`, full `lake build`, marker scan, axiom audit,
     PDF compile/text/render checks, and root/docs PDF byte comparison.

344.  2026-06-05, LR.1cv left-block dimension guard for equation (9): closed
     locally with full validation.  No external proof source was needed.  The
     proof bridges the repository's finite-sum column-orthonormal equations to a
     mathlib `Orthonormal` family in `EuclideanSpace`, applies the
     linear-independent cardinality bound, then specializes the result to the
     concatenated left block `[U,Utail]` and to
     `BlockDiagonalSourceSVDTailCertificate`.  This exposes the necessary side
     condition `r+q <= m`; for a full right-Gram split with `r+q=n`, the
     nullspace-completed route must expose `n <= m` or use a different
     rectangular SVD surface.  This is a dimension guard only; it does not
     construct the replacement basis, prove Eckart--Young, randomness-derived
     certificates, or computed non-probability SVD/singular-vector/projector/
     Gram/sketch routine certificates.  Sampling probabilities and laws remain
     exact mathematical inputs.  Full validation passed locally: focused Lean
     and focused build, `examples/LibraryLookup.lean`, full `lake build`,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs PDF
     byte comparison.

345.  2026-06-05, LR.1cw partial left-block completion for equation (9):
     closed locally with full validation.  No external proof source was needed
     beyond mathlib's orthonormal-basis extension theorem.  The proof first
     completes any exact partially specified orthonormal column family in `R^m`
     to a full `m x m` orthonormal table while preserving the specified
     columns, then specializes through an embedding of head/tail block indices
     into `Fin m` to construct a replacement tail-left table.  The block
     specialization preserves every specified tail column and makes `[U,Utail]`
     column-orthonormal when all head columns are included in the partial set.
     This is exact-object nullspace-completion infrastructure only; it does not
     instantiate the partial set with ordered nonzero-tail directions, compose
     with the replacement source-factor adapter, prove Eckart--Young, derive
     randomness certificates, or certify computed non-probability
     SVD/singular-vector/projector/Gram/sketch routines.  Sampling probabilities
     and laws remain exact mathematical inputs.  Full validation passed locally:
     focused Lean, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

346.  2026-06-05, LR.1cx ordered nonzero-tail completion for equation (9):
     closed locally with full validation.  No external proof source was needed.
     The proof is local exact-object algebra built on LR.1cw and LR.1cu: define
     the partial set containing all ordered head columns and exactly the nonzero
     ordered complement-tail directions, prove partial orthonormality using kth
     ordered singular-value positivity, head-tail cross-orthogonality, and
     nonzero/nonnegative tail singular values, then run orthonormal completion
     through the supplied embedding into `Fin m`.  The resulting replacement
     tail-left table agrees with the zero-safe table on every nonzero complement
     singular direction, has an orthonormal concatenated left block, and
     instantiates the ordered block source-SVD certificate through the
     replacement-tail adapter.  Eckart--Young, randomness-derived certificates,
     and computed non-probability SVD/singular-vector/projector/Gram/sketch
     routines remain open.  Sampling probabilities and laws remain exact
     mathematical inputs.  Full validation passed locally: focused Lean and
     focused build, `examples/LibraryLookup.lean`, full `lake build`, marker
     scan, axiom audit, PDF compile/text/render checks, and root/docs PDF byte
     comparison.

346.  2026-06-05, Algorithm 1 exact rectangular dilation variance proxy:
     closed locally in `ElementwiseSpectral.lean`.  The theorem family proves
     the literal, untruncated squared-magnitude one-step self-adjoint dilation
     variance scale \(\max(m,n)\|A\|_F^2/s^2\), replacing the earlier general
     rectangular Frobenius-detour proxy \(2mn\|A\|_F^2/s^2\).  It also proves
     the independent `s`-sample summed/product-law expectation and trace
     adapters at scale \(\max(m,n)\|A\|_F^2/s\).  The closed Lean names include
     `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect`,
     `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect`,
     `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect`,
     `sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect`,
     `sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect`,
     `sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect`,
     `sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect`,
     `sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect`,
     `sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect`,
     and
     `sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect`.
     This is exact-arithmetic variance infrastructure for Tropp's rectangular
     Bernstein/self-adjoint-dilation route; it does not prove the unconditional
     matrix-Bernstein/Khintchine tail theorem for CACM Algorithm 1 equation (2).
     Full validation passed: focused Lean, focused module build,
     `examples/LibraryLookup.lean`, full `lake build`, touched-file marker
     scan, axiom audit, theorem PDF compile/text check, and root/docs PDF
     byte comparison.  Sampling probabilities and laws remain exact
     mathematical inputs.

347.  2026-06-05, LR.1cy rank-nullity kernel foundation for equation (9):
     closed locally with full validation.  No external proof source was
     needed beyond mathlib finite-dimensional rank-nullity.  The proof turns a
     repository `RectRankFactorization m (r+1) r B` into the linear map
     \(x\mapsto R x:\mathbb R^{r+1}\to\mathbb R^r\), obtains a nonzero kernel
     vector from `LinearMap.ker_ne_bot_of_finrank_lt`, and then uses the
     explicit factorization `B=L R` to prove `B x=0` in the repository
     finite-sum convention.  This is the first min-max dependency for the
     Eckart--Young lower-bound route; it does not prove the singular-value
     lower bound, Frobenius tail optimality, rectangular SVD existence, or
     computed SVD/basis/projector routines.  Sampling probabilities and laws
     remain exact mathematical inputs.  Full validation passed locally:
     focused Lean, focused module build, `examples/LibraryLookup.lean`, full
     `lake build`, marker scan, axiom audit, PDF compile/text/render checks,
     and root/docs PDF byte comparison.

348.  2026-06-05, LR.1cz kernel-to-residual spectral lower-bound adapter:
     closed locally with full validation.  No external source was needed
     beyond the standard
     Eckart--Young min-max argument already cited in LR.1-SVD-2 and the local
     Frobenius matrix-vector domination theorem.  The target uses LR.1cy's
     nonzero kernel vector for a rank-`r` competitor on `r+1` right coordinates,
     rewrites `(A-B)x=A x`, and converts a supplied exact vector-action lower
     bound for `A` into `sigma <= lowRankResidualFrob A B`.  This does not yet
     prove the ordered singular-block lower bound, Frobenius tail optimality,
     rectangular SVD/source-split existence, or computed SVD/basis/projector
     routines.  Sampling probabilities and laws remain exact mathematical
     inputs.  Full validation passed locally: focused Lean, focused module
     build, `examples/LibraryLookup.lean`, full `lake build`, `git diff
     --check`, marker scan, axiom audit, PDF compile/text/render checks, and
     root/docs PDF byte comparison.

349.  2026-06-05, Algorithm 1 literal untruncated support obstruction:
     closed locally in `ElementwiseSpectral.lean`.  No external proof source
     was needed; the proof is an explicit exact `1 x 2` counterexample family.
     For every proposed scalar radius `L`, the matrix with entries `1` and
     `(|L|+2)^-1` has positive squared-magnitude denominator and samples the
     small entry with positive probability, while the exact one-step residual
     increment on that sample has magnitude `|L|+2` and violates
     `rectOpNorm2Le ... L`.  The one-step exact squared-magnitude product law
     also assigns strictly positive probability to the event that the exact
     radius-`L` spectral event fails.  The closed Lean names are
     `algorithm1SmallEntrySupportMatrix`,
     `sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos`,
     `sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos`,
     `algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq`,
     `algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le`,
     `exists_sqMagPositive_sampleResidualIncrement_entry_abs_gt`,
     `exists_sqMagPositive_sampleResidualIncrement_not_rectOpNorm2Le`, and
     `sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_smallEntry_pos`.
     This rules out instantiating the current support-aware Bernstein API for
     the literal untruncated law with a uniform deterministic support radius.
     It does not prove CACM equation (2), and it is not a floating-point
     theorem: sampling probabilities remain exact laws and no computed
     non-probability quantity is involved in this exact support obstruction.

350.  2026-06-05, LR.1da diagonal source-block vector-action lower bound:
     closed locally with focused validation.  No external source was needed
     beyond the standard
     Eckart--Young/SVD min-max chain already cited in LR.1-SVD-2 and the local
     finite-sum norm algebra.  The target should prove the exact vector-action
     hypothesis needed by LR.1cz from a diagonal source block with
     orthonormal left columns, square orthogonal right block, and displayed
     diagonal entries bounded below by `sigma`.  The Lean proof now closes the
     rectangular left-orthonormal norm identity, the diagonal squared lower
     bound, the `U Sigma V^T` action rewrite, and the final vector-action lower
     bound.  This is not a computed SVD or singular-vector theorem; computed
     non-probability routines remain separate ledger obligations.  Sampling
     probabilities and laws remain exact mathematical inputs.  Full validation
     passed locally: focused Lean, focused module build,
     `examples/LibraryLookup.lean`, full `lake build`, `git diff --check`,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs
     PDF byte comparison.

351.  2026-06-05, LR.1db supplied SVD diagonal lower-action specialization:
     closed with full validation.  No external source is needed beyond LR.1da and the
     existing local orthogonality fields for supplied exact SVD-style tables.
     The target should specialize the generic diagonal vector-action theorem to
     full square `U Sigma V^T` tables and thin-rectangular `U Sigma V^T`
     tables, under a visible lower bound on every displayed diagonal singular
     entry.  The Lean proof now closes both the square and thin-rectangular
     wrappers by direct instantiation of LR.1da.  Full validation passed:
     focused Lean, focused module build, `examples/LibraryLookup.lean`, full
     `lake build`, `git diff --check`, marker scan, axiom audit, PDF
     compile/text/render checks, and root/docs PDF byte comparison.  This
     remains exact-object source algebra only; computed
     non-probability SVD/singular-vector/projector/product routines remain
     separate ledger obligations, and sampling probabilities/laws remain exact
     mathematical inputs.

352.  2026-06-05, LR.1dc supplied SVD residual lower-bound composition:
     closed with full validation.  No external source is needed beyond LR.1cz and
     LR.1db.  The target should instantiate the vector-action hypothesis in
     the rank-nullity/min-max residual adapter using the supplied square and
     thin-rectangular diagonal source-action wrappers on `r+1` right
     coordinates.  The Lean proof now closes both composition wrappers by
     direct instantiation of LR.1cz.  Full validation passed: focused Lean,
     focused module build, `examples/LibraryLookup.lean`, full `lake build`,
     `git diff --check`, marker scan, axiom audit, PDF compile/text/render
     checks, and root/docs PDF byte comparison.  This remains exact-object algebra only; computed
     non-probability SVD/singular-vector/projector/product routines and
     sampling randomness certificates remain separate ledger obligations.

353.  2026-06-05, LR.1dd ordered source-head residual lower-bound instantiation:
     closed with full validation.  No external source is needed beyond LR.1dc
     and the local right-Gram ordering infrastructure from LR.1by--LR.1cn.  The
     theorem instantiates the thin-rectangular residual lower-bound theorem with
     `rectRightGramOrderedHeadLeft A hk`, the named ordered head diagonal, and
     an identity right block.  The proof uses
     `rectRightGramOrderedHeadLeft_col_orthonormal_of_last_pos`,
     `rectRightGramOrderedTopEmbedding_certificate`, `rectTopIndex_le_last`,
     `rectSingularValue_antitone`, and `IsOrthogonal.id`.  Full validation
     passed: focused Lean, focused module build, aggregate RandNLA rebuild,
     `examples/LibraryLookup.lean`, full `lake build`, `git diff --check`,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs
     PDF byte comparison.  This is exact-object D4 spectral infrastructure only;
     it is not full Eckart--Young, rectangular SVD existence, randomness, or an
     implementation-facing computed SVD/singular-vector/projector/Gram/sketch/
     product theorem.  Sampling probabilities and laws remain exact
     mathematical inputs.

354.  2026-06-05, LR.1de ordered one-step best-rank coefficient block:
     opened before proving.  No external source is needed beyond LR.1dd and the
     already-local supplied thin-SVD best-rank handoff
     `isBestRankApproxFrob_of_rectangularThinSVD_head_pos_sigmaTail_optimal`.
     The first target is the elementary `q=1` identity
     `frobNorm (squareSVDTailDiagonal sigma)=sigma_last` under nonnegativity of
     the displayed last tail entry.  The second target should instantiate the
     existing handoff with `rectRightGramOrderedHeadLeft A hk`,
     `rectRightGramOrderedHeadSingularDiagonal A hk`, and `idMatrix (r+1)`,
     using LR.1dd for the visible tail-optimality inequality.  This remains
     exact-object one-step D4 infrastructure, not full multi-tail
     Eckart--Young, rectangular SVD existence, randomness, or computed
     non-probability routine certification.  Sampling probabilities and laws
     remain exact mathematical inputs.  Closed by
     `frobNorm_squareSVDTailDiagonal_one` and
     `isBestRankApproxFrob_of_rectRightGramOrderedHeadDiagonal_succ`; the proof
     uses no external source beyond the locally formalized min-max LR.1dd
     lower bound and the local supplied thin-rectangular best-rank handoff.
     Full Lean, lookup, axiom-audit, marker-scan, PDF compile/text/render, and
     root-PDF sync gates passed for the scoped one-step result.

355.  2026-06-05, LR.1df multi-tail diagonal Frobenius identity:
     opened before proving.  No external source is needed; the proof should
     unfold the local `squareSVDTailDiagonal` and `frobNormSq` definitions and
     use finite-sum diagonal support to prove the displayed sum-of-squares
     identity.  This is exact-object diagonal algebra for the future
     multi-tail Eckart--Young theorem, not the q-dimensional min-max lower
     bound and not any computed non-probability routine certificate.  Sampling
     probabilities and laws remain exact mathematical inputs.  Closed by
     `frobNormSq_squareSVDTailDiagonal_eq_sum` and
     `frobNorm_squareSVDTailDiagonal_eq_sqrt_sum`; focused Lean, focused
     module build, aggregate RandNLA build, lookup, full build, marker scan,
     axiom audit, PDF compile/text/render, and root-PDF sync gates passed for
     the scoped diagonal-algebra result.

356.  2026-06-05, LR.1dg q-dimensional right-factor rank-nullity foundation:
     opened before proving.  No external source is needed; the proof should
     define the exact right-factor linear map and use the local mathlib theorem
     `LinearMap.finrank_range_add_finrank_ker` together with the range
     finrank bound into `Fin r -> Real` to prove a kernel-dimension lower bound
     `q <= finrank ker`.  A second algebraic bridge should push membership in
     that right-factor kernel through the stored `RectRankFactorization` to get
     the displayed matrix right-kernel equation for the competitor.  This is
     exact-object q-dimensional min-max infrastructure only, not vector
     selection inside the kernel, the tail Frobenius lower bound,
     rectangular-SVD/source-split existence, randomness, or computed
     non-probability routine certification.  Sampling probabilities and laws
     remain exact mathematical inputs.  Closed by `rectRankRightFactorMap`,
     `rectRankRightFactorMap_ker_finrank_ge`,
     `rectRankFactorization_rightKernel_finrank_ge`, and
     `rectRankFactorization_matrix_rightKernel_of_rightFactor_ker`; focused
     Lean validation passed with no external source beyond local mathlib
     rank-nullity and finite-dimensional range bounds.  Full Lean, lookup,
     aggregate/full build, marker-scan, axiom-audit, PDF compile/text/render,
     and root/docs PDF sync gates passed for the scoped right-kernel result.

357.  2026-06-05, LR.1dh q-dimensional right-kernel family selection:
     opened before proving.  No external source is needed; the proof should
     use the local mathlib theorem `exists_linearIndependent_of_le_finrank` on
     the kernel subtype selected by LR.1dg.  The already-proved
     `rectRankFactorization_rightKernel_finrank_ge` supplies the dimension
     hypothesis, and
     `rectRankFactorization_matrix_rightKernel_of_rightFactor_ker` supplies
     the entrywise matrix-annihilation equation for every selected subtype
     vector.  This is exact-object vector-selection infrastructure only, not
     the tail Frobenius lower bound, full Eckart--Young theorem,
     rectangular-SVD/source-split existence, randomness, or computed
     non-probability routine certification.  Sampling probabilities and laws
     remain exact mathematical inputs.  Closed by
     `rectRankFactorization_exists_rightKernelFamily`; focused Lean validation
     passed with no external source beyond local mathlib finite-dimensional
     linear-independent family selection and LR.1dg.  Full Lean, lookup,
     aggregate/full build, marker-scan, axiom-audit, PDF compile/text/render,
     and root/docs PDF sync gates passed for the scoped selected-family result.

358.  2026-06-05, LR.1di orthonormal right-kernel family selection:
     opened before proving.  No external source is needed for this selector;
     it should use the local LR.1dg-style kernel finrank lower bound together
     with mathlib's finite-dimensional `stdOrthonormalBasis` for the
     Euclidean-coordinate kernel subtype, restricted along `Fin.castLE`.  This
     is still only exact-object
     vector-selection infrastructure; the subsequent Ky Fan/Courant-Fischer
     trace/Rayleigh tail lower-bound step may require a separate proof-source
     comparison.  Closed in focused Lean by
     `rectRankRightFactorEuclideanMap`,
     `rectRankRightFactorEuclideanMap_ker_finrank_ge`,
     `rectRankFactorization_euclideanRightKernel_finrank_ge`,
     `rectRankFactorization_matrix_rightKernel_of_euclideanRightFactor_ker`,
     and `rectRankFactorization_exists_orthonormalRightKernelFamily`.
     Full Lean/lookup/build/PDF validation passed; no external proof source was
     used for this selector.  The next D4 tail lower-bound step remains a
     separate source-audit item.

359.  2026-06-05, LR.1dj orthonormal right-kernel residual-energy domination:
     opened before proving.  Use mathlib's finite Bessel inequality
     `Orthonormal.sum_inner_products_le` row-by-row to prove the Frobenius
     domination `sum_c ||M x_c||_2^2 <= ||M||_F^2` for an exact orthonormal
     right-probe family, then use the local right-kernel residual-action bridge
     to specialize from `M=A-B` to `A` on the LR.1di family.  No external proof
     source is expected for this Bessel/Frobenius layer; the source-side
     Rayleigh/Ky Fan comparison remains a later source-audit item.  Closed in
     focused Lean by `sum_vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_of_orthonormal`,
     `sum_vecNorm2Sq_rectMatMulVec_lowRankResidual_le_of_orthonormal_rightKernel`,
     and `rectRankFactorization_exists_orthonormalRightKernelFamily_energy_le`.
     Full Lean/lookup/build/axiom/PDF text/PDF render validation passed; no
     external proof source was used for this Bessel/Frobenius layer.  The
     source-side tail-energy lower bound remains a separate source-audit item.

360.  2026-06-05, LR.1dk diagonal source-side tail-energy lower bound:
     opened before proving.  Use the finite-dimensional Ky Fan/Courant-Fischer
     mass-transfer argument in diagonal form: coordinate weights of a
     `q`-frame are between zero and one, their total mass is `q`, and moving
     any missing tail coordinate mass into head coordinates cannot decrease
     energy when head diagonal squares dominate tail diagonal squares through
     a visible gap parameter.  No external proof source is expected for this
     diagonal algebra layer; instantiating the gap from ordered singular values
     and transporting through a nontrivial right singular-vector table remain
     later source-audit items.  Closed in Lean by
     `headTail_weighted_tail_sum_le_of_gap`,
     `orthonormal_sum_coord_sq_le_one`,
     `orthonormal_sum_coord_sq_eq_card`,
     `sum_vecNorm2Sq_diagonal_rectMatMulVec_eq_weighted_coord_sq`, and
     `sum_vecNorm2Sq_diagonal_rectMatMulVec_ge_tail_sq_of_orthonormal_gap`.
     Full Lean/lookup/build/axiom/PDF text/PDF render validation passed; no
     external proof source was used for this diagonal algebra layer.

361.  2026-06-05, LR.1dl ordered diagonal gap instantiation:
     opened before proving.  Use only finite index arithmetic: under an
     antitone ordered diagonal-square table, the last head square is a valid
     gap parameter for LR.1dk when `0 < r`.  This is a local adapter from the
     ordered singular-value vocabulary to the visible-gap theorem, not an
     external Ky Fan source dependency.  The zero-head edge case and transport
     through a nontrivial right singular-vector table remain later items.
     Closed without external proof sources: the finite-index adapter and the
     composed source-tail energy theorem passed focused Lean, lookup, aggregate
     and full Lake builds, marker scan, axiom audit, PDF text, and PDF render
     validation.

362.  2026-06-05, LR.1dm zero-head diagonal source-tail energy:
     opened before proving.  Use only finite orthonormal-frame and diagonal
     energy algebra: in the full `q`-dimensional right space, every coordinate
     has total squared mass one across an exact orthonormal `Fin q` family, so
     the diagonal action energy equals the displayed diagonal-square sum.  No
     external proof source is expected; this is a local finite-dimensional
     adapter, not the full Ky Fan theorem.  Closed without external proof
     sources: the full-frame coordinate-mass equality, diagonal energy
     equality, and zero-head lower-bound form passed focused Lean, lookup,
     aggregate and full Lake builds, marker scan, axiom audit, PDF text, and
     PDF render validation.

363.  2026-06-05, LR.1dn combined ordered diagonal source-tail energy:
     opened before proving.  Use only the local dichotomy `r = 0 ∨ 0 < r`,
     composing LR.1dm in the zero-head branch and LR.1dl in the positive-head
     branch.  No external proof source is expected; this is a wrapper around
     the two closed diagonal cases, not a full Rayleigh/Ky Fan theorem.
     Closed with local sources only: the combined adapter and the
     cardinal-equality zero-head helper passed focused Lean, lookup, aggregate
     and full Lake builds, marker scan, axiom audit, PDF text, and PDF render
     validation.

364.  2026-06-05, LR.1do source-factor right-basis transport:
     opened before proving.  Use only local exact linear-algebra sources:
     orthogonality preserves Euclidean inner products for `V^T`, the existing
     source-factor matrix-vector expansion, exact left column orthonormality
     of `U`, and LR.1dn.  No external proof source is expected; this is still
     below the full Eckart--Young theorem.
     Closed with local sources only: the inner-product transport lemma,
     orthonormal-family transport, source/diagonal energy equality, and summed
     LR.1dn composition passed focused Lean, lookup, aggregate and full Lake
     builds, marker scan, axiom audit, PDF text, and PDF render validation.

365.  2026-06-05, LR.1dp q-dimensional Eckart--Young lower-bound bridge:
     opened before proving.  Use only local LR.1dj residual-energy domination,
     LR.1do source-factor ordered source-tail energy, and `frobNormRect_sq`.
     No external proof source is expected; this remains a supplied-source-factor
     lower-bound bridge below SVD/source-split construction.
     Closed with local sources only: the squared lower-bound theorem and the
     square-root norm form passed focused Lean, lookup, aggregate and full Lake
     builds, marker scan, axiom audit, PDF text, and PDF render validation.

366.  2026-06-05, LR.1dq ordered supplied-SVD best-rank adapter:
     opened before proving.  Use only local LR.1dp, the displayed tail-diagonal
     Frobenius identity `frobNorm_squareSVDTailDiagonal_eq_sqrt_sum`, and the
     existing supplied square/thin SVD best-rank constructors that consume a
     tail-optimality inequality.  No external proof source is expected; this
     adapter remains exact-object supplied-SVD infrastructure and does not
     construct or compute singular vectors, projectors, Grams, sketches, or
     products.
     Closed with local sources only: the diagonal source-factor expansion,
     square/thin sigma-tail lower-bound adapters, and square/thin best-rank
     constructors passed focused Lean, lookup, aggregate and full Lake builds,
     marker scan, axiom audit, PDF text, and PDF render validation.

367.  2026-06-05, LR.1dr ordered supplied-SVD relative surface:
     opened before proving.  Use only local LR.1dq and the existing square/thin
     supplied-SVD `..._sigmaTail` relative-residual surfaces.  No external proof
     source is expected; this is a theorem-surface propagation of the newly
     proved tail-optimality inequality, not a new randomness or computed-SVD
     proof.
     Closed with local sources only: the square/thin sigma-tail antitone
     wrappers and their head-positive variants passed focused Lean, lookup,
     aggregate and full Lake builds, marker scan, axiom audit, PDF text, and PDF
     render validation.

368.  2026-06-05, LR.1ds ordered replacement-tail rank/residual surface:
     opened before proving.  Use only local LR.1cx's constructed ordered
     replacement-tail block certificate and the existing block-certificate
     equation-(9) rank/residual surface.  No external proof source is expected:
     this is an exact-object composition from the constructed ordered source
     split to the concrete Gram-inverse projector rank/residual theorem, while
     keeping determinant and cross-term hypotheses visible.  The relative
     Eckart--Young conclusion, randomness-derived cross-term certificates, and
     computed non-probability SVD/projector/Gram/sketch/product routines remain
     separate proof-source obligations.
     Closed with local sources only: the ordered replacement-tail rank surface
     passed focused Lean, focused Lake target build, lookup, aggregate RandNLA
     build, full Lake build, marker scan, axiom audit, PDF compile, PDF text,
     and PDF render validation.

369.  2026-06-05, LR.1dt ordered replacement-tail relative surface:
     opened before proving.  Use only local LR.1cx's constructed ordered
     replacement-tail block certificate and the existing block-certificate
     sigma-tail relative surface.  No external proof source is expected for
     this composition step.  It keeps the exact tail-optimality inequality and
     scalar comparison as visible hypotheses; proving those hypotheses from
     the constructed ordered singular values remains a separate Eckart--Young
     proof-source obligation.  Randomness-derived cross-term certificates and
     computed non-probability SVD/projector/Gram/sketch/product routines also
     remain separate obligations.  Closed with local sources only: focused
     Lean, lookup, aggregate RandNLA build, full Lake build, marker scan,
     axiom audit, PDF compile, PDF text, and PDF render validation passed.

370.  2026-06-05, LR.1du constructed ordered tail-diagonal Frobenius
     expansion: opened for the next D4 tail-optimality dependency after
     LR.1dt.  Use only local Frobenius definitions: first prove the reusable
     square diagonal identity `frobNormSq_diagonal_eq_sum` and its norm form,
     then specialize it to `rectRightGramOrderedTailSingularDiagonal A hk`.
     No external proof source is expected for this exact diagonal-algebra
     step.  The theorem prepares the eventual Eckart--Young lower-bound
     transport by exposing `||Sigma_tail||_F` as the square root of the
     complement singular-square sum; it does not itself prove the residual
     lower bound, randomness-derived cross-term certificates, or computed
     non-probability SVD/projector/Gram/sketch/product routines.  Closed with
     local sources only: focused Lean, lookup, full Lake build, marker scan,
     axiom audit, PDF compile, PDF text, and PDF render validation passed.
     The axiom audit for the four theorem surfaces reported only `propext`,
     `Classical.choice`, and `Quot.sound`.

371.  2026-06-05, LR.1dv constructed ordered head-tail cardinality
     bridge: opened for the next D4 reindexing dependency after LR.1du.
     Use only local selected-set cardinality plus mathlib
     `Finset.card_add_card_compl`: prove
     `rectRightGramSelectedIndexSet_card_add_compl_card` for any embedding,
     then specialize it to the constructed ordered top embedding as
     `rectRightGramOrderedTailIndex_card_add`.  No external proof source is
     expected for this finite-cardinality bridge.  The theorem prepares the
     column-reindexing/residual lower-bound transport by exposing `k+q=n`; it
     does not itself construct the column equivalence, prove the residual lower
     bound, randomness-derived cross-term certificates, or computed
     non-probability SVD/projector/Gram/sketch/product routines.  Closed with
     local sources only: focused Lean, lookup, full Lake build, marker scan,
     axiom audit, PDF compile, PDF text, and PDF render validation passed.
     The axiom audit for the two theorem surfaces reported only `propext`,
     `Classical.choice`, and `Quot.sound`.

372.  2026-06-06, LR.1dw source-factor gap lower-bound bridge:
     opened for the D4 residual lower-bound route after LR.1dv exposed
     `k+q=n`.  Use only local LR.1dk diagonal gap lower bounds, LR.1do's
     right-orthogonal/left-orthonormal source-factor transport pattern, and
     LR.1dj's residual-side orthonormal right-kernel family: prove
     `sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap`,
     then compose it with the rank-factorization residual-energy theorem as
     `rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`
     and take square roots in
     `sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap`.
     No external proof source is expected.  This theorem is exact-object
     infrastructure only: the visible head-tail gap must still be instantiated
     for the constructed ordered right-Gram source split, the original-column
     reindexing/equivalence transport remains open, and randomness-derived
     cross-term certificates plus computed non-probability
     SVD/projector/Gram/sketch/product routine certificates remain separate.
     Sampling probabilities and laws remain exact mathematical inputs.  Closed
     with local sources only: focused Lean, lookup, full Lake build, marker
     scan, axiom audit, PDF compile, PDF text, and PDF render validation
     passed.  The axiom audit for the three theorem surfaces reported only
     `propext`, `Classical.choice`, and `Quot.sound`.

373.  2026-06-06, LR.1dx constructed ordered head-tail square gap:
     opened for the D4 gap-instantiation dependency after LR.1dw and LR.1dv.
     Use only local selected-square equality, `rectSingularValueSq_antitone`,
     `rectTopIndex_le_last`, the complement-versus-selected singular-value
     comparison, basis singular-value nonnegativity, and `sq_le_sq`.  No
     external proof source is expected.  The Lean target is
     `rectRightGramOrdered_head_tail_square_gap`.  This is exact-object
     infrastructure only: it instantiates the visible separator hypothesis for
     the constructed ordered split, but it does not build column
     reindexing/equivalence transport, prove the LR.1dt tail-optimality
     discharge, derive randomness, or certify computed non-probability
     SVD/projector/Gram/sketch/product routines.  Sampling probabilities and
     laws remain exact mathematical inputs.  Closed with local sources only:
     focused Lean, focused LowRankApprox build, lookup, full Lake build,
     marker scan, axiom audit, PDF compile, PDF text, and PDF render validation
     passed.  The axiom audit for the theorem surface reported only `propext`,
     `Classical.choice`, and `Quot.sound`.

374.  2026-06-06, LR.1dy exact column-permutation transport:
     opened for the D4 column-reindexing dependency after LR.1dv/LR.1dx.
     Use only local `rectPermuteCols` and `frobNormRect_permuteCols`.  Define
     `RectRankFactorization.permuteCols`, then prove
     `RectRankAtMost.permuteCols`, `RectRankAtMost.of_permuteCols`, and
     `lowRankResidualFrob_permuteCols`.  No external proof source is expected:
     this is exact finite-index transport, not a new SVD, randomness, or
     implementation-facing floating-point argument.  The specific constructed
     `Fin (k+q) ≃ Fin n` head-plus-tail equivalence and the LR.1dt
     tail-optimality discharge remain separate obligations.  Sampling
     probabilities and laws remain exact mathematical inputs.
     Closed with local Lean only.  Focused Lean, focused LowRankApprox build,
     lookup, full Lake build, marker scan, axiom audit, PDF compile/text/render
     checks, and root/docs PDF sync passed.  The axiom audit for
     `RectRankFactorization.permuteCols`, `RectRankAtMost.permuteCols`,
     `RectRankAtMost.of_permuteCols`, and `lowRankResidualFrob_permuteCols`
     reported only `propext`, `Classical.choice`, and `Quot.sound`.

375.  2026-06-06, LR.1dz constructed ordered head-tail column equivalence:
     opened for the remaining D4 exact column-equivalence dependency after
     LR.1dv/LR.1dy.  Use only local selected-set/complement finite-index
     algebra: define `rectRightGramOrderedHeadTailColumnMap`, prove injectivity
     by disjointness of `S` and `S^c`, prove surjectivity by the selected-or-
     complement dichotomy, then package `rectRightGramOrderedHeadTailColumnSumEquiv`
     and `rectRightGramOrderedHeadTailColumnEquiv` with `finSumFinEquiv`.
     No external proof source is expected; this is exact finite reindexing, not
     an SVD, randomness, or implementation-facing floating-point argument.
     The LR.1dt tail-optimality discharge remains separate.  Sampling
     probabilities and laws remain exact mathematical inputs.
     Closed with local Lean only.  Focused Lean, focused LowRankApprox build,
     lookup, full Lake build, marker scan, axiom audit, PDF compile/text/render
     checks, and root/docs PDF sync passed.  The axiom audit for
     `rectRightGramOrderedHeadTailColumnMap`,
     `rectRightGramOrderedHeadTailColumnMap_injective`,
     `rectRightGramOrderedHeadTailColumnMap_surjective`,
     `rectRightGramOrderedHeadTailColumnSumEquiv`,
     `rectRightGramOrderedHeadTailColumnEquiv`,
     `rectRightGramOrderedHeadTailColumnEquiv_head`, and
     `rectRightGramOrderedHeadTailColumnEquiv_tail` reported only `propext`,
     `Classical.choice`, and `Quot.sound`.

376.  2026-06-06, LR.1ea cross-domain column-equivalence residual transport:
     opened for the D4 bridge needed after LR.1dz.  Define
     `rectReindexCols` for an exact equivalence `Fin p ≃ Fin n`, transport
     explicit rank factorizations and rank-at-most certificates by composing
     right factors with the equivalence, prove Frobenius norm/residual
     invariance using `Fintype.sum_equiv`, and specialize the result to
     `rectRightGramOrderedHeadTailColumnEquiv hk`.  No external proof source is
     expected: this is finite reindexing algebra, not an SVD, randomness, or
     implementation-facing floating-point argument.  Sampling probabilities and
     laws remain exact mathematical inputs.  Closed with local Lean only:
     focused Lean, focused LowRankApprox build, lookup, full Lake build,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs
     PDF sync passed.  The axiom audit for the ten theorem surfaces reported
     only `propext`, `Classical.choice`, and `Quot.sound`.

377.  2026-06-06, LR.1eb constructed ordered tail-optimality discharge:
     opened for the D4 bridge that removes LR.1dt's supplied `hopt`
     hypothesis on the constructed ordered replacement-tail path.  Use only
     local sources: the constructed ordered head-tail square gap, the
     q-dimensional gap lower-bound theorem, the constructed column equivalence,
     cross-domain residual transport, and the diagonal tail Frobenius
     expansion.  The Lean targets are
     `rectRightGramOrderedHeadTailLeftFinBlock`,
     `rectRightGramOrderedHeadTailSigmaFin`,
     `rectRightGramOrderedHeadTailRightFinBlock`,
     `rectRightGramOrderedHeadTailRightOriginalFinBlock`,
     `sourceSVDFactorMatrix_rectRightGramOrderedHeadTailFinBlock_eq_reindexCols`,
     `frobNorm_rectRightGramOrderedTailSingularDiagonal_le_lowRankResidualFrob`,
     and
     `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal`.
     No external proof source is expected: this is exact finite-index/SVD-block
     assembly from already local foundations, not a randomness or
     implementation-facing floating-point theorem.  Sampling probabilities and
     laws remain exact mathematical inputs.  Closed with local Lean only:
     focused Lean, focused LowRankApprox build, lookup, full Lake build,
     marker scan, axiom audit, PDF compile/text/render checks, and root/docs
     PDF sync passed.  The axiom audit for the eleven theorem surfaces reported
     only `propext`, `Classical.choice`, and `Quot.sound`.

377.  2026-06-06, A3.4-S9t CountSketch actual-input row-sampling endpoint:
     opened to remove the remaining orthonormal-input limitation from the
     collision-free CountSketch row-sampling path.  Proof source is local:
     reuse the already formalized right-Gram congruence route for exact
     factorizations `A = U C`, instantiate it with the exact CountSketch
     preconditioner, and compose it with the existing sparse computed
     CountSketch apply, computed uniform denominator, rounded row division, and
     rounded Gram-dot perturbation theorem.  The exact factors `U,C` are
     analysis witnesses and are not computed algorithm outputs in this theorem;
     the computed matrix is
     `fl_countSketchSparseApply fp h (rademacherSignVector Ω) A`.  No external
     proof source is needed beyond the previously recorded CountSketch
     collision-free route and the local factored-input congruence lemmas.
     Sampling probabilities and laws remain exact mathematical inputs.

378.  2026-06-06, LR.1ec scalar-relative ordered replacement-tail surface:
     opened for the exact scalar-comparison cleanup after LR.1eb.  Use only
     local ordered-ring arithmetic and Frobenius-norm nonnegativity: prove
     `two_sqrt_one_add_sq_mul_tail_le_of_scalar`, then instantiate it with the
     constructed tail norm in
     `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative`.
     No external proof source is expected.  This is exact-object theorem-surface
     cleanup only; it does not derive randomness or certify computed
     non-probability SVD/projector/Gram/sketch/product routines.  Sampling
     probabilities and laws remain exact mathematical inputs.  Closed with
     local Lean only: focused Lean, focused LowRankApprox build, lookup, full
     Lake build, marker scan, axiom audit, PDF compile/text/render checks, and
     root/docs PDF sync passed.  The axiom audit for the two LR.1ec theorem
     surfaces, plus the locally repaired Rademacher expectation lemma, reported
     only `propext`, `Classical.choice`, and `Quot.sound`.

379.  2026-06-06, A3.4-S9u non-injective CountSketch moment foundation:
     opened for the standard CountSketch variance route beyond the
     collision-free sufficient path.  Use only local finite-probability and
     finite Rademacher sources: add the generic real-valued indicator
     expectation identity, specialize exact pair-collision indicators to the
     CountSketch hash law and the full hash-sign product law, prove a
     flip-negation zero-expectation lemma, classify fourth moments of two
     ordered distinct Rademacher sign pairs, and package the result as the
     summed ordered-pair identity for
     `sum_{a != b} c_ab omega_a omega_b`.  This exact layer introduces no
     computed non-probability quantities; it is the missing sign/hash-moment
     substrate before the Gram Frobenius second-moment and Chebyshev/Loewner
     embedding theorem.  Sampling probabilities and laws remain exact
     mathematical inputs.  Closed with local Lean only: focused
     `FiniteProbability` and `Preconditioning` checks, focused
     `Preconditioning` build, lookup validation, full Lake build, marker scan,
     axiom audit, PDF compile/text/render checks, and root/docs PDF sync
     passed.  The axiom audit for the nine theorem surfaces reported only
     `propext`, `Classical.choice`, and `Quot.sound`.

380.  2026-06-06, A3.4-S9v non-injective CountSketch Frobenius/Markov sparse
     Gram FP endpoint: opened to turn S9u's exact sign/hash moments into an
     actual, non-conditional Algorithm 3 sparse Gram result.  Proof source is
     local finite algebra and finite probability only.  First prove the exact
     sketched Gram-entry error identity
     `rowGram_preconditionRows_countSketchRows_sub_rowGram_eq_distinctPair_sum`,
     reducing the real error to an ordered off-diagonal collision/sign sum.
     Then simplify the fourth-moment kernel by introducing the ordered-pair
     reversal equivalence and proving
     `countSketchDistinctPair_fourKernel_sum_le_two_sum_sq`.  Combining this
     with exact hash collision expectation gives
     `countSketchProbability_expectationReal_rowGram_entry_error_sq_le`;
     summing entries gives
     `countSketchProbability_expectationReal_rowGram_frob_error_sq_le`, and
     finite Markov gives
     `countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub`.
     The computed-object theorem
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub`
     uses the concrete sparse Gram arithmetic theorem
     `fl_countSketchSparseGramDot_perturb_bound`, so no generic perturbation
     certificate is assumed.  The readable simplification
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm`
     replaces the coefficient sum by `||A||_F^4`, and
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_frob_error_le_ge_one_sub_orthonormal`
     specializes this to `2 n^2/(r eta^2)` for `U^T U = I`.  This closes a
     non-injective Frobenius/Markov route and charges sparse signed products,
     bucket accumulation, and Gram dot products; it is still weaker than the
     standard CountSketch Loewner/subspace-embedding theorem and does not yet
     compose downstream uniform-row sampling or close the complete
     input-sparsity Algorithm 3 theorem.  Sampling probabilities and laws
     remain exact mathematical inputs.

381.  2026-06-06, A3.4-S9w non-injective CountSketch finite-Loewner sparse
     Gram FP endpoint: opened to turn S9v's computed Frobenius event into the
     two-sided Loewner geometry event needed by Algorithm 3 statements.  The
     new event `countSketchFlSparseGramDotRowGramTwoSidedLoewnerEvent` uses the
     same realized radius `eta + countSketchSparseGramFullFpPerturbBudget`.
     The deterministic theorem
     `countSketchFlSparseGramDotRowGramFrobErrorEvent_subset_twoSidedLoewnerEvent`
     applies the local Frobenius-to-operator bridge
     `finiteLoewnerLe_two_sided_add_of_frobNorm_le` with zero exact error.
     The probability wrappers
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_ge_one_sub`,
     `..._frobNorm`, and `..._orthonormal` inherit the exact, simplified, and
     orthonormal S9v failure terms, respectively.  Focused Lean, focused build,
     and lookup validation passed before ledger promotion.  This is still a
     Markov/Frobenius-derived Loewner endpoint, not the optimal CountSketch
     subspace-embedding concentration theorem or downstream uniform-row
     composition.  Sampling probabilities and laws remain exact mathematical
     inputs.

382.  2026-06-06, A3.4-S9x general iid uniform-row Frobenius/Markov
     sample-Gram foundation: opened to remove the hidden orthonormal-column
     restriction from the downstream row-sampling foundation needed after
     non-injective CountSketch.  For an arbitrary exact matrix `M`, Lean now
     proves the one-row mean identity
     `uniform_rowOuterGramSample_mean_eq_rowGram`, the iid sample-average
     variance identity
     `uniformRowTraceProbability_expectationReal_sampleAverage_sub_mean_sq`,
     the coordinate sample-Gram formula
     `uniformRowTraceProbability_expectationReal_uniformRowSampleGram_entry_error_sq`,
     the raw row-fourth moment
     `uniformRowOuterGramSample_total_second_moment`, the Frobenius
     simplification `rowNormSq_sq_sum_le_frobNormSqRect_sq`, and the final
     exact/simplified Markov events
     `uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub`
     and
     `uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm`.
     The exact failure term is
     `m * sum_i rowNormSq M i ^ 2 / (s * eta^2)`, with simplified upper
     radius `m * ||M||_F^4 / (s * eta^2)` and corresponding nonzero
     \(\Theta\)-orders.  Focused `lake env lean
     LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSampling.lean` and focused
     module build passed before ledger promotion.  This is exact-law and
     exact-arithmetic infrastructure only; it deliberately does not charge
     floating-point arithmetic until composed with concrete computed
     preconditioned matrices, row-scaling denominators, and rounded
     sample-Gram dot products.  Sampling probabilities and laws remain exact
     mathematical inputs.

383.  2026-06-06, A3.4-S9y general iid uniform-row floating-point
     Frobenius sample-Gram endpoint: opened to compose the arbitrary-matrix
     S9x exact row-sampling foundation with the concrete rounded sampled-Gram
     arithmetic in `UniformRowSamplingFP.lean`.  Lean now defines the exact
     row-Gram Frobenius event
     `uniformRowSampleGramRowGramFrobErrorEvent`, the exact-denominator
     floating-point event
     `uniformRowFlSampleGramDotRowGramFrobErrorEvent`, and the
     computed-denominator event
     `uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent`.
     The subset theorems
     `uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot` and
     `uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen`
     use the concrete perturbation bounds for rounded row divisions,
     computed denominators, and rounded length-`s` dot products.  The final
     probability theorems
     `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub`,
     `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm`,
     `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub`,
     and
     `uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm`
     keep the exact S9x Markov probability terms while enlarging the radius
     by the explicit sample-dependent FP budgets.  Focused `lake env lean
     LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`,
     focused `lake build
     LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP`, and
     `lake env lean examples/LibraryLookup.lean` passed before ledger
     promotion.  This closes the generic uniform-row sampled-Gram computation
     for arbitrary exact inputs; composing a concrete non-injective
     CountSketch-computed preconditioned matrix into this endpoint remains
     the next Algorithm 3 frontier.  Sampling probabilities and laws remain
     exact mathematical inputs.

384.  2026-06-06, A3.4-S9z non-injective CountSketch plus downstream
     uniform-row FP Frobenius endpoint: opened to close the frontier left by
     S9y without reverting to the collision-free hash event.  `Preconditioning`
     now proves the exact bucket partition identity
     `countSketchBucket_sum_sum_eq` and the deterministic Frobenius growth
     bound `frobNormSqRect_preconditionRows_countSketchRows_le`, namely
     \(\|S_{h,\omega}A\|_F^2\le m\|A\|_F^2\) for exact signs with
     \(|\omega_k|\le1\).  `UniformRowSamplingFP.lean` now defines the exact
     product event `countSketchUniformRowSampleGramRowGramFrobEvent`, the
     computed event
     `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent`,
     proves the exact product-law theorem
     `countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub`,
     and proves the implementation-facing theorems
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub`
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm`.
     The simplified failure loss is
     `2 * ||A||_F^4 / (r * etaCS^2) + r * m^2 * ||A||_F^4 / (s * etaRow^2)`,
     and the final computed radius is
     `etaCS + etaRow + countSketchSparseUniformRowComputedDenPerturbBudget`.
     Focused `lake env lean` checks for `Preconditioning.lean` and
     `UniformRowSamplingFP.lean`, focused module builds, and
     `lake env lean examples/LibraryLookup.lean` passed before ledger
     promotion.  This closes a non-injective CountSketch plus downstream
     uniform-row implementation endpoint with sparse apply, computed
     denominator, rounded row divisions, and rounded sampled-Gram dot products
     charged.  It remains Markov/Frobenius-derived rather than the optimal
     CountSketch finite-Loewner/subspace-embedding theorem.  Sampling
     probabilities and laws remain exact mathematical inputs.

385.  2026-06-06, A3.4-S9za downstream non-injective CountSketch finite-Loewner
     promotion: opened to give the fully computed S9z pipeline a geometric
     two-sided event.  `UniformRowSamplingFP.lean` now defines
     `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent`,
     proves the deterministic subset
     `countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent`,
     and exposes the exact-coefficient and simplified probability theorems
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub`
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm`.
     The event states
     \(-\tau I\preceq\widehat G_{\rm CS+row}^{fp}-A^TA\preceq\tau I\)
     with
     \(\tau=\eta_{\rm CS}+\eta_{\rm row}+T_{\rm CS,row}^{fp}\), and keeps the
     same simplified loss order
     \(\Theta(\|A\|_F^4/(r\eta_{\rm CS}^2)+r m^2\|A\|_F^4/(s\eta_{\rm row}^2))\).
     Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`
     and focused `lake build LeanFpAnalysis.FP.Algorithms.RandNLA.UniformRowSamplingFP`
     passed before ledger promotion.  This is a local Frobenius-to-Loewner
     transfer after all computed sparse apply, computed denominator, row
     division, and Gram-dot arithmetic has already been charged; it remains
     Markov/Frobenius-derived rather than optimal CountSketch concentration.

386.  2026-06-06, A3.4-S9zb downstream non-injective CountSketch sample-budget
     wrappers: opened to make the S9za probability statement directly
     interpretable in the final theorem surface.  `UniformRowSamplingFP.lean`
     now proves
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget`,
     which replaces the displayed readable loss by an explicit target
     failure probability \(\delta\), and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget`,
     which sets \(\eta_{\rm CS}=\eta_{\rm row}=\varepsilon/2\).  The equal
     split gives exact Loewner radius contribution \(\varepsilon\), leaving
     the final realized radius \(\varepsilon+T_{\rm CS,row}^{fp}\), and expands
     the sufficient loss condition to
     \(8\|A\|_F^4/(r\varepsilon^2)+4r m^2\|A\|_F^4/(s\varepsilon^2)\le\delta\),
     with order
     \(\Theta(\|A\|_F^4/(r\varepsilon^2)+r m^2\|A\|_F^4/(s\varepsilon^2))\).
     Focused `lake env lean LeanFpAnalysis/FP/Algorithms/RandNLA/UniformRowSamplingFP.lean`
     passed before ledger promotion.  This corollary does not add a
     perturbation-event or certificate-existence assumption; it only packages
     the already proved S9za loss into a non-vacuity/sample-size display.

386a. 2026-06-07, A3.4-S9zc downstream non-injective CountSketch
     exact-coefficient target-budget wrappers: opened to keep the sharper S9za
     coefficient loss available as a direct \(1-\delta\) theorem surface,
     rather than forcing users through the readable Frobenius upper bound.
     `UniformRowSamplingFP.lean` now proves the generic computed-denominator
     wrappers
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget`,
     plus the concrete denominator wrappers
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget`
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget`.
     The generic budget is
     \(2r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/\eta_{\rm CS}^2
     +r m^2\|A\|_F^4/(s\eta_{\rm row}^2)\le\delta\); the equal-radius
     budget is
     \(8r^{-1}\sum_{j,k,a\ne b}(A_{aj}A_{bk})^2/\varepsilon^2
     +4r m^2\|A\|_F^4/(s\varepsilon^2)\le\delta\), with irreducible order
     \(\Theta(r^{-1}\sum(A_{aj}A_{bk})^2/\varepsilon^2
     +r m^2\|A\|_F^4/(s\varepsilon^2))\).  Validation passed: focused
     Lean, focused module build, executable lookup after module rebuild,
     aggregate RandNLA build, full `lake build`, marker scan, no-proof-sketch
     wording scan, `git diff --check`, temporary axiom audit with only
     `[propext, Classical.choice, Quot.sound]`, and master summary PDF
     rebuild/text search.  This is still the Markov/Frobenius-derived
     non-injective route; it does not prove optimal CountSketch concentration.

386b. 2026-06-07, A3.4-S9u2 fixed-vector CountSketch quadratic-form moment
     foundation: opened to sharpen the non-injective CountSketch route before
     attempting a finite-cover or uniform subspace-embedding theorem.
     `Preconditioning.lean` now proves the exact one-column bridge
     `finiteQuadraticForm_rowGram_preconditionRows_sub_rowGram_eq_rowGram_singleton_error`
     and the product-law moment theorem
     `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le`.
     For exact \(A\) and fixed exact \(x\), the theorem gives
     \(E[(x^T((SA)^T(SA)-A^TA)x)^2]\le
     2r^{-1}\sum_{a\ne b}((Ax)_a(Ax)_b)^2\).  The readable wrappers are
     `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_vecNorm`
     and
     `countSketchProbability_expectationReal_rowGram_quadratic_error_sq_le_frobNorm`,
     giving \(2\|Ax\|_2^4/r\) and
     \(2\|A\|_F^4\|x\|_2^4/r\).  The tail wrappers
     `countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub`
     and
     `countSketchProbability_eventProb_abs_rowGram_quadratic_error_le_ge_one_sub_delta_of_coeff_budget`
     expose the direct \(1-\delta\) condition
     \(2r^{-1}\sum_{a\ne b}((Ax)_a(Ax)_b)^2/\eta^2\le\delta\).  The
     irreducible loss has order
     \(\Theta(r^{-1}\sum_{a\ne b}((Ax)_a(Ax)_b)^2/\eta^2)\), with readable
     \(O(\|Ax\|_2^4/(r\eta^2))\).  Validation passed: focused Lean,
     focused module build, executable lookup, aggregate RandNLA build, full
     `lake build`, marker scan, no-proof-sketch wording scan, `git diff
     --check`, temporary axiom audit with only `[propext, Classical.choice,
     Quot.sound]`, and master summary PDF rebuild/text search.  This is exact
     probability and exact arithmetic only; it does not charge floating-point
     operations and does not yet prove a uniform CountSketch embedding theorem.

387.  2026-06-06, A3.4-S9j finite signed-mixing total-failure wrapper:
     opened to expose the actual-input finite signed-mixing computed-denominator
     endpoint as a single target-failure theorem.  `UniformRowSamplingFP.lean`
     now proves
     `signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget`,
     deriving the direct \(1-\delta\) lower bound from the already proved
     \(1-(\delta_{\rm pre}+\delta_{\rm sample})\) theorem under the explicit
     arithmetic budget \(\delta_{\rm pre}+\delta_{\rm sample}\le\delta\).
     The theorem keeps the same fully computed event: rounded
     `G * diag(sign)`, rounded left preconditioning, computed uniform
     denominator, rounded row divisions, and rounded Gram dot products are
     charged by the existing concrete budget.  Exact Rademacher and uniform-row
     laws remain exact mathematical laws by convention.  No perturbation-event,
     certificate-existence, or extra computation assumption is introduced.

388.  2026-06-06, A3.4-S9t CountSketch actual-input target-failure wrapper:
     opened to expose the collision-free actual-input CountSketch computed
     endpoint as a single target-failure theorem.  `UniformRowSamplingFP.lean`
     now proves
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget`,
     deriving the direct \(1-\delta\) lower bound from the existing
     \(1-(m^2/r+\delta_{\rm sample})\) theorem under the explicit arithmetic
     budget \(m^2/r+\delta_{\rm sample}\le\delta\).  The computed event is
     unchanged: sparse rounded CountSketch apply to the actual input
     \(A=UC\), computed uniform denominator, rounded row divisions, and rounded
     Gram dot products are all charged by the concrete budget.  Exact hash,
     sign, and row-sampling laws remain exact mathematical laws; \(U,C\) are
     analysis witnesses, not computed outputs.

389.  2026-06-10, A3.4-S9zp generated-FHT stored actual-input paths:
     no external source was used.  The local theorem
     `signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`
     combines the existing computed-left/input product budget with the
     computed uniform-denominator sampled-Gram budget.  The final endpoints
     `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputMulOneComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`,
     `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputAddZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`,
     and
     `signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputSubZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`
     instantiate the actual input storage certificates
     `ComputedMatrix.flMulOne fp A`, `ComputedMatrix.flAddZeroRight fp A`, and
     `ComputedMatrix.flSubZeroRight fp A`, so the implementation computes
     `Ahat_ij = fl_mul A_ij 1`, `fl_add A_ij 0`, or `fl_sub A_ij 0` before
     forming `fl(Pihat*Ahat)`.  The proofs are local algebra from
     `ComputedMatrix.flMulOne_entry_error_bound`,
     `ComputedMatrix.flAddZeroRight_entry_error_bound`,
     `ComputedMatrix.flSubZeroRight_entry_error_bound`,
     `fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound`,
     `fl_uniformRowSampleGramDotWithComputedDen_perturb_bound`, and the
     existing source-sharp SRHT theorem for the exact analysis witnesses
     \(A=UC\).  Exact Rademacher and uniform-row laws remain exact
     mathematical laws; no perturbation-event hypothesis, certificate-existence
     assumption, supplied orthogonality witness, supplied flatness witness, or
     generic denominator remains in the final theorems.  Other actual-input
     storage formats remain separate implementation paths unless selected.

390.  2026-06-11, A3.4-S9zr CountSketch product-grid finite-cover
     wrappers: no external source was used.  `MatrixAlgebra.lean` now proves
     `finiteUnitBallCover_of_rectUnitBallCover` and
     `finiteUnitBallCover_product_grid`, converting an exact
     one-dimensional interval cover into the coordinatewise product grid
     `z_a(j)=grid (a j)` over `a : Fin n -> alpha`; the existing
     `fintype_card_product_grid_index` gives the cardinality `|alpha|^n`.
     `Preconditioning.lean` instantiates the existing exact finite-cover
     CountSketch Loewner theorem as
     `countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
     and
     `countSketchProbability_eventProb_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     then transfers the same explicit grid loss to the computed sparse Gram
     event through
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`
     and
     `countSketchProbability_eventProb_flSparseGramDot_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`.
     The probability loss is
     `sum_{a : Fin n -> alpha} 2*||A*z_a||_2^4/(r*eta^2)
      + 2*||A||_F^4/(r*L^2)`, with exact Loewner radius
     `eta + L*(2*rho + rho^2)` and computed sparse-Gram radius enlarged by
     `T_CSGram_fp(h, omega, A)`.  Exact hash/sign laws and the exact product
     grid remain analysis objects.  The computed endpoint charges sparse
     signed products, bucket accumulation, and rounded Gram dot products
     through the already proved sparse-Gram budget under `gammaValid fp m`
     and `gammaValid fp r`; it uses no supplied finite-cover certificate,
     perturbation-existence event, or probability-computation floating-point
     term.  This remains a Markov/Frobenius finite-cover route, not the
     optimal CountSketch subspace-embedding concentration theorem.

391.  2026-06-11, A3.4-S9zs downstream CountSketch product-grid wrappers:
     no external source was used.  `UniformRowSamplingFP.lean` now proves
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`,
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
     These theorems instantiate the existing downstream finite-cover
     CountSketch-plus-uniform-row FP endpoint with the product grid
     `z_a(j)=grid (a j)` over `a : Fin n -> alpha`, using
     `finiteUnitBallCover_product_grid` and the nonnegativity consequence of
     `sqrt(n)*deltaGrid <= rho`.  The computed event keeps the same charged
     downstream radius: exact CountSketch cover radius
     `eta + L*(2*rho + rho^2)`, exact downstream row-sampling radius
     `etaRow`, plus the realized `countSketchSparseUniformRowComputedDenPerturbBudget`
     for sparse apply, denominator formation, sampled-row divisions, and
     sampled-Gram dot products.  The exact product-grid loss is
     `sum_{a : Fin n -> alpha} 2*r^{-1}*sum_{p != q}
      ((A*z_a)_p*(A*z_a)_q)^2/eta^2
      + 2*r^{-1}*sum_{j,k,p != q}(A_pj*A_qk)^2/L^2
      + r*m^2*||A||_F^4/(s*etaRow^2)`.  The concrete-denominator wrapper
     selects the already proved routine
     `fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`.
     Exact hash/sign laws, exact row-sampling laws, and the product grid
     remain analysis objects; no supplied finite-cover certificate,
     perturbation-existence event, or probability-computation FP term is used.
     This closes the explicit product-grid adapter for the downstream
     Markov/Frobenius CountSketch-plus-uniform-row route, not the optimal
     CountSketch subspace-embedding concentration theorem.

392.  2026-06-11, A3.4-S9zt CountSketch stored-sign sparse-Gram arithmetic:
     no external source was used.  This is deterministic floating-point
     storage/arithmetic infrastructure.  `Preconditioning.lean` now proves
     `preconditionRows_countSketchRows_storedSign_entry_error_bound`,
     `fl_countSketchSparseApplyEntry_withStoredSign_error_bound`,
     `fl_countSketchSparseApplyWithStoredSign_entry_error_bound`, and
     `fl_countSketchSparseGramDotWithStoredSign_perturb_bound`.  For a
     computed sign table `signhat : ComputedVector fp sign`, the sparse-apply
     radius is the previous sparse arithmetic term with `signhat.vector` plus
     the explicit storage contribution
     `sum_t signhat.abs_error (bucketIndex t) * |A_(bucketIndex t),j|`.
     The stored-sign Gram theorem then threads this entrywise radius through
     rounded length-`r` Gram dot products using the existing
     `fl_rowSketchGramDot_abs_perturb_bound_exact` interface.  The concrete
     wrappers
     `fl_countSketchSparseGramDotWithFlStoredSign_perturb_bound`,
     `fl_countSketchSparseGramDotWithFlStoredSignAddZeroRight_perturb_bound`,
     and
     `fl_countSketchSparseGramDotWithFlStoredSignSubZeroRight_perturb_bound`
     instantiate `signhat` by the already proved `fl_mul sign_i 1`,
     `fl_add sign_i 0`, and `fl_sub sign_i 0` sign-storage constructors, whose
     absolute-one Rademacher radius is `u`.  Exact hash/sign laws remain exact
     analysis/probability objects; this row charges only non-probability sign
     storage, sparse signed products, bucket accumulation, and Gram dot
     products.  The high-probability product-grid wrapper whose event radius
     uses this stored-sign Gram budget is closed in A3.4-S9zu.

393.  2026-06-11, A3.4-S9zu CountSketch product-grid stored-sign sparse-Gram
     probability wrapper: no external source was used beyond the already
     recorded CountSketch finite-cover/product-grid Markov/Frobenius route.
     `Preconditioning.lean` now exposes
     `countSketchFlSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent`,
     `countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignRowGramTwoSidedLoewnerEvent`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSign_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignAddZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     and
     `countSketchProbability_eventProb_flSparseGramDotWithFlStoredSignSubZeroRight_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`.
     The subset theorem deterministically transfers the exact finite-cover
     CountSketch Loewner event to the computed event with radius
     `eta + L*(2*rho + rho^2) + T_CSGram_stored(h, omega, A)`, where the last
     term is the S9zt stored-sign sparse-Gram perturbation budget.  The
     probability wrappers instantiate the exact product grid
     `z_a(j) = grid (a j)` and preserve the exact-law failure loss
     `sum_a 2*||A*z_a||_2^4/(r*eta^2) + 2*||A||_F^4/(r*L^2)`, with target
     probability at least `1-delta` whenever that displayed loss is at most
     `delta`.  The concrete final wrappers select the three modeled sign-copy
     modes `fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0`.
     Exact hash/sign laws, exact product-grid vectors, and exact sampling
     probabilities remain analysis objects.  Computed non-probability objects
     are the stored sign table, sparse products, bucket accumulations, and
     rounded Gram dot products.  The result remains Markov/Frobenius-derived
     and does not close the optimal CountSketch subspace-embedding
     concentration theorem, hash-generation/storage arithmetic, or parallel
     reassociation or aliasing sparse-sketch memory-layout semantics beyond
     the sparse-Gram tree route closed in S9zz, the fixed per-bucket
     permutations closed in S9zx, and the downstream tree-reduced composition
     closed in S9zza.

394.  2026-06-11, A3.4-S9zx CountSketch product-grid stored-sign
     permuted-bucket sparse-Gram wrapper: no external source was used beyond
     the recorded CountSketch finite-cover/product-grid Markov/Frobenius route
     and the local Higham-style sparse arithmetic model.  `Preconditioning.lean`
     now exposes
     `countSketchFlSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent`,
     `countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignPermutedRowGramTwoSidedLoewnerEvent`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSignPermuted_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     and the three concrete `fl_mul sign_i 1`, `fl_add sign_i 0`, and
     `fl_sub sign_i 0` stored-sign copy wrappers with `Permuted` in their
     names.  The exact bucket order is a discrete realized-index choice, not a
     floating-point real computation.  The deterministic radius charges stored
     signs, rounded signed products, left-to-right accumulation in that chosen
     bucket order, and rounded length-`r` Gram dot products.  The exact
     product-grid probability loss is unchanged from S9zu, with order
     `Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)` in the fixed
     exact-input/grid/threshold regime.  This closes fixed per-bucket
     permutation layouts; tree-reduced sparse Gram is closed separately in
     S9zz, and the downstream tree-reduced composition is closed in S9zza.
     Parallel reassociation, aliasing, and lower-level hash/sign
     generation/storage formats remain separate implementation routines or
     open source rows.

395.  2026-06-11, A3.4-S9zv CountSketch product-grid stored-sign downstream
     uniform-row wrappers: no external source was used beyond the already
     recorded product-grid CountSketch finite-cover Markov/Frobenius route,
     the stored-sign sparse-apply arithmetic in S9zt, and the local
     computed-denominator uniform-row sampled-Gram perturbation route.
     `UniformRowSamplingFP.lean` now exposes
     `countSketchSparseComputedPreconditionedBasisWithStoredSign`,
     `countSketchSparseUniformRowComputedDenStoredSignPerturbBudget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
     `countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
     The probability-one perturbation theorem composes the stored-sign sparse
     apply entrywise budget, the basis perturbation bridge for sampled Grams,
     and the computed-denominator row-sampling perturbation theorem.  The
     final product-grid wrappers preserve the exact product-grid CountSketch
     loss and the exact downstream uniform-row loss; the radius is
     `eta + L*(2*rho + rho^2) + etaRow + T_CS_row_store(h, omega, sigma, A)`.
     Exact hash/sign laws, exact product-grid vectors, exact downstream row
     laws, and the reference `A^T*A` remain exact analysis/probability
     objects.  Computed non-probability objects are the stored sign table,
     rounded sparse products, bucket accumulations, the concrete denominator
     for `sqrt(s/r)`, row divisions, and sampled-Gram dot products.  The
     remaining Algorithm 3 CountSketch targets are optimal CountSketch
     concentration, lower-level hash-generation/storage arithmetic, and
     parallel reassociation or aliasing sparse-sketch memory layouts beyond
     the sparse-Gram tree route closed in S9zz, the downstream tree-reduced
     composition closed in S9zza, and the fixed per-bucket permutations closed
     in S9zx.

396.  2026-06-11, A3.4-S9zw CountSketch product-grid stored-sign downstream
     alternate denominator-route wrappers: no external source was used beyond
     the already recorded S9zv stored-sign downstream theorem, the generic
     computed-denominator transfer theorem, and the local concrete denominator
     certificates.  `UniformRowSamplingFP.lean` now exposes
     `uniformRowFlSqrtExactInputScaleDen`,
     `uniformRowFlDivThenSqrtScaleDen`,
     `uniformRowFlInvMulThenSqrtScaleDen`,
     `uniformRowFlSqrtDivSqrtScaleDen`, and the corresponding stored-sign
     downstream product-grid wrappers
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtExactInputDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlDivThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlInvMulThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtDivSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
     The exact product-grid CountSketch loss and exact downstream uniform-row
     loss are unchanged.  These wrappers only replace the deterministic
     denominator component in the stored-sign row-scaling radius by the
     route-specific factors `u`, `sqrt(1+u)*u + u`,
     `sqrt((1+u)*(1+u))*u + 2*u + u^2`, or `(3*u + u^2)/(1-u)`.
     The exact-input square-root route requires the scalar ratio `s/r` to be
     supplied exactly; when the ratio is computed in floating point, the
     divide/multiply routes are the fully rounded alternatives.  Exact
     hash/sign laws, exact product-grid vectors, exact downstream row laws,
     exact input `A`, and the reference `A^T*A` remain exact analysis and
     probability objects; stored signs, sparse products, bucket accumulation,
     denominator formation, row divisions, and sampled-Gram dot products are
     computed and charged.

397.  2026-06-11, A3.4-S9zy CountSketch product-grid stored-sign
     permuted-bucket downstream uniform-row wrappers: no external source was
     used beyond the S9zx fixed per-bucket sparse-apply/Gram arithmetic, the
     S9zv stored-sign downstream theorem shape, and the local computed
     denominator sampled-Gram perturbation route.  `UniformRowSamplingFP.lean`
     now exposes
     `countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted`,
     `countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
     `countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and the three concrete stored-sign copy wrappers
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
     The exact bucket order is a realized discrete index operation and adds no
     probability loss.  The final radius is
     `eta + L*(2*rho + rho^2) + etaRow
     + T_CS_row_store_pi(h, omega, sigma, A)`, charging stored signs, rounded
     sparse products, accumulation in the chosen bucket order, the concrete
     denominator for `sqrt(s/r)`, row divisions, and sampled-Gram dot
     products.  Exact hash/sign laws, exact product-grid vectors, exact
     downstream row laws, exact input `A`, exact bucket order, and `A^T*A`
     remain exact analysis/probability or discrete objects.  This closes fixed
     per-bucket permutation layouts for the stored-sign downstream path; the
     tree-reduced downstream path is closed in S9zza.  Parallel
     reassociation, aliasing sparse-sketch layouts, lower-level hash/sign
     generation and storage formats, and optimal CountSketch concentration
     remain separate targets.

398.  2026-06-11, A2.8stored Algorithm 2 leverage stored-basis endpoint:
     no new external concentration theorem was used beyond the already
     recorded equation (7) source chain: Drineas--Mahoney's CACM Algorithm 2
     statement, Drineas--Mahoney--Muthukrishnan--Sarlos leverage sampling,
     Oliveira/Tropp rank-one matrix concentration, and Higham-style
     floating-point arithmetic.  The new proof is a deterministic local
     floating-point transfer layered on the already closed Bennett
     sample-budget theorem.  `RowSamplingLeverageComputedBasis.lean` now
     exposes `leverageExactBasisSampleColumnAbsBudget`,
     `leverageComputedBasisSampleColumnEntryBudget`,
     `leverageComputedBasisSampleColumnErrorBudget`,
     `rowSketchGramFullAbsFpColumnBudget`,
     `leverageComputedBasisDenGramBudget`,
     `fl_rowSampleSketchWithComputedBasisDen_abs_error_bound`,
     `fl_rowSketchGramDot_abs_perturb_bound_of_column_budget`,
     `leverage_fl_rowSampleGramDotWithComputedBasisDen_perturb_bound`,
     the generic computed-basis/computed-denominator probability theorem, and
     the three final stored-basis wrappers for `fl_mul U_ij 1`,
     `fl_add U_ij 0`, and `fl_sub U_ij 0` combined with
     `leverageFlMulThenSqrtRowScaleDen`.  The exact orthonormal basis `U`,
     leverage law, samples, and identity reference remain analysis/probability
     objects.  Computed non-probability objects are the stored basis table, the
     concrete denominator, rounded sampled-row divisions, and rounded
     sampled-Gram dot products.  The theorem sheet expands the deterministic
     radius to
     `(gamma_s*(1+lambda_U)^2 + 2*lambda_U + lambda_U^2) *
     sum_j (sum_{i:p_i>0} |U_ij|/sqrt(p_i))^2` with `lambda_U` fully
     substituted from `u` and the concrete denominator routine, and records the
     fixed-problem `Theta((gamma_s + u*(1+support_size))*column_factor)` order.
     QR/SVD or other generation of `U` from a data matrix remains a separate
     concrete `ComputedMatrix` routine obligation.

399.  2026-06-11, A3.4-S9zz CountSketch product-grid stored-sign
     tree-reduced sparse-Gram wrapper: no external source was used beyond the
     already recorded CountSketch finite-cover/product-grid Markov/Frobenius
     route, the local `SumTree.forward_error` theorem, and the local
     Higham-style sparse arithmetic model.  `Preconditioning.lean` now exposes
     `fl_countSketchSparseApplyEntryTree_error_bound`,
     `fl_countSketchSparseApplyTree_entry_error_bound`,
     `fl_countSketchSparseGramDotTree_perturb_bound`,
     `fl_countSketchSparseApplyWithStoredSignTree_entry_error_bound`,
     `fl_countSketchSparseGramDotWithStoredSignTree_perturb_bound`,
     the concrete tree-reduced sign-copy Gram wrappers
     `fl_countSketchSparseGramDotWithFlStoredSignTree_perturb_bound`,
     `fl_countSketchSparseGramDotWithFlStoredSignAddZeroRightTree_perturb_bound`,
     and
     `fl_countSketchSparseGramDotWithFlStoredSignSubZeroRightTree_perturb_bound`,
     plus the product-grid probability surface
     `countSketchFlSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent`,
     `countSketchRowGramTwoSidedLoewnerCoverEvent_subset_flSparseGramDotWithStoredSignTreeRowGramTwoSidedLoewnerEvent`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_vecNorm_add_frobNorm`,
     `countSketchProbability_eventProb_flSparseGramDotWithStoredSignTree_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_vecNorm_add_frobNorm_budget`,
     and the three concrete `Tree` product-grid sign-copy wrappers for
     `fl_mul sign_i 1`, `fl_add sign_i 0`, and `fl_sub sign_i 0`.  The exact
     binary tree shape for each realized bucket, including the trailing zero
     leaf, is a discrete algorithm choice and adds no probability loss.  The
     deterministic radius charges sign storage, rounded signed products,
     tree-depth bucket accumulation, and rounded length-`r` Gram dot products.
     The final event radius is
     `eta + L*(2*rho + rho^2) + T_CSGram_store_tree(h, omega, tree, A)`, and
     the exact product-grid loss remains
     `sum_a 2*||A*z_a||_2^4/(r*eta^2) + 2*||A||_F^4/(r*L^2)`, with
     `Theta((sum_a ||A*z_a||_2^4/eta^2 + ||A||_F^4/L^2)/r)` probability-loss
     order for fixed exact input/grid/threshold data and nonzero numerator.
     For fixed realized data, the tree entry budget has order
     `Theta((u + gamma_depth_i)*bucket_column_one_norm)`, and balanced bucket
     trees give the more interpretable
     `Theta(u*(1 + log(bucket_size_i + 1))*bucket_column_one_norm)` order.
     Exact hash/sign laws, exact product-grid vectors, exact input `A`, tree
     shapes, and `A^T*A` remain exact analysis/probability or discrete
     objects.  Computed non-probability objects are fully charged.  This closes
     tree-reduced sparse-Gram CountSketch layouts; the downstream
     tree-reduced uniform-row composition is closed in S9zza.
     Parallel/aliasing sparse-sketch layouts, lower-level hash/sign generation
     and storage formats, and optimal CountSketch concentration remain
     separate targets.

400.  2026-06-11, A3.4-S9zza CountSketch product-grid stored-sign
     tree-reduced downstream uniform-row wrapper: no external source was used
     beyond the already recorded product-grid CountSketch finite-cover
     Markov/Frobenius route, the S9zz tree-reduced sparse-apply arithmetic,
     the S9zv stored-sign downstream theorem shape, and the local
     computed-denominator sampled-Gram perturbation route.
     `UniformRowSamplingFP.lean` now exposes
     `countSketchSparseComputedPreconditionedBasisWithStoredSignTree`,
     `countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one`,
     `countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and the three concrete stored-sign copy wrappers
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`,
     and
     `countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget`.
     The exact binary tree shape for each realized bucket, including the
     trailing zero leaf, is a discrete algorithm choice and adds no probability
     loss.  The final radius is
     `eta + L*(2*rho + rho^2) + etaRow
     + T_CS_row_store_tree(h, omega, sigma, A)`, charging stored signs,
     rounded signed products, tree-depth bucket accumulation, the concrete
     `uniformRowFlSqrtMulInvSqrtScaleDen` denominator for `sqrt(s/r)`,
     row divisions, and sampled-Gram dot products.  Exact hash/sign laws,
     exact product-grid vectors, exact downstream row laws, tree shapes, exact
     input `A`, and `A^T*A` remain exact analysis/probability or discrete
     objects.  The probability loss is unchanged from the product-grid
     downstream route:
     `sum_a 2*||A*z_a||_2^4/(r*eta^2)
     + 2*||A||_F^4/(r*L^2)
     + r*m^2*||A||_F^4/(s*etaRow^2)`.
     For fixed realized data and `d = sqrt(s/r)`, the displayed deterministic
     radius has order
     `Theta(gamma_s*|| |Bhat|^T|Bhat| ||_F
     + ||(E_den_tree)^T|Bhat| + |Btilde|^T E_den_tree||_F
     + ||F_tree^T|Btilde| + |B|^T F_tree||_F)`, with
     `E_den_tree = Theta(u*|Bhat| + |Yhat_tree|/|dhat| *
     (4*u + 3*u^2 + u^3)/(1-u))` and
     `F_tree = Theta((u + gamma_depth_i)*bucket_column_one_norm/d)`.
     Balanced bucket trees give
     `Theta(u*(1 + log(bucket_size_i + 1))*bucket_column_one_norm/d)` for the
     sampled-basis term.  No perturbation-event hypothesis,
     certificate-existence assumption, generic probability-loss assumption, or
     probability-computation floating-point term is used.

401.  2026-06-11, A2.8actual Algorithm 2 leverage actual-input endpoint:
     no new external concentration theorem was used beyond the already
     recorded equation (7) leverage source chain.  The proof adds a local
     right-Gram congruence transfer and a deterministic floating-point
     perturbation calculation for the actual sampled matrix.  In
     `RowSamplingLeverageComputedBasis.lean`, the exact theorem
     `leverageTraceProbability_eventProb_factoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`
     transfers the orthonormal-basis leverage event to
     `rowGram (preconditionColumns U C) = A^T*A` when exact analysis witnesses
     satisfy `A = U C` and `U^T U = I`.  The implementation-facing theorem
     `leverageTraceProbability_eventProb_factoredInput_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`
     then samples exact rows of `A` from the exact leverage law defined by
     `U`, computes the concrete denominator `fl_sqrt(fl_mul s p_i)`, rounds
     sampled-row divisions, and rounds the length-`s` Gram dot products.
     Exact objects are the analysis witnesses `U`, `C`, `A=U C`, the leverage
     probabilities, and the row trace law.  Computed non-probability objects
     are the denominator, row divisions, and sampled-Gram dot products.  The
     displayed radius is
     `T_A^fp = (gamma_s*(1+eta)^2 + 2*eta + eta^2) *
     sum_j (sum_{i:p_i>0} |A_ij|/sqrt(p_i))^2`, with `eta` fully substituted
     from `u` and the concrete denominator routine, and fixed-problem order
     `Theta((gamma_s + u*(1+support_size))*actual_column_factor)`.  QR, SVD,
     rank-revealing, or other routines that compute `U` or `C` remain separate
     concrete computed-quantity obligations.
